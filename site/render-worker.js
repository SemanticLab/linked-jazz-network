/* Scene renderer in a Web Worker: draws the full graph into an OffscreenCanvas
   and ships ImageBitmaps to the main thread, which just blits. Panning/zooming
   never blocks on rendering. Visual output matches app.js's sync fallback.
   Motion frames ("lod") skip the faintest edge tier, cap labels at 110 and
   place them from an estimated width instead of measureText. */
"use strict";

let N = 0, E = 0;
let X, Y, SZ, COMM, FLAGS, DEG, IMGIDX, LABEL, BYDEG, EA, EB, ETIER;
let nodeVis = null, edgeVis = null;
let PAL = null, NSLOT = 6;
let AT = null;
const sheets = [];
const ALPHA = [0.025, 0.08, 0.2], LWID = [0.6, 1.0, 1.6];
let fontReady = false;

const canvas = new OffscreenCanvas(1, 1);
const ctx = canvas.getContext("2d", { alpha: false });

onmessage = (e) => {
  const m = e.data;
  if (m.type === "init") {
    ({ N, E, PAL, NSLOT, AT } = m);
    X = m.X; Y = m.Y; SZ = m.SZ; COMM = m.COMM; FLAGS = m.FLAGS; DEG = m.DEG;
    IMGIDX = m.IMGIDX; LABEL = m.LABEL; BYDEG = m.BYDEG;
    EA = m.EA; EB = m.EB; ETIER = m.ETIER;
    nodeVis = m.nodeVis; edgeVis = m.edgeVis;
    for (let s = 0; s < (AT.sheets || 0); s++) {
      fetch(`atlas_${s}.webp`).then(r => r.blob()).then(b => createImageBitmap(b))
        .then(bm => { sheets[s] = bm; postMessage({ type: "atlasready" }); })
        .catch(() => {});
    }
    loadFont();
  } else if (m.type === "vis") {
    nodeVis = m.nodeVis; edgeVis = m.edgeVis;
  } else if (m.type === "palette") {
    PAL = m.PAL;
  } else if (m.type === "render") {
    render(m);
  }
};

/* Libre Franklin for the labels: pull the @font-face blocks from Google Fonts
   and register them in the worker's own font set (no DOM here). Falls back
   to system-ui silently. */
async function loadFont() {
  if (!self.fonts || !self.FontFace) return;
  try {
    const css = await (await fetch(
      "https://fonts.googleapis.com/css2?family=Libre+Franklin:wght@500;700&display=swap")).text();
    const blocks = css.split("@font-face").slice(1);
    const loads = [];
    for (const b of blocks) {
      const url = /url\(([^)]+)\)/.exec(b), w = /font-weight:\s*(\d+)/.exec(b),
            ur = /unicode-range:\s*([^;]+);/.exec(b);
      if (!url) continue;
      const ff = new FontFace("Libre Franklin", `url(${url[1]})`,
        { weight: w ? w[1] : "500", unicodeRange: ur ? ur[1] : undefined });
      self.fonts.add(ff);
      loads.push(ff.load().catch(() => {}));
    }
    await Promise.all(loads);
    fontReady = true;
    postMessage({ type: "fontsready" });
  } catch (e) { /* keep system-ui */ }
}
const LABEL_FONT = (fs) => `500 ${fs}px "Libre Franklin", system-ui, sans-serif`;

const commColor = (rank) => (rank < NSLOT ? PAL.SLOT[rank] : PAL.OTHER);

function drawR(i, k) {
  const r = SZ[i] * k;
  if (DEG[i] >= 100) return Math.max(r, Math.min(16, r * 8));
  if (DEG[i] >= 25) return Math.max(r, Math.min(10, r * 6));
  return r;
}

function atlasPos(idx) {
  const s = Math.floor(idx / AT.perSheet), c = idx % AT.perSheet;
  return [s, (c % AT.perRow) * AT.cell, Math.floor(c / AT.perRow) * AT.cell];
}

function drawNode(i, k, tx, ty) {
  const x = X[i] * k + tx, y = Y[i] * k + ty, r = drawR(i, k);
  const col = commColor(COMM[i]);
  const ai = IMGIDX[i];
  if (ai >= 0 && r >= 6) {
    const [s, sx, sy] = atlasPos(ai);
    const img = sheets[s];
    if (img) {
      ctx.save();
      ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832); ctx.clip();
      ctx.drawImage(img, sx, sy, AT.cell, AT.cell, x - r, y - r, r * 2, r * 2);
      ctx.restore();
      ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832);
      ctx.strokeStyle = col; ctx.lineWidth = Math.max(1.5, r * 0.10); ctx.stroke();
      if (FLAGS[i] & 1) {
        ctx.beginPath(); ctx.arc(x, y, r + Math.max(1.5, r * 0.10), 0, 6.2832);
        ctx.strokeStyle = PAL.INK; ctx.lineWidth = 1.2; ctx.stroke();
      }
      return;
    }
  }
  ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832);
  ctx.globalAlpha = (FLAGS[i] & 2) ? 0.55 : 1;
  ctx.fillStyle = col; ctx.fill();
  ctx.globalAlpha = 1;
  if (r >= 3) {
    ctx.strokeStyle = (FLAGS[i] & 1) ? PAL.INK : PAL.BLUE;
    ctx.lineWidth = (FLAGS[i] & 1) ? Math.max(1, r * 0.09) : 1;
    ctx.stroke();
  }
}

function render(m) {
  const { seq, k, W, H, pad, rs } = m;
  const tx = m.tx + pad, ty = m.ty + pad;
  const CW = W + 2 * pad, CH = H + 2 * pad;
  const t0 = performance.now();
  const lod = !!m.lod;
  const pw = Math.round(CW * rs), ph = Math.round(CH * rs);
  if (canvas.width !== pw || canvas.height !== ph) { canvas.width = pw; canvas.height = ph; }
  ctx.setTransform(rs, 0, 0, rs, 0, 0);
  ctx.fillStyle = PAL.SURFACE;
  ctx.fillRect(0, 0, CW, CH);

  /* edges: three weight tiers of the one blue, batched into three paths */
  const paths = [new Path2D(), new Path2D(), new Path2D()];
  const mrg = 60;
  for (let j = 0; j < E; j++) {
    if (!edgeVis[j]) continue;
    const t = ETIER[j];
    if (lod && t === 0) continue;                 // motion frame: drop the fog
    const a = EA[j], b = EB[j];
    const x1 = X[a] * k + tx, y1 = Y[a] * k + ty, x2 = X[b] * k + tx, y2 = Y[b] * k + ty;
    if ((x1 < -mrg && x2 < -mrg) || (x1 > CW + mrg && x2 > CW + mrg) ||
        (y1 < -mrg && y2 < -mrg) || (y1 > CH + mrg && y2 > CH + mrg)) continue;
    paths[t].moveTo(x1, y1); paths[t].lineTo(x2, y2);
  }
  ctx.strokeStyle = PAL.BLUE;
  for (let t = lod ? 1 : 0; t < 3; t++) { ctx.globalAlpha = ALPHA[t]; ctx.lineWidth = LWID[t]; ctx.stroke(paths[t]); }
  ctx.globalAlpha = 1;

  /* nodes: small batched by colour, big individually */
  const bigs = [];
  const batch = new Map();
  for (let i = 0; i < N; i++) {
    if (!nodeVis[i]) continue;
    const r = drawR(i, k);
    const x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -r - 20 || x > CW + r + 20 || y < -r - 20 || y > CH + r + 20) continue;
    if (r < 0.3) continue;
    if (r < 3.2 && IMGIDX[i] < 0) {
      const key = Math.min(COMM[i], NSLOT) * 2 + ((FLAGS[i] & 2) ? 1 : 0);
      let p = batch.get(key);
      if (!p) { p = new Path2D(); batch.set(key, p); }
      p.moveTo(x + r, y); p.arc(x, y, r, 0, 6.2832);
    } else bigs.push(i);
  }
  for (const [key, p] of batch) {
    const cr = Math.floor(key / 2);
    ctx.globalAlpha = (key % 2 ? 0.55 : 0.95) * (cr >= NSLOT ? 0.7 : 1);
    ctx.fillStyle = commColor(cr);
    ctx.fill(p);
  }
  ctx.globalAlpha = 1;
  bigs.sort((a, b) => SZ[a] - SZ[b]);
  for (const i of bigs) drawNode(i, k, tx, ty);

  /* labels: by degree, occupancy boxes; motion frames estimate widths */
  ctx.textBaseline = "middle";
  ctx.lineJoin = "round";
  const placed = [];
  const cap = lod ? 110 : 420;
  let count = 0;
  for (let bi = 0; bi < BYDEG.length; bi++) {
    if (count >= cap) break;
    const i = BYDEG[bi];
    if (!nodeVis[i]) continue;
    const r = drawR(i, k);
    if (r < 5.5) continue;
    const x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -80 || x > CW + 80 || y < -20 || y > CH + 20) continue;
    const fs = Math.min(22, Math.max(11, r * 0.55));
    ctx.font = LABEL_FONT(fs);
    const w = lod ? LABEL[i].length * fs * 0.56 : ctx.measureText(LABEL[i]).width;
    const lx = x + r + 5, ly = y;
    let hit = false;
    for (const bb of placed) {
      if (lx < bb[2] && lx + w > bb[0] && ly - fs / 2 < bb[3] && ly + fs / 2 > bb[1]) { hit = true; break; }
    }
    if (hit) continue;
    placed.push([lx, ly - fs / 2 - 2, lx + w, ly + fs / 2 + 2]);
    ctx.strokeStyle = PAL.SURFACE; ctx.lineWidth = 3.5;
    ctx.strokeText(LABEL[i], lx, ly);
    ctx.fillStyle = PAL.INK;
    ctx.fillText(LABEL[i], lx, ly);
    count++;
  }

  const bitmap = canvas.transferToImageBitmap();
  postMessage({ type: "frame", seq, lod, k: m.k, tx: m.tx, ty: m.ty, W, H, pad, rs, bitmap,
                ms: Math.round(performance.now() - t0) }, [bitmap]);
}
