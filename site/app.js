/* Jazz Oral Histories — people network. Raw Canvas 2D renderer, no libraries.
   Static-scene bitmap: the full graph is drawn once per "settle"; pan/zoom
   blits that bitmap with the current transform at 60fps, then re-renders
   crisp after ~140ms idle. */
"use strict";

if (!window.GRAPH) throw new Error("graph.data.js missing");
document.getElementById("loading").style.display = "none";

/* companion static site with the full transcripts (evidence pane deep-links
   into it: ?t=<docid>#b<page>-<block>) */
const TRANSCRIPTS_URL = "https://thisismattmiller.github.io/linked-jazz-2026-transcripts/";

/* ---------------- palette (validated, dark) ---------------- */
const SLOT = ["#3987e5", "#199e70", "#c98500", "#008300",
              "#9085e9", "#e66767", "#d55181", "#d95926"];
const OTHER = "#6e6d66";
const SURFACE = "#1a1a19", PAGE = "#0d0d0d";
const INK = "#ffffff", INK3 = "#898781";
const commColor = (rank) => (rank < 8 ? SLOT[rank] : OTHER);

/* ---------------- unpack graph ---------------- */
const G = window.GRAPH;
const AT = window.ATLAS || { ids: {}, sheets: 0, cell: 80, perRow: 51, perSheet: 2601 };
const N = G.nodes.length, E = G.edges.length;
const ID = new Array(N), LABEL = new Array(N), Q = new Array(N), SQ = new Array(N);
const X = new Float32Array(N), Y = new Float32Array(N), SZ = new Float32Array(N);
const COMM = new Int32Array(N), FLAGS = new Uint8Array(N), DEG = new Int32Array(N),
      MEN = new Int32Array(N), INSTM = new Uint8Array(N), DOCS = new Int32Array(N);
const idIndex = new Map();
for (let i = 0; i < N; i++) {
  const n = G.nodes[i];
  ID[i] = n[0]; LABEL[i] = n[1]; X[i] = n[2]; Y[i] = n[3]; SZ[i] = n[4];
  COMM[i] = n[5]; FLAGS[i] = n[6]; DEG[i] = n[7]; MEN[i] = n[8]; INSTM[i] = n[9];
  Q[i] = n[10] || null; SQ[i] = n[11] || null; DOCS[i] = n[12] || 0;
  idIndex.set(n[0], i);
}
const EA = new Int32Array(E), EB = new Int32Array(E);
const EW = new Float32Array(E), ENC = new Int32Array(E), ETYPE = new Int32Array(E);
const EREL = new Array(E);
for (let j = 0; j < E; j++) {
  const e = G.edges[j];
  EA[j] = e[0]; EB[j] = e[1]; EW[j] = e[2]; ENC[j] = e[3]; EREL[j] = e[4];
  let m = 0; for (const [t] of e[4]) m |= (1 << t);
  ETYPE[j] = m;
}
/* CSR adjacency */
const adjOff = new Int32Array(N + 1);
for (let j = 0; j < E; j++) { adjOff[EA[j] + 1]++; adjOff[EB[j] + 1]++; }
for (let i = 0; i < N; i++) adjOff[i + 1] += adjOff[i];
const adjN = new Int32Array(E * 2), adjE = new Int32Array(E * 2);
{
  const cur = adjOff.slice(0, N);
  for (let j = 0; j < E; j++) {
    adjN[cur[EA[j]]] = EB[j]; adjE[cur[EA[j]]++] = j;
    adjN[cur[EB[j]]] = EA[j]; adjE[cur[EB[j]]++] = j;
  }
}

/* ---------------- view state ---------------- */
const sceneEl = document.getElementById("scene"),
      overEl = document.getElementById("overlay");
const sctx = sceneEl.getContext("2d"), octx = overEl.getContext("2d");
let W = 0, H = 0, DPR = Math.min(devicePixelRatio || 1, 2);
const PAD = 400;                                     // crisp-frame margin (css px) for pan slack
const IPAD = 140;                                    // interactive-frame margin (small = fast)
const view = { k: 1, tx: 0, ty: 0 };
const buf = document.createElement("canvas");        // static scene bitmap (padded)
const bctx = buf.getContext("2d");
let snap = null;                                     // transform the bitmap was rendered at

function resize() {
  W = innerWidth; H = innerHeight;
  for (const c of [sceneEl, overEl]) { c.width = W * DPR; c.height = H * DPR; }
  buf.width = (W + 2 * PAD) * DPR; buf.height = (H + 2 * PAD) * DPR;
  requestRender(0);
}
addEventListener("resize", resize);

/* world bbox + initial fit.
   FA2's extent is arbitrary and outlier-heavy, so: (a) node world-sizes are
   rescaled to the CORE extent (2nd..98th pct) so they are visible at fit zoom
   regardless of layout scale; (b) the initial view fits that core mass, not
   the flung-out periphery. */
let wx0 = 1e9, wy0 = 1e9, wx1 = -1e9, wy1 = -1e9;
for (let i = 0; i < N; i++) {
  if (X[i] < wx0) wx0 = X[i]; if (X[i] > wx1) wx1 = X[i];
  if (Y[i] < wy0) wy0 = Y[i]; if (Y[i] > wy1) wy1 = Y[i];
}
const core = (() => {
  const xs = Float32Array.from(X).sort(), ys = Float32Array.from(Y).sort();
  const q = (a, p) => a[Math.floor(p * (a.length - 1))];
  return { x0: q(xs, 0.02), x1: q(xs, 0.98), y0: q(ys, 0.02), y1: q(ys, 0.98) };
})();
// node sizes arrive in world units from the layout (relief guarantees spacing)
let kFit = 1;
function fitView() {
  const pad = 70;
  view.k = Math.min((innerWidth - pad) / (core.x1 - core.x0),
                    (innerHeight - pad) / (core.y1 - core.y0));
  view.tx = innerWidth / 2 - (core.x0 + core.x1) / 2 * view.k;
  view.ty = innerHeight / 2 - (core.y0 + core.y1) / 2 * view.k;
  kFit = view.k;
}

/* ---------------- filters ---------------- */
const relOn = G.types.map(() => true);
const instOn = G.insts.map(() => true);
let minC = 1, showSing = true, hideUnc = true, isoComm = null;
const nodeVis = new Uint8Array(N), edgeVis = new Uint8Array(E);

function recomputeVisibility() {
  let relMask = 0;
  relOn.forEach((v, t) => { if (v) relMask |= (1 << t); });
  let instMask = 0;
  instOn.forEach((v, t) => { if (v) instMask |= (1 << t); });
  for (let i = 0; i < N; i++) {
    nodeVis[i] = (INSTM[i] & instMask) && (showSing || !(FLAGS[i] & 2)) &&
                 (isoComm === null || COMM[i] === isoComm) ? 1 : 0;
  }
  const touched = new Uint8Array(N);
  let ve = 0;
  for (let j = 0; j < E; j++) {
    edgeVis[j] = nodeVis[EA[j]] && nodeVis[EB[j]] && ENC[j] >= minC &&
                 (ETYPE[j] & relMask) ? 1 : 0;
    if (edgeVis[j]) { touched[EA[j]] = touched[EB[j]] = 1; ve++; }
  }
  let vn = 0;
  for (let i = 0; i < N; i++) {
    if (hideUnc && !touched[i]) nodeVis[i] = 0;
    vn += nodeVis[i];
  }
  document.getElementById("viscount").textContent =
    `${vn.toLocaleString()} people · ${ve.toLocaleString()} relationships shown`;
}

/* ---------------- atlas sheets ---------------- */
const sheets = [];
for (let s = 0; s < AT.sheets; s++) {
  const img = new Image();
  img.onload = () => requestRender(0);
  img.src = `atlas_${s}.jpg`;
  sheets.push(img);
}
function atlasPos(idx) {
  const s = Math.floor(idx / AT.perSheet), c = idx % AT.perSheet;
  return [s, (c % AT.perRow) * AT.cell, Math.floor(c / AT.perRow) * AT.cell];
}
const IMGIDX = new Int32Array(N).fill(-1);
for (let i = 0; i < N; i++) {
  const a = AT.ids[ID[i]];
  if (a !== undefined) IMGIDX[i] = a;
}

/* ---------------- scene render ---------------- */
function drawEdges(ctx, k, tx, ty, cw, ch) {
  const paths = new Map();          // styleKey -> Path2D
  const m = 60;                     // cull margin px
  for (let j = 0; j < E; j++) {
    if (!edgeVis[j]) continue;
    const a = EA[j], b = EB[j];
    const x1 = X[a] * k + tx, y1 = Y[a] * k + ty,
          x2 = X[b] * k + tx, y2 = Y[b] * k + ty;
    if ((x1 < -m && x2 < -m) || (x1 > cw + m && x2 > cw + m) ||
        (y1 < -m && y2 < -m) || (y1 > ch + m && y2 > ch + m)) continue;
    const hub = DEG[a] >= DEG[b] ? a : b;
    const cr = Math.min(COMM[hub], 8);
    const tier = EW[j] < 1.2 ? 0 : EW[j] < 2.6 ? 1 : 2;
    const key = cr * 3 + tier;
    let p = paths.get(key);
    if (!p) { p = new Path2D(); paths.set(key, p); }
    p.moveTo(x1, y1); p.lineTo(x2, y2);
  }
  const ALPHA = [0.05, 0.11, 0.19], LWID = [0.6, 1.0, 1.6];
  for (const [key, p] of paths) {
    const cr = Math.floor(key / 3), tier = key % 3;
    ctx.globalAlpha = ALPHA[tier];
    ctx.strokeStyle = cr < 8 ? SLOT[cr] : OTHER;
    ctx.lineWidth = LWID[tier];
    ctx.stroke(p);
  }
  ctx.globalAlpha = 1;
}

/* important hubs keep a readable minimum screen size at far zoom — spacing is
   physically guaranteed by the layout, so a capped boost can't lie about it */
function drawR(i, k) {
  const r = SZ[i] * k;
  if (DEG[i] >= 100) return Math.max(r, Math.min(16, r * 8));
  if (DEG[i] >= 25) return Math.max(r, Math.min(10, r * 6));
  return r;
}

function drawNode(ctx, i, k, tx, ty, ring = true) {
  const x = X[i] * k + tx, y = Y[i] * k + ty, r = drawR(i, k);
  const col = commColor(COMM[i]);
  const ai = IMGIDX[i];
  if (ai >= 0 && r >= 6 && sheets.length) {
    const [s, sx, sy] = atlasPos(ai);
    const img = sheets[s];
    if (img && img.complete && img.naturalWidth) {
      ctx.save();
      ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832); ctx.clip();
      ctx.drawImage(img, sx, sy, AT.cell, AT.cell, x - r, y - r, r * 2, r * 2);
      ctx.restore();
      if (ring) {
        ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832);
        ctx.strokeStyle = col; ctx.lineWidth = Math.max(1.5, r * 0.10); ctx.stroke();
        if (FLAGS[i] & 1) {       // interviewee: second outer ring in ink
          ctx.beginPath(); ctx.arc(x, y, r + Math.max(1.5, r * 0.10), 0, 6.2832);
          ctx.strokeStyle = "rgba(255,255,255,0.85)"; ctx.lineWidth = 1.2; ctx.stroke();
        }
      }
      return;
    }
  }
  ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832);
  ctx.globalAlpha = (FLAGS[i] & 2) ? 0.5 : 1;
  ctx.fillStyle = col; ctx.fill();
  ctx.globalAlpha = 1;
  if (ring && r >= 3) {
    ctx.strokeStyle = (FLAGS[i] & 1) ? "rgba(255,255,255,0.85)" : "rgba(255,255,255,0.12)";
    ctx.lineWidth = (FLAGS[i] & 1) ? Math.max(1, r * 0.09) : 1;
    ctx.stroke();
  }
}

function drawLabels(ctx, k, tx, ty, order, cw, ch) {
  const placed = [];
  let count = 0;
  ctx.textBaseline = "middle";
  ctx.lineJoin = "round";
  for (const i of order) {
    if (count >= 420) break;
    const r = drawR(i, k);
    if (r < 5.5) continue;
    const x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -80 || x > cw + 80 || y < -20 || y > ch + 20) continue;
    const fs = Math.min(24, Math.max(10.5, r * 0.55));
    ctx.font = `600 ${fs}px system-ui, sans-serif`;
    const w = ctx.measureText(LABEL[i]).width;
    const lx = x + r + 5, ly = y;
    let hit = false;
    for (const b of placed) {
      if (lx < b[2] && lx + w > b[0] && ly - fs / 2 < b[3] && ly + fs / 2 > b[1]) { hit = true; break; }
    }
    if (hit) continue;
    placed.push([lx, ly - fs / 2 - 2, lx + w, ly + fs / 2 + 2]);
    ctx.strokeStyle = "rgba(13,13,13,0.85)"; ctx.lineWidth = 3.5;
    ctx.strokeText(LABEL[i], lx, ly);
    ctx.fillStyle = INK;
    ctx.fillText(LABEL[i], lx, ly);
    count++;
  }
}

const byDeg = Array.from({ length: N }, (_, i) => i).sort((a, b) => DEG[b] - DEG[a]);

function renderScene() {
  const k = view.k;
  const tx = view.tx + PAD, ty = view.ty + PAD;      // draw into the padded buffer
  const CW = W + 2 * PAD, CH = H + 2 * PAD;
  bctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  bctx.fillStyle = SURFACE;
  bctx.fillRect(0, 0, CW, CH);
  drawEdges(bctx, k, tx, ty, CW, CH);
  /* nodes: small first (batched by community), then big/portrait individually */
  const bigs = [];
  const batch = new Map();
  for (let i = 0; i < N; i++) {
    if (!nodeVis[i]) continue;
    const r = drawR(i, k);
    const x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -r - 20 || x > CW + r + 20 || y < -r - 20 || y > CH + r + 20) continue;
    if (r < 0.3) continue;
    if (r < 3.2 && IMGIDX[i] < 0) {
      const key = Math.min(COMM[i], 8) * 2 + ((FLAGS[i] & 2) ? 1 : 0);
      let p = batch.get(key);
      if (!p) { p = new Path2D(); batch.set(key, p); }
      p.moveTo(x + r, y); p.arc(x, y, r, 0, 6.2832);
    } else bigs.push(i);
  }
  for (const [key, p] of batch) {
    const cr = Math.floor(key / 2);
    bctx.globalAlpha = key % 2 ? 0.5 : 0.95;
    bctx.fillStyle = cr < 8 ? SLOT[cr] : OTHER;
    bctx.fill(p);
  }
  bctx.globalAlpha = 1;
  bigs.sort((a, b) => SZ[a] - SZ[b]);
  for (const i of bigs) drawNode(bctx, i, k, tx, ty);
  drawLabels(bctx, k, tx, ty, byDeg.filter(i => nodeVis[i]), CW, CH);
  if (location.search.includes("debug")) {
    let batched = 0; for (const [, p] of batch) batched++;
    console.log(`[dbg] k=${k.toFixed(5)} tx=${tx.toFixed(1)} ty=${ty.toFixed(1)} W=${W} H=${H} ` +
      `maxSZ=${maxSZ.toFixed(1)} bigs=${bigs.length} batchGroups=${batched} ` +
      `core=[${core.x0.toFixed(0)},${core.y0.toFixed(0)}..${core.x1.toFixed(0)},${core.y1.toFixed(0)}] ` +
      `n0=(${(X[0] * k + tx).toFixed(1)},${(Y[0] * k + ty).toFixed(1)}) r0=${(SZ[0] * k).toFixed(2)}`);
  }
  snap = { k: view.k, tx: view.tx, ty: view.ty };
  frameBitmap = null;
  frameMeta = { pad: PAD, rs: DPR };
  blit();
  if (location.search.includes("debug")) {
    const bp = bctx.getImageData(buf.width / 2, buf.height / 2, 1, 1).data;
    const sp = sctx.getImageData(sceneEl.width / 2, sceneEl.height / 2, 1, 1).data;
    let nz = 0;
    const all = bctx.getImageData(0, 0, buf.width, 200).data;
    for (let i = 0; i < all.length; i += 4) if (all[i] > 40 || all[i+1] > 40 || all[i+2] > 40) nz++;
    console.log(`[dbg2] buf center=${bp} scene center=${sp} brightPixelsTop200rows=${nz} bufSize=${buf.width}x${buf.height}`);
  }
}

let frameBitmap = null;                              // latest worker-rendered bitmap
let frameMeta = { pad: PAD, rs: DPR };               // pad+resolution the bitmap was made at
function blit() {
  sctx.setTransform(1, 0, 0, 1, 0, 0);
  sctx.fillStyle = SURFACE;
  sctx.fillRect(0, 0, W * DPR, H * DPR);
  if (!snap) return;
  const s = view.k / snap.k;
  const sc = s * DPR / frameMeta.rs;
  sctx.setTransform(sc, 0, 0, sc,
    (view.tx - (snap.tx + frameMeta.pad) * s) * DPR,
    (view.ty - (snap.ty + frameMeta.pad) * s) * DPR);
  sctx.drawImage(frameBitmap || buf, 0, 0);
  sctx.setTransform(1, 0, 0, 1, 0, 0);
}

/* ---- render worker: scene renders happen OFF the main thread. While the
   view is moving we stream SMALL low-res frames (~2MP, fast to raster and
   upload); 260ms after the last movement one crisp padded frame is rendered.
   Falls back to the sync renderer when OffscreenCanvas is unavailable. ---- */
let worker = null, workerBusy = false, workerDirty = 0, workerReady = false, seq = 0;
if (window.OffscreenCanvas && window.Worker) {
  try { worker = new Worker("render-worker.js"); } catch (e) { worker = null; }
}
function pumpWorker(crisp = false) {
  if (!worker || !workerReady) return;
  if (workerBusy) { workerDirty = Math.max(workerDirty, crisp ? 2 : 1); return; }
  workerBusy = true;
  const pad = crisp ? PAD : IPAD;
  const rs = crisp ? DPR : Math.min(DPR, 1);
  worker.postMessage({ type: "render", seq: ++seq, lod: !crisp,
                       k: view.k, tx: view.tx, ty: view.ty, W, H, pad, rs });
}
if (worker) {
  worker.onmessage = (e) => {
    const m = e.data;
    if (m.type === "frame") {
      if (frameBitmap) frameBitmap.close();
      frameBitmap = m.bitmap;
      frameMeta = { pad: m.pad, rs: m.rs };
      snap = { k: m.k, tx: m.tx, ty: m.ty };
      workerBusy = false;
      if (location.search.includes("debug"))
        console.log(`[frame] ${m.rs === DPR ? "crisp" : "fast"} ${m.ms}ms`);
      blit(); drawOverlay();
      if (workerDirty) { const c = workerDirty === 2; workerDirty = 0; pumpWorker(c); }
    } else if (m.type === "atlasready") {
      pumpWorker(true);
    }
  };
}
function sendVisToWorker() {
  if (worker) worker.postMessage({ type: "vis",
    nodeVis: nodeVis.slice(), edgeVis: edgeVis.slice() });
}

/* render scheduling: blit every frame during interaction; low-res frames
   stream from the worker, crisp frame 260ms after the view settles. */
let renderTimer = null, rafPending = false;
function requestRender(idleMs = 140) {
  if (!rafPending) {
    rafPending = true;
    requestAnimationFrame(() => { rafPending = false; blit(); drawOverlay(); });
  }
  if (worker) {
    pumpWorker(false);
    clearTimeout(renderTimer);
    renderTimer = setTimeout(() => pumpWorker(true), 260);
    return;
  }
  if (snap) {
    const s = view.k / snap.k;
    const dx = Math.abs(view.tx - snap.tx), dy = Math.abs(view.ty - snap.ty);
    if (dx > PAD * 0.55 * s || dy > PAD * 0.55 * s || s < 0.75 || s > 1.6) idleMs = Math.min(idleMs, 30);
  }
  clearTimeout(renderTimer);
  renderTimer = setTimeout(() => { renderScene(); drawOverlay(); }, idleMs);
}

/* ---------------- spatial index / hit test ---------------- */
let maxSZ = 0;
for (let i = 0; i < N; i++) if (SZ[i] > maxSZ) maxSZ = SZ[i];
const CELL = Math.max((core.x1 - core.x0) / 240, maxSZ * 1.05);
const gridMap = new Map();
for (let i = 0; i < N; i++) {
  const key = Math.floor(X[i] / CELL) * 100000 + Math.floor(Y[i] / CELL);
  let a = gridMap.get(key);
  if (!a) { a = []; gridMap.set(key, a); }
  a.push(i);
}
function pick(px, py) {
  const wx = (px - view.tx) / view.k, wy = (py - view.ty) / view.k;
  const cx = Math.floor(wx / CELL), cy = Math.floor(wy / CELL);
  let best = -1, bestD = 1e9;
  for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) {
    const a = gridMap.get((cx + dx) * 100000 + (cy + dy));
    if (!a) continue;
    for (const i of a) {
      if (!nodeVis[i]) continue;
      const d = Math.hypot(X[i] - wx, Y[i] - wy);
      const rr = Math.max(SZ[i], 5 / view.k);
      if (d < rr && d < bestD) { bestD = d; best = i; }
    }
  }
  return best;
}

/* ---------------- overlay: hover + selection ego ---------------- */
let hoverI = -1, selI = -1;
function drawOverlay() {
  octx.setTransform(DPR, 0, 0, DPR, 0, 0);
  octx.clearRect(0, 0, W, H);
  if (dragging) return;                    // ego redraw mid-drag is a frame killer
  const focus = selI >= 0 ? selI : hoverI;
  if (focus < 0) return;
  const k = view.k, tx = view.tx, ty = view.ty;
  octx.fillStyle = selI >= 0 ? "rgba(13,13,13,0.62)" : "rgba(13,13,13,0.45)";
  octx.fillRect(0, 0, W, H);
  /* ego edges */
  const nbrs = [];
  for (let p = adjOff[focus]; p < adjOff[focus + 1]; p++) {
    const j = adjE[p];
    if (!edgeVis[j]) continue;
    const o = adjN[p];
    nbrs.push([o, j]);
    const x1 = X[focus] * k + tx, y1 = Y[focus] * k + ty,
          x2 = X[o] * k + tx, y2 = Y[o] * k + ty;
    octx.beginPath(); octx.moveTo(x1, y1); octx.lineTo(x2, y2);
    octx.globalAlpha = 0.6;
    octx.strokeStyle = commColor(COMM[o]);
    octx.lineWidth = Math.min(3, 0.7 + EW[j] * 0.5);
    octx.stroke();
  }
  octx.globalAlpha = 1;
  nbrs.sort((a, b) => SZ[a[0]] - SZ[b[0]]);
  for (const [o] of nbrs) drawNode(octx, o, k, tx, ty);
  drawNode(octx, focus, k, tx, ty);
  /* focus halo */
  const fx = X[focus] * k + tx, fy = Y[focus] * k + ty, fr = SZ[focus] * k;
  octx.beginPath(); octx.arc(fx, fy, fr + 4, 0, 6.2832);
  octx.strokeStyle = INK; octx.lineWidth = 2; octx.stroke();
  /* labels: focus + top neighbors */
  const order = [focus, ...nbrs.map(x => x[0]).sort((a, b) => DEG[b] - DEG[a])];
  octx.textBaseline = "middle"; octx.lineJoin = "round";
  const placed = []; let cnt = 0;
  for (const i of order) {
    if (cnt >= 42) break;
    const r = SZ[i] * k, x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -80 || x > W + 80 || y < -20 || y > H + 20) continue;
    const fs = i === focus ? Math.max(14, Math.min(26, r * 0.6)) : Math.min(16, Math.max(10, r * 0.55));
    octx.font = `600 ${fs}px system-ui, sans-serif`;
    const w = octx.measureText(LABEL[i]).width, lx = x + r + 5, ly = y;
    let hit = false;
    for (const bb of placed)
      if (lx < bb[2] && lx + w > bb[0] && ly - fs / 2 < bb[3] && ly + fs / 2 > bb[1]) { hit = true; break; }
    if (hit) continue;
    placed.push([lx, ly - fs / 2 - 2, lx + w, ly + fs / 2 + 2]);
    octx.strokeStyle = "rgba(13,13,13,0.9)"; octx.lineWidth = 3.5;
    octx.strokeText(LABEL[i], lx, ly);
    octx.fillStyle = INK; octx.fillText(LABEL[i], lx, ly);
    cnt++;
  }
}

/* ---------------- interactions ---------------- */
let dragging = false, moved = false, lastX = 0, lastY = 0, hoverTimer = null;
sceneEl.parentElement.addEventListener("pointerdown", (e) => {
  dragging = true; moved = false; lastX = e.clientX; lastY = e.clientY;
});
addEventListener("pointermove", (e) => {
  if (dragging) {
    const dx = e.clientX - lastX, dy = e.clientY - lastY;
    if (Math.abs(dx) + Math.abs(dy) > 2) moved = true;
    view.tx += dx; view.ty += dy;
    lastX = e.clientX; lastY = e.clientY;
    requestRender();
  } else {
    if (mback.classList.contains("open")) {          // no map hover under the modal
      clearTimeout(hoverTimer);
      if (hoverI !== -1) { hoverI = -1; document.body.style.cursor = ""; drawOverlay(); }
      return;
    }
    const i = pick(e.clientX, e.clientY);
    document.body.style.cursor = i >= 0 ? "pointer" : "";
    clearTimeout(hoverTimer);
    if (i < 0) {
      if (hoverI !== -1) { hoverI = -1; drawOverlay(); }   // leaving clears instantly
    } else if (i !== hoverI) {
      hoverTimer = setTimeout(() => { hoverI = i; drawOverlay(); }, 190);
    }                                                      // dim only after the pointer rests
  }
});
addEventListener("pointerup", (e) => {
  if (!dragging) return;
  dragging = false;
  if (!moved) {
    const i = pick(e.clientX, e.clientY);
    if (i >= 0) select(i);
    else { selI = -1; closePanel(); drawOverlay(); history.replaceState(null, "", "#"); }
  }
});
addEventListener("wheel", (e) => {
  if (mback.classList.contains("open")) return;      // modal locks the map
  if (e.target.closest("#rail,#results,#topbar")) return;
  e.preventDefault();
  const f = Math.exp(-e.deltaY * 0.0016);
  const nk = Math.min(kFit * 4000, Math.max(kFit * 0.1, view.k * f));
  const r = nk / view.k;
  view.tx = e.clientX - (e.clientX - view.tx) * r;
  view.ty = e.clientY - (e.clientY - view.ty) * r;
  view.k = nk;
  requestRender();
}, { passive: false });
addEventListener("keydown", (e) => {
  if (e.key === "Escape") { selI = -1; closePanel(); drawOverlay(); }
});

function flyTo(i, done) {
  const targetK = Math.max(view.k, 90 / SZ[i]);
  const from = { ...view };
  const to = { k: targetK, tx: W / 2 - X[i] * targetK, ty: H / 2 - Y[i] * targetK };
  const t0 = performance.now(), dur = 650;
  (function step(t) {
    const u = Math.min(1, (t - t0) / dur), s = u < 0.5 ? 2 * u * u : 1 - (2 - 2 * u) ** 2 / 2;
    view.k = from.k + (to.k - from.k) * s;
    view.tx = from.tx + (to.tx - from.tx) * s;
    view.ty = from.ty + (to.ty - from.ty) * s;
    requestRender(u < 1 ? 9999 : 60);
    if (u < 1) requestAnimationFrame(step);
    else if (done) done();
  })(t0);
}

/* ---------------- person modal ---------------- */
const mback = document.getElementById("mback"), mev = document.getElementById("mev");
function esc(s) { return s.replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])); }
function closePanel() { mback.classList.remove("open"); mev.classList.remove("open"); mev.innerHTML = ""; }

function fnv64(s) {                                  // matches extract_evidence.py
  let h = 0xCBF29CE484222325n;
  const P = 0x100000001B3n, M = 0xFFFFFFFFFFFFFFFFn;
  for (const b of new TextEncoder().encode(s)) { h ^= BigInt(b); h = (h * P) & M; }
  return h.toString(16).padStart(16, "0");
}

/* direction arrow for edge j, relative to person p: "→" = p acts on the other */
function dirArrow(j, p, bits) {
  if (!bits) return "";
  if ((bits & 3) === 3) return "↔";
  const pIsA = EA[j] === p;
  const acts = pIsA ? 1 : 2;
  return bits & acts ? "→" : "←";
}

function paintPortrait(cv, i, px) {
  const pctx = cv.getContext("2d");
  pctx.clearRect(0, 0, px, px);
  const ai = IMGIDX[i], half = px / 2;
  if (ai >= 0 && sheets.length) {
    const [s, sx, sy] = atlasPos(ai);
    const img = sheets[s];
    const paint = () => {
      pctx.save(); pctx.beginPath(); pctx.arc(half, half, half - 2, 0, 6.2832); pctx.clip();
      pctx.drawImage(img, sx, sy, AT.cell, AT.cell, 0, 0, px, px); pctx.restore();
      pctx.beginPath(); pctx.arc(half, half, half - 3, 0, 6.2832);
      pctx.strokeStyle = commColor(COMM[i]); pctx.lineWidth = 6; pctx.stroke();
    };
    img.complete ? paint() : img.addEventListener("load", paint, { once: true });
  } else {
    pctx.beginPath(); pctx.arc(half, half, half - 12, 0, 6.2832);
    pctx.fillStyle = commColor(COMM[i]); pctx.fill();
    pctx.fillStyle = "#fff"; pctx.font = `600 ${px * 0.38}px system-ui`;
    pctx.textAlign = "center"; pctx.textBaseline = "middle";
    pctx.fillText((LABEL[i] || "?")[0].toUpperCase(), half, half + px * 0.03);
  }
}

function select(i, fly = false) {
  selI = i;
  history.replaceState(null, "", "#" + encodeURIComponent(ID[i]));
  if (fly) flyTo(i);
  drawOverlay();
  paintPortrait(document.getElementById("mportrait"), i, 192);
  document.getElementById("mname").textContent = LABEL[i];
  const chips = [];
  if (FLAGS[i] & 1) chips.push(`<span class="chip itv">interviewee</span>`);
  chips.push(`<span class="chip"><span class="dot" style="background:${commColor(COMM[i])}"></span>${esc(commName(COMM[i]))}</span>`);
  G.insts.forEach((nm, t) => { if (INSTM[i] & (1 << t)) chips.push(`<span class="chip">${INST_LABEL[nm] || nm}</span>`); });
  document.getElementById("mchips").innerHTML = chips.join("");
  document.getElementById("mstats").innerHTML =
    `<b>${DEG[i].toLocaleString()}</b> connections · <b>${MEN[i].toLocaleString()}</b> mentions · appears in <b>${DOCS[i]}</b> interview${DOCS[i] === 1 ? "" : "s"}`;
  const links = [];
  if (Q[i]) links.push(`<a href="https://www.wikidata.org/wiki/${Q[i]}" target="_blank">Wikidata ↗</a>`);
  if (SQ[i]) links.push(`<a href="https://base.semlab.io/wiki/Item:${SQ[i]}" target="_blank">Semlab ↗</a>`);
  links.push(`<a id="mshowmap">Show on map ⌖</a>`);
  document.getElementById("mlinks").innerHTML = links.join("");
  document.getElementById("mshowmap").onclick = () => {
    closePanel(); flyTo(i);
  };

  /* relation-type sections: person chips with direction + count */
  const byType = new Map();          // typeIdx -> [{o, j, c, d}]
  for (let p = adjOff[i]; p < adjOff[i + 1]; p++) {
    const o = adjN[p], j = adjE[p];
    if (!edgeVis[j] && !nodeVis[o]) { /* still show — modal is about the data */ }
    for (const r of EREL[j]) {
      const [t, c, d] = [r[0], r[1], r[2] || 0];
      if (!byType.has(t)) byType.set(t, []);
      byType.get(t).push({ o, j, c, d });
    }
  }
  const CAP = 36;
  const parts = [];
  for (let t = 0; t < G.types.length; t++) {
    const list = byType.get(t);
    if (!list) continue;
    list.sort((a, b) => b.c - a.c || DEG[b.o] - DEG[a.o]);
    const chipHtml = (e) => {
      const arrow = dirArrow(e.j, i, e.d);
      return `<span class="pchip" data-o="${e.o}" data-j="${e.j}">
        <span class="dot" style="background:${commColor(COMM[e.o])}"></span>
        ${arrow ? `<span class="dir">${arrow}</span>` : ""}
        <span class="nm">${esc(LABEL[e.o])}</span>
        ${e.c > 1 ? `<span class="xn">×${e.c}</span>` : ""}</span>`;
    };
    const head = list.slice(0, CAP).map(chipHtml).join("");
    const rest = list.length > CAP
      ? `<span class="names hidden-rest" style="display:none">${list.slice(CAP).map(chipHtml).join("")}</span>
         <button class="morebtn">+ ${list.length - CAP} more</button>`
      : "";
    parts.push(`<section><h4>${esc(G.types[t])}<span class="n">${list.length}</span></h4>
      <div class="names">${head}${rest}</div></section>`);
  }
  document.getElementById("mrels").innerHTML =
    parts.join("") || `<section><h4>no classified relationships</h4></section>`;
  mev.classList.remove("open"); mev.innerHTML = "";
  mback.classList.add("open");
}

/* evidence pane: fetch the per-pair file and show quotes with context */
async function showEvidence(i, o) {
  document.querySelectorAll(".pchip.sel").forEach(el => el.classList.remove("sel"));
  document.querySelectorAll(`.pchip[data-o="${o}"]`).forEach(el => el.classList.add("sel"));
  mev.classList.add("open");
  mev.innerHTML = `<div class="evhead">${esc(LABEL[i])} &amp; ${esc(LABEL[o])}
      <small>what the interviews say</small></div><div class="evload">loading…</div>`;
  const pairkey = [ID[i], ID[o]].sort().join("|");
  let data;
  try {
    const h = fnv64(pairkey);
    const res = await fetch(`ev/${h.slice(0, 2)}/${h}.json`);
    if (!res.ok) throw new Error(res.status);
    data = await res.json();
  } catch (e) {
    mev.querySelector(".evload").textContent = "no evidence file found (" + e.message + ")";
    return;
  }
  const names = new Set();
  for (const nm of [LABEL[i], LABEL[o]]) {
    names.add(nm);
    const last = nm.split(" ").pop();
    if (last.length >= 4) names.add(last);
  }
  const hl = (txt) => {
    let h = esc(txt);
    for (const nm of names) {
      if (nm.length < 4) continue;
      h = h.replace(new RegExp(`(${nm.replace(/[.*+?^${}()|[\\]\\\\]/g, "\\$&")})(?![^<]*>)`, "gi"), "<mark>$1</mark>");
    }
    return h;
  };
  const items = data.items.map(it => {
    const anchor = Number.isInteger(it.pg) && Number.isInteger(it.bl) ? `#b${it.pg}-${it.bl}` : "";
    const tr = `${TRANSCRIPTS_URL}?t=${encodeURIComponent(it.doc)}${anchor}`;
    return `
    <div class="evitem">
      <div class="src">from <b>${esc(it.who)}</b>’s interview · ${INST_LABEL[it.inst] || it.inst}
        <br>${esc(it.title)}</div>
      <span class="reltag">${esc(it.rel)}${it.dir === "mutual" ? " ↔" : ""}${it.conf ? ` · ${Math.round(it.conf * 100)}%` : ""}</span>
      ${it.q ? `<div class="evquote">${hl(it.q)}</div>` : ""}
      ${(it.ctx || []).map(t =>
        `<div class="turn src${t.src}"><span class="sp">${esc(t.s)}:</span> ${hl(t.x)}</div>`).join("")}
      <div class="evread"><a href="${tr}" target="_blank" rel="noopener">read the full transcript ↗</a></div>
    </div>`;
  }).join("");
  mev.innerHTML = `<div class="evhead">${esc(LABEL[i])} &amp; ${esc(LABEL[o])}
      <small>${data.items.length} interview${data.items.length === 1 ? "" : "s"}${data.more ? ` (+${data.more} more not shown)` : ""} · click name again to pivot</small></div>` + items;
}

document.getElementById("mrels").addEventListener("click", (e) => {
  const more = e.target.closest(".morebtn");
  if (more) {
    more.previousElementSibling.style.display = "contents";
    more.remove();
    return;
  }
  const chip = e.target.closest(".pchip");
  if (!chip) return;
  const o = +chip.dataset.o;
  if (chip.classList.contains("sel")) { select(o); return; }   // second click pivots to that person
  showEvidence(selI, o);
});
document.getElementById("mclose").onclick = () => { selI = -1; closePanel(); drawOverlay(); };
mback.addEventListener("pointerdown", (e) => {
  if (e.target === mback) { selI = -1; closePanel(); drawOverlay(); }
});

/* ---------------- community names (top-2 members) ---------------- */
const commTop = new Map();
for (const i of byDeg) {
  const c = COMM[i];
  let a = commTop.get(c);
  if (!a) { a = []; commTop.set(c, a); }
  if (a.length < 2) a.push(LABEL[i]);
}
function commName(rank) {
  const L = (window.COMM_LABELS || {})[rank];       // LLM-assigned label, if generated
  if (L && L.label) return L.label;
  const t = commTop.get(rank);
  return t ? t.join(" · ") : `community ${rank}`;
}

/* ---------------- UI: rail ---------------- */
const INST_LABEL = { tulane: "Tulane", hamilton: "Hamilton", si: "Smithsonian", rutgers: "Rutgers" };
{
  const cl = document.getElementById("commlist");
  const shown = G.comm.filter(c => c.rank < 8).sort((a, b) => a.rank - b.rank);
  const others = G.comm.filter(c => c.rank >= 8).sort((a, b) => b.size - a.size);
  const otherN = others.reduce((s, c) => s + c.size, 0);
  const row = (c, color) =>
    `<div class="commrow" data-c="${c.rank}"><span class="dot" style="background:${color}"></span>
     <span class="nm" title="${esc(commName(c.rank))}">${esc(commName(c.rank))}</span>
     <span class="cnt">${c.size.toLocaleString()}</span></div>`;
  cl.innerHTML = shown.map(c => row(c, SLOT[c.rank])).join("") +
    `<div class="commrow" id="othertoggle"><span class="dot" style="background:${OTHER}"></span>
     <span class="nm">other communities (${others.length})</span>
     <span class="cnt">${otherN.toLocaleString()} <span id="otherarrow">▸</span></span></div>
     <div id="otherlist" style="display:none">` +
    others.map(c => row(c, OTHER)).join("") + `</div>`;
  cl.addEventListener("click", (e) => {
    const r = e.target.closest(".commrow");
    if (!r) return;
    if (r.id === "othertoggle") {
      const ol = document.getElementById("otherlist");
      const open = ol.style.display === "none";
      ol.style.display = open ? "block" : "none";
      document.getElementById("otherarrow").textContent = open ? "▾" : "▸";
      return;
    }
    const c = +r.dataset.c;
    isoComm = isoComm === c ? null : c;
    cl.querySelectorAll(".commrow[data-c]").forEach(el =>
      el.classList.toggle("active", +el.dataset.c === isoComm));
    refilter();
  });

  const counts = G.types.map(() => 0);
  for (let j = 0; j < E; j++) for (const [t] of EREL[j]) counts[t]++;
  document.getElementById("rellist").innerHTML = G.types.map((t, ti) =>
    `<label class="opt"><input type="checkbox" data-t="${ti}" checked> ${t}
     <span class="cnt">${counts[ti].toLocaleString()}</span></label>`).join("");
  document.getElementById("rellist").addEventListener("change", (e) => {
    relOn[+e.target.dataset.t] = e.target.checked; refilter();
  });

  document.getElementById("instlist").innerHTML = G.insts.map((nm, ti) =>
    `<label class="opt"><input type="checkbox" data-t="${ti}" checked> ${INST_LABEL[nm] || nm}</label>`).join("");
  document.getElementById("instlist").addEventListener("change", (e) => {
    instOn[+e.target.dataset.t] = e.target.checked; refilter();
  });

  document.getElementById("minn").addEventListener("input", (e) => {
    minC = +e.target.value;
    document.getElementById("minnlbl").textContent = `≥ ${minC} interview${minC > 1 ? "s" : ""}`;
    refilter();
  });
  document.getElementById("showsing").addEventListener("change", (e) => { showSing = e.target.checked; refilter(); });
  document.getElementById("hideunc").addEventListener("change", (e) => { hideUnc = e.target.checked; refilter(); });
  document.getElementById("resetview").onclick = () => { fitView(); requestRender(0); };
}
function refilter() { recomputeVisibility(); sendVisToWorker(); requestRender(0); }

/* ---------------- search ---------------- */
{
  const inp = document.getElementById("search"), res = document.getElementById("results");
  const lower = LABEL.map(s => s.toLowerCase());
  let selRow = -1, rows = [];
  function run() {
    const q = inp.value.trim().toLowerCase();
    if (q.length < 2) { res.style.display = "none"; return; }
    rows = [];
    for (const i of byDeg) {
      if (lower[i].includes(q)) { rows.push(i); if (rows.length >= 12) break; }
    }
    selRow = 0;
    res.innerHTML = rows.map((i, ri) =>
      `<div class="row ${ri === 0 ? "sel" : ""}" data-i="${i}">
        <span class="dot" style="background:${commColor(COMM[i])}"></span>
        <span class="nm">${esc(LABEL[i])}</span><span class="deg">${DEG[i]}</span></div>`).join("");
    res.style.display = rows.length ? "block" : "none";
  }
  inp.addEventListener("input", run);
  inp.addEventListener("keydown", (e) => {
    if (e.key === "ArrowDown" || e.key === "ArrowUp") {
      e.preventDefault();
      selRow = Math.max(0, Math.min(rows.length - 1, selRow + (e.key === "ArrowDown" ? 1 : -1)));
      [...res.children].forEach((el, ri) => el.classList.toggle("sel", ri === selRow));
    } else if (e.key === "Enter" && rows.length) {
      go(rows[selRow]);
    } else if (e.key === "Escape") { res.style.display = "none"; inp.blur(); }
  });
  res.addEventListener("mousedown", (e) => {
    const row = e.target.closest(".row");
    if (row) go(+row.dataset.i);
  });
  function go(i) { res.style.display = "none"; inp.blur(); select(i, true); }
}

/* ---------------- boot ---------------- */
document.getElementById("subtitle").textContent =
  ` ${N.toLocaleString()} people · ${E.toLocaleString()} relationships · 4 archives`;
resize();
fitView();
recomputeVisibility();
if (worker) {
  const ESTYLE = new Uint8Array(E);
  for (let j = 0; j < E; j++) {
    const hub = DEG[EA[j]] >= DEG[EB[j]] ? EA[j] : EB[j];
    ESTYLE[j] = Math.min(COMM[hub], 8) * 3 + (EW[j] < 1.2 ? 0 : EW[j] < 2.6 ? 1 : 2);
  }
  worker.postMessage({
    type: "init", N, E,
    SLOT, OTHER, SURFACE, INK,
    AT: { sheets: AT.sheets || 0, cell: AT.cell, perRow: AT.perRow, perSheet: AT.perSheet },
    X: X.slice(), Y: Y.slice(), SZ: SZ.slice(), COMM: COMM.slice(),
    FLAGS: FLAGS.slice(), DEG: DEG.slice(), IMGIDX: IMGIDX.slice(),
    LABEL, BYDEG: Int32Array.from(byDeg),
    EA: EA.slice(), EB: EB.slice(), ESTYLE,
    nodeVis: nodeVis.slice(), edgeVis: edgeVis.slice(),
  });
  workerReady = true;
  requestRender(0);
} else {
  renderScene();
}
if (location.search.includes("dump")) {
  setTimeout(() => {
    const d = document.createElement("div");
    d.id = "canvasdump";
    d.textContent = sceneEl.toDataURL("image/png");
    d.style.display = "none";
    document.body.appendChild(d);
  }, 4000);
}
if (location.hash.length > 1) {
  const key = decodeURIComponent(location.hash.slice(1));
  const i = idIndex.get(key);
  if (location.search.includes("debug"))
    console.log(`[dbg-hash] raw=${location.hash} key=${key} found=${i}`);
  if (i !== undefined) {
    if (location.search.includes("instant")) {   // no animation (also: headless has no rAF)
      view.k = Math.max(kFit, 90 / SZ[i]);
      view.tx = W / 2 - X[i] * view.k;
      view.ty = H / 2 - Y[i] * view.k;
      select(i, false);
      requestRender(0);
      const evp = new URLSearchParams(location.search).get("ev");
      const oi = evp && idIndex.get(evp);
      if (oi !== undefined && oi !== null) setTimeout(() => showEvidence(i, oi), 400);
    } else setTimeout(() => select(i, true), 300);
  }
}
