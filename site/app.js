/* Linked Jazz — people network. Raw Canvas 2D renderer, no libraries.
   The full graph is rasterised off the main thread (render-worker.js) into a
   padded bitmap; pan/zoom blit that bitmap at 60 fps, low-res frames stream
   while the view moves, one crisp frame lands when it settles. Colours and
   type come from the Linked Jazz design tokens (CSS variables on :root). */
"use strict";

/* companion static site with the full transcripts (evidence pane deep-links
   into it: ?t=<docid>#b<page>-<block>) */
const TRANSCRIPTS_URL = "https://semlab.io/linked-jazz-transcripts/";
const DEBUG = location.search.includes("debug");

/* ---------------- design tokens -> canvas palette ---------------- */
/* the six node colours a legend may carry (never yellow+gold or green+lime
   together); every other community is drawn in line-strong */
const SLOT_TOKENS = ["node-periwinkle", "node-orange", "node-green", "node-magenta", "node-gold", "node-sage"];
const NSLOT = SLOT_TOKENS.length;
let PAL = null;
function readPalette() {
  const cs = getComputedStyle(document.documentElement);
  const t = (n) => cs.getPropertyValue("--" + n).trim();
  PAL = { SLOT: SLOT_TOKENS.map(t), OTHER: t("line-strong"), SURFACE: t("surface-raised"), PAGE: t("surface"),
          INK: t("ink"), INK_MUTED: t("ink-muted"), BLUE: t("blue"), BLUE_DEEP: t("blue-deep"), BLUE_SOFT: t("blue-soft"),
          ON_BLUE: t("on-blue"), dark: cs.colorScheme === "dark" };
  return PAL;
}
readPalette();
const commColor = (rank) => (rank < NSLOT ? PAL.SLOT[rank] : PAL.OTHER);
const LABEL_FONT = (fs, w = 500) => `${w} ${fs}px "Libre Franklin", system-ui, sans-serif`;

/* ---------------- graph (filled by boot) ---------------- */
let G, AT, N, E, ID, LABEL, Q, SQ, X, Y, SZ, COMM, FLAGS, DEG, MEN, INSTM, DOCS, idIndex;
let EA, EB, EW, ENC, ETYPE, EREL, adjOff, adjN, adjE, byDeg;

function unpack(g) {
  G = g;
  AT = window.ATLAS || { ids: {}, sheets: 0, cell: 80, perRow: 51, perSheet: 2601 };
  N = G.nodes.length; E = G.edges.length;
  ID = new Array(N); LABEL = new Array(N); Q = new Array(N); SQ = new Array(N);
  X = new Float32Array(N); Y = new Float32Array(N); SZ = new Float32Array(N);
  COMM = new Int32Array(N); FLAGS = new Uint8Array(N); DEG = new Int32Array(N);
  MEN = new Int32Array(N); INSTM = new Uint8Array(N); DOCS = new Int32Array(N);
  idIndex = new Map();
  for (let i = 0; i < N; i++) {
    const n = G.nodes[i];
    ID[i] = n[0]; LABEL[i] = n[1]; X[i] = n[2]; Y[i] = n[3]; SZ[i] = n[4];
    COMM[i] = n[5]; FLAGS[i] = n[6]; DEG[i] = n[7]; MEN[i] = n[8]; INSTM[i] = n[9];
    Q[i] = n[10] || null; SQ[i] = n[11] || null; DOCS[i] = n[12] || 0;
    idIndex.set(n[0], i);
  }
  EA = new Int32Array(E); EB = new Int32Array(E);
  EW = new Float32Array(E); ENC = new Int32Array(E); ETYPE = new Int32Array(E);
  EREL = new Array(E);
  for (let j = 0; j < E; j++) {
    const e = G.edges[j];
    EA[j] = e[0]; EB[j] = e[1]; EW[j] = e[2]; ENC[j] = e[3]; EREL[j] = e[4];
    let m = 0; for (const [t] of e[4]) m |= (1 << t);
    ETYPE[j] = m;
  }
  G.nodes = null; G.edges = null;                     // let the raw arrays go
  /* CSR adjacency */
  adjOff = new Int32Array(N + 1);
  for (let j = 0; j < E; j++) { adjOff[EA[j] + 1]++; adjOff[EB[j] + 1]++; }
  for (let i = 0; i < N; i++) adjOff[i + 1] += adjOff[i];
  adjN = new Int32Array(E * 2); adjE = new Int32Array(E * 2);
  const cur = adjOff.slice(0, N);
  for (let j = 0; j < E; j++) {
    adjN[cur[EA[j]]] = EB[j]; adjE[cur[EA[j]]++] = j;
    adjN[cur[EB[j]]] = EA[j]; adjE[cur[EB[j]]++] = j;
  }
  byDeg = Int32Array.from({ length: N }, (_, i) => i).sort((a, b) => DEG[b] - DEG[a]);
}

/* ---------------- view state ---------------- */
const sceneEl = document.getElementById("scene"),
      overEl = document.getElementById("overlay");
const sctx = sceneEl.getContext("2d", { alpha: false, desynchronized: true }),
      octx = overEl.getContext("2d");
let W = 0, H = 0, DPR = Math.min(devicePixelRatio || 1, 2);
const PAD = 280;                                     // crisp-frame margin (css px) for pan slack
const IPAD = 120;                                    // interactive-frame margin (small = fast)
const view = { k: 1, tx: 0, ty: 0 };
const buf = document.createElement("canvas");        // static scene bitmap (sync fallback only)
const bctx = buf.getContext("2d");
let snap = null;                                     // transform the bitmap was rendered at

function resize() {
  const r = sceneEl.parentElement.getBoundingClientRect();
  W = Math.round(r.width); H = Math.round(r.height);
  for (const c of [sceneEl, overEl]) { c.width = W * DPR; c.height = H * DPR; }
  if (!worker) { buf.width = (W + 2 * PAD) * DPR; buf.height = (H + 2 * PAD) * DPR; }
  if (G) requestRender(0);
}
addEventListener("resize", resize);

/* world bbox + initial fit: the view fits the core mass (2nd..98th pct), not
   the flung-out periphery */
let core = null, kFit = 1;
function computeCore() {
  const xs = Float32Array.from(X).sort(), ys = Float32Array.from(Y).sort();
  const q = (a, p) => a[Math.floor(p * (a.length - 1))];
  core = { x0: q(xs, 0.02), x1: q(xs, 0.98), y0: q(ys, 0.02), y1: q(ys, 0.98) };
}
function fitView() {
  const pad = 70;
  view.k = Math.min((W - pad) / (core.x1 - core.x0), (H - pad) / (core.y1 - core.y0));
  view.tx = W / 2 - (core.x0 + core.x1) / 2 * view.k;
  view.ty = H / 2 - (core.y0 + core.y1) / 2 * view.k;
  kFit = view.k;
}

/* ---------------- filters ---------------- */
let relOn, instOn, nodeVis, edgeVis;
let minC = 1, showSing = true, hideUnc = true, isoComm = null;

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

/* ---------------- atlas sheets (main thread: lazy, only for the overlay and
   the portrait in the modal — the worker owns its own copy) ---------------- */
const sheets = [];
let sheetsRequested = false;
function ensureSheets(onload) {
  if (sheetsRequested) return;
  sheetsRequested = true;
  for (let s = 0; s < AT.sheets; s++) {
    const img = new Image();
    img.onload = () => { sheets[s] = img; if (onload) onload(); drawOverlay(); };
    img.src = `atlas_${s}.webp`;
  }
}
function atlasPos(idx) {
  const s = Math.floor(idx / AT.perSheet), c = idx % AT.perSheet;
  return [s, (c % AT.perRow) * AT.cell, Math.floor(c / AT.perRow) * AT.cell];
}
let IMGIDX;

/* ---------------- scene render (sync fallback when no worker) ---------------- */
const ALPHA = [0.025, 0.08, 0.2], LWID = [0.6, 1.0, 1.6];
function drawEdges(ctx, k, tx, ty, cw, ch) {
  const paths = [new Path2D(), new Path2D(), new Path2D()];
  const m = 60;
  for (let j = 0; j < E; j++) {
    if (!edgeVis[j]) continue;
    const a = EA[j], b = EB[j];
    const x1 = X[a] * k + tx, y1 = Y[a] * k + ty, x2 = X[b] * k + tx, y2 = Y[b] * k + ty;
    if ((x1 < -m && x2 < -m) || (x1 > cw + m && x2 > cw + m) ||
        (y1 < -m && y2 < -m) || (y1 > ch + m && y2 > ch + m)) continue;
    const p = paths[EW[j] < 1.2 ? 0 : EW[j] < 2.6 ? 1 : 2];
    p.moveTo(x1, y1); p.lineTo(x2, y2);
  }
  ctx.strokeStyle = PAL.BLUE;
  for (let t = 0; t < 3; t++) { ctx.globalAlpha = ALPHA[t]; ctx.lineWidth = LWID[t]; ctx.stroke(paths[t]); }
  ctx.globalAlpha = 1;
}

/* important hubs keep a readable minimum screen size at far zoom */
function drawR(i, k) {
  const r = SZ[i] * k;
  if (DEG[i] >= 100) return Math.max(r, Math.min(16, r * 8));
  if (DEG[i] >= 25) return Math.max(r, Math.min(10, r * 6));
  return r;
}

function drawNode(ctx, i, k, tx, ty) {
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

function placeLabels(ctx, k, tx, ty, order, cw, ch, cap, measure) {
  const placed = [];
  let count = 0;
  ctx.textBaseline = "middle"; ctx.lineJoin = "round";
  for (const i of order) {
    if (count >= cap) break;
    const r = drawR(i, k);
    if (r < 5.5) continue;
    const x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -80 || x > cw + 80 || y < -20 || y > ch + 20) continue;
    const fs = Math.min(22, Math.max(11, r * 0.55));
    ctx.font = LABEL_FONT(fs);
    const w = measure ? ctx.measureText(LABEL[i]).width : LABEL[i].length * fs * 0.56;
    const lx = x + r + 5, ly = y;
    let hit = false;
    for (const b of placed) {
      if (lx < b[2] && lx + w > b[0] && ly - fs / 2 < b[3] && ly + fs / 2 > b[1]) { hit = true; break; }
    }
    if (hit) continue;
    placed.push([lx, ly - fs / 2 - 2, lx + w, ly + fs / 2 + 2]);
    ctx.strokeStyle = PAL.SURFACE; ctx.lineWidth = 3.5;
    ctx.strokeText(LABEL[i], lx, ly);
    ctx.fillStyle = PAL.INK;
    ctx.fillText(LABEL[i], lx, ly);
    count++;
  }
}

function renderScene() {
  const k = view.k;
  const tx = view.tx + PAD, ty = view.ty + PAD;
  const CW = W + 2 * PAD, CH = H + 2 * PAD;
  bctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  bctx.fillStyle = PAL.SURFACE;
  bctx.fillRect(0, 0, CW, CH);
  drawEdges(bctx, k, tx, ty, CW, CH);
  const bigs = [], batch = new Map();
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
    bctx.globalAlpha = (key % 2 ? 0.55 : 0.95) * (cr >= NSLOT ? 0.7 : 1);
    bctx.fillStyle = commColor(cr);
    bctx.fill(p);
  }
  bctx.globalAlpha = 1;
  bigs.sort((a, b) => SZ[a] - SZ[b]);
  for (const i of bigs) drawNode(bctx, i, k, tx, ty);
  placeLabels(bctx, k, tx, ty, byDeg.filter(i => nodeVis[i]), CW, CH, 420, true);
  snap = { k: view.k, tx: view.tx, ty: view.ty };
  frameBitmap = null;
  frameMeta = { pad: PAD, rs: DPR };
  blit();
}

let frameBitmap = null;                              // latest worker-rendered bitmap
let frameMeta = { pad: PAD, rs: DPR };               // pad+resolution the bitmap was made at
function blit() {
  sctx.setTransform(1, 0, 0, 1, 0, 0);
  sctx.fillStyle = PAL.SURFACE;
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

/* ---- render worker ---- */
let worker = null, workerBusy = false, workerDirty = 0, workerReady = false, seq = 0;
if (window.OffscreenCanvas && window.Worker) {
  try { worker = new Worker("render-worker.js?v=9"); } catch (e) { worker = null; }
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
      if (DEBUG) console.log(`[frame] ${m.lod ? "fast" : "crisp"} ${m.ms}ms`);
      blit(); drawOverlay();
      if (workerDirty) { const c = workerDirty === 2; workerDirty = 0; pumpWorker(c); }
    } else if (m.type === "atlasready" || m.type === "fontsready") {
      pumpWorker(true);
    }
  };
}
function sendVisToWorker() {
  if (worker) worker.postMessage({ type: "vis", nodeVis: nodeVis.slice(), edgeVis: edgeVis.slice() });
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
let CELL = 1, gridMap = null, maxSZ = 0;
function buildGrid() {
  for (let i = 0; i < N; i++) if (SZ[i] > maxSZ) maxSZ = SZ[i];
  CELL = Math.max((core.x1 - core.x0) / 240, maxSZ * 1.05);
  gridMap = new Map();
  for (let i = 0; i < N; i++) {
    const key = Math.floor(X[i] / CELL) * 100000 + Math.floor(Y[i] / CELL);
    let a = gridMap.get(key);
    if (!a) { a = []; gridMap.set(key, a); }
    a.push(i);
  }
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
      const ddx = X[i] - wx, ddy = Y[i] - wy;
      const d = Math.sqrt(ddx * ddx + ddy * ddy);
      const rr = Math.max(SZ[i], 5 / view.k);
      if (d < rr && d < bestD) { bestD = d; best = i; }
    }
  }
  return best;
}

/* ---------------- overlay: hover + selection ego ---------------- */
let hoverI = -1, selI = -1;
function drawOverlay() {
  if (!G) return;
  octx.setTransform(DPR, 0, 0, DPR, 0, 0);
  octx.clearRect(0, 0, W, H);
  if (dragging) return;                    // ego redraw mid-drag is a frame killer
  const focus = selI >= 0 ? selI : hoverI;
  if (focus < 0) return;
  ensureSheets();
  const k = view.k, tx = view.tx, ty = view.ty;
  octx.fillStyle = PAL.SURFACE;
  octx.globalAlpha = selI >= 0 ? 0.72 : 0.58;
  octx.fillRect(0, 0, W, H);
  octx.globalAlpha = 1;
  /* ego edges: blue, full opacity, 2px (the design's hover state) */
  const nbrs = [];
  const ego = new Path2D();
  const fx = X[focus] * k + tx, fy = Y[focus] * k + ty;
  for (let p = adjOff[focus]; p < adjOff[focus + 1]; p++) {
    const j = adjE[p];
    if (!edgeVis[j]) continue;
    const o = adjN[p];
    nbrs.push(o);
    ego.moveTo(fx, fy); ego.lineTo(X[o] * k + tx, Y[o] * k + ty);
  }
  octx.strokeStyle = PAL.BLUE; octx.lineWidth = 1.5; octx.globalAlpha = 0.9;
  octx.stroke(ego);
  octx.globalAlpha = 1;
  nbrs.sort((a, b) => SZ[a] - SZ[b]);
  for (const o of nbrs) drawNode(octx, o, k, tx, ty);
  drawNode(octx, focus, k, tx, ty);
  /* focus ring: 2px gap then 3px of blue, like the focus ring */
  const fr = drawR(focus, k);
  octx.beginPath(); octx.arc(fx, fy, fr + 3.5, 0, 6.2832);
  octx.strokeStyle = PAL.BLUE; octx.lineWidth = 3; octx.stroke();
  /* labels: focus + top neighbours */
  const order = [focus, ...nbrs.sort((a, b) => DEG[b] - DEG[a])];
  octx.textBaseline = "middle"; octx.lineJoin = "round";
  const placed = []; let cnt = 0;
  for (const i of order) {
    if (cnt >= 42) break;
    const r = drawR(i, k), x = X[i] * k + tx, y = Y[i] * k + ty;
    if (x < -80 || x > W + 80 || y < -20 || y > H + 20) continue;
    const fs = i === focus ? Math.max(15, Math.min(26, r * 0.6)) : Math.min(16, Math.max(11, r * 0.55));
    octx.font = LABEL_FONT(fs, i === focus ? 700 : 500);
    const w = octx.measureText(LABEL[i]).width, lx = x + r + 6, ly = y;
    let hit = false;
    for (const bb of placed)
      if (lx < bb[2] && lx + w > bb[0] && ly - fs / 2 < bb[3] && ly + fs / 2 > bb[1]) { hit = true; break; }
    if (hit) continue;
    placed.push([lx, ly - fs / 2 - 2, lx + w, ly + fs / 2 + 2]);
    octx.strokeStyle = PAL.SURFACE; octx.lineWidth = 4;
    octx.strokeText(LABEL[i], lx, ly);
    octx.fillStyle = PAL.INK; octx.fillText(LABEL[i], lx, ly);
    cnt++;
  }
}

/* ---------------- interactions ---------------- */
let dragging = false, moved = false, lastX = 0, lastY = 0, hoverTimer = null;
const stage = sceneEl.parentElement;
const TOP = () => stage.getBoundingClientRect().top;
stage.addEventListener("pointerdown", (e) => {
  dragging = true; moved = false; lastX = e.clientX; lastY = e.clientY;
});
addEventListener("pointermove", (e) => {
  if (!G) return;
  if (dragging) {
    const dx = e.clientX - lastX, dy = e.clientY - lastY;
    if (Math.abs(dx) + Math.abs(dy) > 2) moved = true;
    view.tx += dx; view.ty += dy;
    lastX = e.clientX; lastY = e.clientY;
    requestRender();
  } else {
    if (mback.classList.contains("open") || e.target.closest("#rail,#header,#commcard")) {
      clearTimeout(hoverTimer);
      if (hoverI !== -1) { hoverI = -1; document.body.style.cursor = ""; drawOverlay(); }
      return;
    }
    const i = pick(e.clientX, e.clientY - TOP());
    document.body.style.cursor = i >= 0 ? "pointer" : "";
    clearTimeout(hoverTimer);
    if (i < 0) {
      if (hoverI !== -1) { hoverI = -1; drawOverlay(); }
    } else if (i !== hoverI) {
      hoverTimer = setTimeout(() => { hoverI = i; drawOverlay(); }, 190);
    }
  }
});
addEventListener("pointerup", (e) => {
  if (!dragging) return;
  dragging = false;
  if (!moved) {
    const i = pick(e.clientX, e.clientY - TOP());
    if (i >= 0) select(i);
    else { selI = -1; closePanel(); drawOverlay(); history.replaceState(null, "", "#"); }
  } else requestRender(0);
});
addEventListener("wheel", (e) => {
  if (!G || mback.classList.contains("open")) return;
  if (e.target.closest("#rail,#results,#header,#commcard")) return;
  e.preventDefault();
  const f = Math.exp(-e.deltaY * 0.0016);
  const nk = Math.min(kFit * 4000, Math.max(kFit * 0.1, view.k * f));
  const r = nk / view.k;
  const cy = e.clientY - TOP();
  view.tx = e.clientX - (e.clientX - view.tx) * r;
  view.ty = cy - (cy - view.ty) * r;
  view.k = nk;
  requestRender();
}, { passive: false });
addEventListener("keydown", (e) => {
  if (e.key === "Escape") { selI = -1; closePanel(); drawOverlay(); }
});

function flyTo(i, done) {
  const targetK = Math.max(view.k, 90 / SZ[i]);
  flyToView({ k: targetK, tx: W / 2 - X[i] * targetK, ty: H / 2 - Y[i] * targetK }, done);
}
/* fit the visible members of one community (2nd..98th percentile, so a few
   flung-out members don't dictate the zoom) and fly there */
function fitCommunity(c) {
  const xs = [], ys = [];
  for (let i = 0; i < N; i++) if (nodeVis[i] && COMM[i] === c) { xs.push(X[i]); ys.push(Y[i]); }
  if (xs.length < 2) return;
  xs.sort((a, b) => a - b); ys.sort((a, b) => a - b);
  const q = (a, p) => a[Math.floor(p * (a.length - 1))];
  const x0 = q(xs, 0.02), x1 = q(xs, 0.98), y0 = q(ys, 0.02), y1 = q(ys, 0.98);
  const pad = 120, railW = innerWidth > 720 ? 290 : 0;
  const k = Math.min(kFit * 400, Math.min((W - railW - pad) / Math.max(1, x1 - x0), (H - pad) / Math.max(1, y1 - y0)));
  flyToView({ k, tx: railW + (W - railW) / 2 - (x0 + x1) / 2 * k, ty: H / 2 - (y0 + y1) / 2 * k });
}
function flyToView(to, done) {
  const from = { ...view };
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
function esc(s) { return String(s ?? "").replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])); }
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
  const paint = () => {
    const [s, sx, sy] = atlasPos(ai);
    const img = sheets[s];
    if (!img) return false;
    pctx.save(); pctx.beginPath(); pctx.arc(half, half, half - 2, 0, 6.2832); pctx.clip();
    pctx.drawImage(img, sx, sy, AT.cell, AT.cell, 0, 0, px, px); pctx.restore();
    pctx.beginPath(); pctx.arc(half, half, half - 3, 0, 6.2832);
    pctx.strokeStyle = commColor(COMM[i]); pctx.lineWidth = 4; pctx.stroke();
    return true;
  };
  /* initials on blue-soft (PersonCard's avatar) until a portrait is available */
  pctx.beginPath(); pctx.arc(half, half, half - 4, 0, 6.2832);
  pctx.fillStyle = PAL.BLUE_SOFT; pctx.fill();
  pctx.fillStyle = PAL.BLUE_DEEP; pctx.font = `700 ${px * 0.34}px "Libre Franklin", system-ui`;
  pctx.textAlign = "center"; pctx.textBaseline = "middle";
  const ini = (LABEL[i] || "?").split(/\s+/).slice(0, 2).map(w => w[0]).join("").toUpperCase();
  pctx.fillText(ini, half, half + px * 0.02);
  if (ai >= 0) {
    ensureSheets();
    if (!paint()) {
      const s = atlasPos(ai)[0];
      const again = () => { if (selI === i) paint(); };
      if (sheets[s]) paint(); else setTimeout(() => (sheets[s] ? again() : setTimeout(again, 800)), 400);
    }
  }
}

const INST_LABEL = { tulane: "Tulane", hamilton: "Hamilton", si: "Smithsonian", rutgers: "Rutgers" };
const SYMMETRIC = new Set(["in music group with", "played with", "toured with", "collaborated with",
                           "friend of", "acquaintance of", "has met"]);
const ACTOR_IS_OBJECT = new Set(["played under", "influenced by"]);   // direction bit marks the leader / influencer

function select(i, fly = false) {
  selI = i;
  history.replaceState(null, "", "#" + encodeURIComponent(ID[i]));
  if (fly) flyTo(i);
  drawOverlay();
  paintPortrait(document.getElementById("mportrait"), i, 192);
  document.getElementById("mname").textContent = LABEL[i];
  const chips = [];
  if (FLAGS[i] & 1) chips.push(`<span class="lj-rel itv">Interviewed</span>`);
  chips.push(`<span class="lj-rel"><span class="dot" style="background:${commColor(COMM[i])}"></span>${esc(commName(COMM[i]))}</span>`);
  G.insts.forEach((nm, t) => { if (INSTM[i] & (1 << t)) chips.push(`<span class="lj-rel">${INST_LABEL[nm] || nm}</span>`); });
  document.getElementById("mchips").innerHTML = chips.join("");
  document.getElementById("mstats").innerHTML =
    `<b>${DEG[i].toLocaleString()}</b> relationships · <b>${MEN[i].toLocaleString()}</b> mentions · in <b>${DOCS[i]}</b> oral histor${DOCS[i] === 1 ? "y" : "ies"}`;
  const links = [];
  if (Q[i]) links.push(`<a href="https://www.wikidata.org/wiki/${Q[i]}" target="_blank" rel="noopener">Wikidata</a>`);
  if (SQ[i]) links.push(`<a href="https://base.semlab.io/wiki/Item:${SQ[i]}" target="_blank" rel="noopener">Semlab</a>`);
  links.push(`<a id="mshowmap" href="#${encodeURIComponent(ID[i])}">Show on the map</a>`);
  document.getElementById("mlinks").innerHTML = links.join("");
  document.getElementById("mshowmap").onclick = (e) => { e.preventDefault(); closePanel(); flyTo(i); };

  /* relation-type sections, written as sentences so the direction is never in
     doubt: "Teo · KNOWS OF · Sonny Williams" vs "Sonny Williams · KNOWS OF · Teo".
     Symmetric relations get one row. A directed relation with no recorded
     direction falls back to the interview: the interviewee is the one who knows
     of / was influenced by / played under the person they mentioned. */
  const byType = new Map();
  for (let p = adjOff[i]; p < adjOff[i + 1]; p++) {
    const o = adjN[p], j = adjE[p];
    for (const r of EREL[j]) {
      const [t, c, d] = [r[0], r[1], r[2] || 0];
      if (!byType.has(t)) byType.set(t, []);
      byType.get(t).push({ o, j, c, d });
    }
  }
  const CAP = 36;
  const parts = [];
  const me = `<b class="who">${esc(LABEL[i])}</b>`;
  const chipHtml = (e) =>
    `<span class="pchip" data-o="${e.o}" data-j="${e.j}" role="button" tabindex="0">
      <span class="dot" style="background:${commColor(COMM[e.o])}"></span>
      <span class="nm">${esc(LABEL[e.o])}</span>
      ${e.c > 1 ? `<span class="xn" title="${e.c} interviews corroborate this">×${e.c}</span>` : ""}</span>`;
  const chipList = (list) => {
    const head = list.slice(0, CAP).map(chipHtml).join("");
    const rest = list.length > CAP
      ? `<span class="names hidden-rest" style="display:none">${list.slice(CAP).map(chipHtml).join("")}</span>
         <button class="lj-btn morebtn">Show all ${list.length}</button>` : "";
    return `<span class="names">${head}${rest}</span>`;
  };
  for (let t = 0; t < G.types.length; t++) {
    const list = byType.get(t);
    if (!list) continue;
    list.sort((a, b) => b.c - a.c || DEG[b.o] - DEG[a.o]);
    const rel = `<span class="lj-rel reltag">${esc(G.types[t])}</span>`;
    const rows = [];
    if (SYMMETRIC.has(G.types[t])) {
      rows.push(`<div class="relrow"><span class="lead">${me} ${rel}</span> ${chipList(list)}</div>`);
    } else {
      const out = [], inn = [], both = [], unk = [];
      for (const e of list) {
        let bits = e.d;
        if (!bits && !ACTOR_IS_OBJECT.has(G.types[t])) {   // not recorded: the interviewee is the subject
          const meItv = !!(FLAGS[i] & 1), oItv = !!(FLAGS[e.o] & 1);
          if (meItv !== oItv) bits = (meItv === (EA[e.j] === i)) ? 1 : 2;
        }
        if (bits === 3) both.push(e);
        else if (!bits) unk.push(e);
        else {
          /* the bit marks the "actor" of the relation as the audit recorded it: the
             leader for played under, the mentor, the influencer, the one who knows of.
             For played under / influenced by that actor is the OBJECT of the phrase. */
          const meIsActor = (EA[e.j] === i) === (bits === 1);
          const meIsSubject = ACTOR_IS_OBJECT.has(G.types[t]) ? !meIsActor : meIsActor;
          (meIsSubject ? out : inn).push(e);
        }
      }
      if (out.length) rows.push(`<div class="relrow"><span class="lead">${me} ${rel}</span> ${chipList(out)}</div>`);
      if (inn.length) rows.push(`<div class="relrow"><span class="lead"><span class="caption">these people</span> ${rel} ${me}</span> ${chipList(inn)}</div>`);
      if (both.length) rows.push(`<div class="relrow"><span class="lead">${me} ${rel} <span class="caption">each other</span></span> ${chipList(both)}</div>`);
      if (unk.length) rows.push(`<div class="relrow"><span class="lead">${me} ${rel} <span class="caption">(direction not recorded)</span></span> ${chipList(unk)}</div>`);
    }
    parts.push(`<section><h4 class="label">${esc(G.types[t])}<span class="n">${list.length}</span></h4>${rows.join("")}</section>`);
  }
  document.getElementById("mrels").innerHTML =
    parts.join("") || `<section><h4 class="label">No classified relationships</h4></section>`;
  mev.classList.remove("open"); mev.innerHTML = "";
  mback.classList.add("open");
}

/* evidence pane: fetch the per-pair file and show the passages as Transcript blocks */
async function showEvidence(i, o) {
  document.querySelectorAll(".pchip.sel").forEach(el => el.classList.remove("sel"));
  document.querySelectorAll(`.pchip[data-o="${o}"]`).forEach(el => el.classList.add("sel"));
  mev.classList.add("open");
  mev.innerHTML = `<div class="evhead">${esc(LABEL[i])} and ${esc(LABEL[o])}
      <small class="caption">What the interviews say</small></div><div class="evload caption">Loading…</div>`;
  const pairkey = [ID[i], ID[o]].sort().join("|");
  let data;
  try {
    const h = fnv64(pairkey);
    const res = await fetch(`ev/${h.slice(0, 2)}/${h}.json`);
    if (!res.ok) throw new Error(res.status);
    data = await res.json();
  } catch (e) {
    mev.querySelector(".evload").textContent = "No passages are recorded for this pair (" + e.message + ").";
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
    <blockquote class="lj-transcript">
      <div class="src caption">From <b>${esc(it.who)}</b>’s interview · ${INST_LABEL[it.inst] || it.inst}<br>${esc(it.title)}</div>
      <span class="lj-rel">${esc(it.rel)}${it.dir === "mutual" ? " ↔" : ""}</span>
      ${it.q ? `<p class="q">${hl(it.q)}</p>` : ""}
      ${(it.ctx || []).map(t =>
        `<div class="turn src${t.src}"><span class="sp">${esc(t.s)}</span> ${hl(t.x)}</div>`).join("")}
      <footer class="caption"><span>${it.conf ? `Confidence ${Math.round(it.conf * 100)}%` : ""}</span>
        <a href="${tr}" target="_blank" rel="noopener">Read the interview</a></footer>
    </blockquote>`;
  }).join("");
  mev.innerHTML = `<div class="evhead">${esc(LABEL[i])} and ${esc(LABEL[o])}
      <small class="caption">${data.items.length} interview${data.items.length === 1 ? "" : "s"}${data.more ? ` (+${data.more} more not shown)` : ""} · click the name again to go to that person</small></div>` + items;
}

document.getElementById("mrels").addEventListener("click", (e) => {
  const more = e.target.closest(".morebtn");
  if (more) { more.previousElementSibling.style.display = "contents"; more.remove(); return; }
  const chip = e.target.closest(".pchip");
  if (!chip) return;
  const o = +chip.dataset.o;
  if (chip.classList.contains("sel")) { select(o); return; }   // second click pivots to that person
  showEvidence(selI, o);
});
document.getElementById("mrels").addEventListener("keydown", (e) => {
  if ((e.key === "Enter" || e.key === " ") && e.target.classList.contains("pchip")) { e.preventDefault(); e.target.click(); }
});
document.getElementById("mclose").onclick = () => { selI = -1; closePanel(); drawOverlay(); };
mback.addEventListener("pointerdown", (e) => {
  if (e.target === mback) { selI = -1; closePanel(); drawOverlay(); }
});

/* ---------------- community names ---------------- */
let commTop = null;
function commName(rank) {
  const L = (window.COMM_LABELS || {})[rank];       // agent-assigned label, if any
  if (L && L.label) return L.label;
  const t = commTop.get(rank);
  return t ? t.join(" · ") : `Community ${rank}`;
}

/* ---------------- community card: what the labelling agent found ---------------- */
const commcard = document.getElementById("commcard");
function showCommCard(c) {
  if (c === null) { commcard.classList.remove("open"); return; }
  const L = (window.COMM_LABELS || {})[c] || {};
  const size = (G.comm.find(x => x.rank === c) || {}).size || 0;
  let members = 0, itv = 0; const insts = new Set();
  for (let i = 0; i < N; i++) if (COMM[i] === c) { members++; if (FLAGS[i] & 1) itv++; G.insts.forEach((nm, t) => { if (INSTM[i] & (1 << t)) insts.add(INST_LABEL[nm] || nm); }); }
  document.getElementById("commtitle").innerHTML =
    `<span class="dot" style="background:${commColor(c)}"></span><span>${esc(commName(c))}</span>`;
  document.getElementById("commmeta").textContent =
    [L.era, L.place, `${size.toLocaleString()} people`, `${itv.toLocaleString()} interviewed`].filter(Boolean).join(" · ");
  document.getElementById("commscene").textContent = L.scene || "";
  document.getElementById("commsummary").textContent = L.summary ||
    "No description has been written for this community yet; it is named after its two most-connected members.";
  const figs = (L.key_figures || []).map(nm => {
    const lower = nm.toLowerCase();
    let best = -1;
    for (const i of byDeg) if (COMM[i] === c && LABEL[i].toLowerCase() === lower) { best = i; break; }
    if (best < 0) for (const i of byDeg) if (LABEL[i].toLowerCase() === lower) { best = i; break; }
    return best >= 0
      ? `<span class="pchip" data-i="${best}" role="button" tabindex="0"><span class="dot" style="background:${commColor(COMM[best])}"></span><span class="nm">${esc(LABEL[best])}</span></span>`
      : `<span class="pchip off"><span class="nm">${esc(nm)}</span></span>`;
  });
  document.getElementById("commfigshead").style.display = figs.length ? "" : "none";
  document.getElementById("commfigs").innerHTML = figs.join("");
  document.getElementById("commconf").textContent =
    (L.confidence != null ? `How well-defined the labelling agent judged this community: ${Math.round(L.confidence * 100)}%. ` : "") +
    (insts.size ? `Interviews from ${[...insts].join(", ")}.` : "");
  commcard.classList.add("open");
}
document.getElementById("commclose").onclick = () => {
  isoComm = null;
  document.querySelectorAll(".commrow.active").forEach(el => el.classList.remove("active"));
  showCommCard(null); refilter(); fitView(); requestRender(0);
};
document.getElementById("commfigs").addEventListener("click", (e) => {
  const chip = e.target.closest(".pchip[data-i]");
  if (chip) select(+chip.dataset.i, true);
});
document.getElementById("commfigs").addEventListener("keydown", (e) => {
  if ((e.key === "Enter" || e.key === " ") && e.target.dataset.i) { e.preventDefault(); e.target.click(); }
});

/* ---------------- UI: rail ---------------- */
function buildRail() {
  commTop = new Map();
  for (const i of byDeg) {
    const c = COMM[i];
    let a = commTop.get(c);
    if (!a) { a = []; commTop.set(c, a); }
    if (a.length < 2) a.push(LABEL[i]);
  }
  const cl = document.getElementById("commlist");
  const shown = G.comm.filter(c => c.rank < NSLOT).sort((a, b) => a.rank - b.rank);
  const others = G.comm.filter(c => c.rank >= NSLOT).sort((a, b) => b.size - a.size);
  const otherN = others.reduce((s, c) => s + c.size, 0);
  const row = (c, color) =>
    `<div class="commrow" data-c="${c.rank}" role="button" tabindex="0"><span class="dot" style="background:${color}"></span>
     <span class="nm" title="${esc(commName(c.rank))}">${esc(commName(c.rank))}</span>
     <span class="cnt">${c.size.toLocaleString()}</span></div>`;
  cl.innerHTML = shown.map(c => row(c, PAL.SLOT[c.rank])).join("") +
    `<div class="commrow" id="othertoggle" role="button" tabindex="0"><span class="dot" style="background:${PAL.OTHER}"></span>
     <span class="nm">${others.length} other communities</span>
     <span class="cnt">${otherN.toLocaleString()} <span id="otherarrow">▸</span></span></div>
     <div id="otherlist" style="display:none">` +
    others.map(c => row(c, PAL.OTHER)).join("") + `</div>`;
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
    showCommCard(isoComm);
    if (isoComm !== null) fitCommunity(isoComm);       // bring the cluster into view
    else { fitView(); requestRender(0); }
  });
  cl.addEventListener("keydown", (e) => {
    if ((e.key === "Enter" || e.key === " ") && e.target.classList.contains("commrow")) { e.preventDefault(); e.target.click(); }
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
function buildSearch() {
  const inp = document.getElementById("search"), res = document.getElementById("results");
  const lower = LABEL.map(s => s.toLowerCase());
  let selRow = -1, rows = [];
  function run() {
    const q = inp.value.trim().toLowerCase();
    if (q.length < 2) { res.style.display = "none"; return; }
    rows = [];
    for (const i of byDeg) {
      if (lower[i].includes(q)) { rows.push(i); if (rows.length >= 7) break; }
    }
    selRow = 0;
    res.innerHTML = rows.map((i, ri) =>
      `<li role="option" aria-selected="${ri === 0}" data-i="${i}">
        <span class="dot" style="background:${commColor(COMM[i])}"></span>
        <span class="nm">${esc(LABEL[i])}</span><span class="deg">${DEG[i].toLocaleString()} relationships</span></li>`).join("");
    res.style.display = rows.length ? "block" : "none";
  }
  inp.addEventListener("input", run);
  inp.addEventListener("keydown", (e) => {
    if (e.key === "ArrowDown" || e.key === "ArrowUp") {
      e.preventDefault();
      selRow = Math.max(0, Math.min(rows.length - 1, selRow + (e.key === "ArrowDown" ? 1 : -1)));
      [...res.children].forEach((el, ri) => el.setAttribute("aria-selected", ri === selRow));
    } else if (e.key === "Enter" && rows.length) {
      e.preventDefault(); go(rows[selRow]);
    } else if (e.key === "Escape") { res.style.display = "none"; inp.blur(); }
  });
  res.addEventListener("mousedown", (e) => {
    const row = e.target.closest("li");
    if (row) { e.preventDefault(); go(+row.dataset.i); }
  });
  inp.addEventListener("blur", () => setTimeout(() => { res.style.display = "none"; }, 120));
  function go(i) { res.style.display = "none"; inp.blur(); select(i, true); }
}

/* ---------------- theme: follow the system, re-colour the canvas ---------------- */
function applyTheme() {
  readPalette();
  if (worker && workerReady) worker.postMessage({ type: "palette", PAL });
  if (G) requestRender(0);
}
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", applyTheme);

/* ---------------- boot ---------------- */
async function boot() {
  const msg = document.getElementById("loadmsg");
  let text;
  try {
    const r = await fetch("graph.data.js");
    if (!r.ok) throw new Error(r.status);
    text = await r.text();
  } catch (e) {
    msg.textContent = "The network data could not be loaded (graph.data.js, " + e.message + ").";
    document.querySelector("#loading .ring").style.display = "none";
    return;
  }
  msg.textContent = "Building the network…";
  await new Promise(r => setTimeout(r, 0));          // let the message paint
  const t0 = performance.now();
  unpack(JSON.parse(text.slice(text.indexOf("{"), text.lastIndexOf("}") + 1)));
  text = null;
  computeCore();
  buildGrid();
  IMGIDX = new Int32Array(N).fill(-1);
  for (let i = 0; i < N; i++) { const a = AT.ids[ID[i]]; if (a !== undefined) IMGIDX[i] = a; }
  relOn = G.types.map(() => true); instOn = G.insts.map(() => true);
  nodeVis = new Uint8Array(N); edgeVis = new Uint8Array(E);
  if (DEBUG) console.log(`[boot] unpack+index ${Math.round(performance.now() - t0)}ms`);

  document.getElementById("stats").textContent =
    `${N.toLocaleString()} people · ${E.toLocaleString()} relationships · 4 archives`;
  buildRail(); buildSearch();
  resize(); fitView(); recomputeVisibility();
  document.getElementById("loading").style.display = "none";
  if (worker) {
    const ETIER = new Uint8Array(E);
    for (let j = 0; j < E; j++) ETIER[j] = EW[j] < 1.2 ? 0 : EW[j] < 2.6 ? 1 : 2;
    worker.postMessage({
      type: "init", N, E, PAL, NSLOT,
      AT: { sheets: AT.sheets || 0, cell: AT.cell, perRow: AT.perRow, perSheet: AT.perSheet },
      X: X.slice(), Y: Y.slice(), SZ: SZ.slice(), COMM: COMM.slice(),
      FLAGS: FLAGS.slice(), DEG: DEG.slice(), IMGIDX: IMGIDX.slice(),
      LABEL, BYDEG: byDeg.slice(),
      EA: EA.slice(), EB: EB.slice(), ETIER,
      nodeVis: nodeVis.slice(), edgeVis: edgeVis.slice(),
    });
    workerReady = true;
    requestRender(0);
  } else {
    buf.width = (W + 2 * PAD) * DPR; buf.height = (H + 2 * PAD) * DPR;
    renderScene();
  }
  document.fonts.load('500 12px "Libre Franklin"').then(() => { if (!worker) renderScene(); drawOverlay(); }).catch(() => {});

  if (location.search.includes("dump")) {
    setTimeout(() => {
      const d = document.createElement("div");
      d.id = "canvasdump"; d.textContent = sceneEl.toDataURL("image/png"); d.style.display = "none";
      document.body.appendChild(d);
    }, 4000);
  }
  if (location.hash.length > 1) {
    const key = decodeURIComponent(location.hash.slice(1));
    const i = idIndex.get(key);
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
}
boot();
