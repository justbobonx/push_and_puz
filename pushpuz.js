/*
  PUSH & PUZ
  Seven rows on the long axis. Discs pack around a center well.
  Odd count sits on the well. Even count straddles it.
  Match-3 on a straight slot line: neighbors in a row, the same slot
  across rows, or a diagonal stepping one or two slots per row.
  Two resolved shots per turn. Opponent front cannot match the last shot.
  Empty rows refill from the board bag at end of turn. Refill does not fire matches.
  A visible disc on your end slot loses. Animation is not the grid.
*/

const ROWS = 7;
const END = 15;
const MATCH = 3;
const QLEN = 3;
const SHOTS = 2;
const BOARD_SETS = 3;
const COLS = [
  { fill: "#ff3b5c", hi: "#ffb6c6" },
  { fill: "#ff9f1a", hi: "#ffe3b8" },
  { fill: "#bb2bff", hi: "#db88ff" },
  { fill: "#2ee06a", hi: "#b5ffd1" },
  { fill: "#3aa0ff", hi: "#b8ddff" }
];
const BG = "#07080d";
const PCOL = ["#ff9f1a", "#3aa0ff"];
const SETTLE_MIN = 0.26;
const SETTLE_MAX = 0.9;
const POP_MS = 0.34;

const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d");
const APP_VERSION = ((document.getElementById("puz-version") || {}).textContent || "").trim();

const state = {
  w: 0, h: 0, viewW: 0, viewH: 0, dpr: 1, portrait: false,
  mode: "title", phase: "idle", phaseT: 0, turn: 0, shotsLeft: SHOTS,
  rows: [], bags: [[], []], boardBag: [], chain: 0, chainT: 0,
  loser: -1, last: 0, shot: null,
  boardLeft: 0, boardRight: 0, boardTop: 0, pitch: 0, half: 0, discR: 0, wellX: 0
};

function shuffle(list) {
  for (let i = list.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    const t = list[i];
    list[i] = list[j];
    list[j] = t;
  }
  return list;
}

function colorPackOfSets(sets) {
  const pack = [];
  for (let s = 0; s < sets; s++) {
    for (let c = 0; c < COLS.length; c++) pack.push(c);
  }
  return shuffle(pack);
}

function takeBoardColor() {
  while (state.boardBag.length < COLS.length * BOARD_SETS) {
    const more = colorPackOfSets(1);
    for (let k = 0; k < more.length; k++) state.boardBag.push(more[k]);
  }
  return state.boardBag.shift();
}

function mixHex(a, b, t) {
  const pa = parseInt(a.slice(1), 16);
  const pb = parseInt(b.slice(1), 16);
  const r = Math.round(((pa >> 16) & 255) + (((pb >> 16) & 255) - ((pa >> 16) & 255)) * t);
  const g = Math.round(((pa >> 8) & 255) + (((pb >> 8) & 255) - ((pa >> 8) & 255)) * t);
  const bl = Math.round((pa & 255) + ((pb & 255) - (pa & 255)) * t);
  return "rgb(" + r + "," + g + "," + bl + ")";
}

function makeCell(color) {
  return { color: color, x: 0, y: 0, vx: 0, vy: 0, tx: 0, ty: 0, pop: 0, popSide: -1, sc: 1 };
}

function freshRows() {
  const rows = [];
  for (let r = 0; r < ROWS; r++) rows.push({ cells: [], lw: 0, rw: 0, bal: 0, bvx: 0 });
  return rows;
}

function topUp(p) {
  if (state.bags[p].length >= QLEN) return;
  const more = colorPackOfSets(2);
  for (let k = 0; k < more.length; k++) state.bags[p].push(more[k]);
}

function settleFront(p, ban) {
  const bag = state.bags[p];
  let i = 0;
  while (true) {
    if (i >= bag.length) {
      const more = colorPackOfSets(2);
      for (let k = 0; k < more.length; k++) bag.push(more[k]);
    }
    if (ban < 0 || bag[i] !== ban) break;
    i++;
  }
  if (i === 0) return;
  const color = bag.splice(i, 1)[0];
  const skipped = bag.splice(0, i);
  for (let k = 0; k < skipped.length; k++) {
    const at = Math.floor(Math.random() * (bag.length + 1));
    bag.splice(at, 0, skipped[k]);
  }
  bag.unshift(color);
  topUp(p);
}

function slotsOf(row) {
  const n = row.cells.length;
  if (!n) return [];
  const s = row.lw - row.rw;
  const out = new Array(n);
  for (let k = 0; k < n; k++) out[k] = s - (n - 1) + 2 * k;
  return out;
}

function findMatches() {
  const hit = new Set();
  const cross = new Set();
  const rowLines = [];
  const slotRows = state.rows.map(slotsOf);
  function note(keys) {
    for (let n = 0; n < keys.length; n++) hit.add(keys[n]);
  }
  for (let r = 0; r < ROWS; r++) {
    const cells = state.rows[r].cells;
    const slots = slotRows[r];
    let i = 0;
    while (i < cells.length) {
      const col = cells[i].color;
      const parity = slots[i] & 1;
      let j = i + 1;
      while (j < cells.length && cells[j].color === col && (slots[j] & 1) === parity) j++;
      if (j - i >= MATCH) {
        const keys = [];
        for (let k = i; k < j; k++) keys.push(r + ":" + k);
        note(keys);
        rowLines.push({ r: r, keys: keys });
      }
      i = j;
    }
  }
  function at(r, slot, color) {
    const slots = slotRows[r];
    const cells = state.rows[r].cells;
    for (let i = 0; i < cells.length; i++) {
      if (slots[i] === slot && cells[i].color === color) return i;
    }
    return -1;
  }
  for (let r = 0; r < ROWS; r++) {
    const cells = state.rows[r].cells;
    const slots = slotRows[r];
    for (let i = 0; i < cells.length; i++) {
      const col = cells[i].color;
      const slot = slots[i];
      const dirs = [0, 1, -1, 2, -2];
      for (let d = 0; d < dirs.length; d++) {
        if (r + MATCH > ROWS) continue;
        const dir = dirs[d];
        const idx = [i];
        let ok = true;
        for (let s = 1; s < MATCH; s++) {
          const k = at(r + s, slot + dir * s, col);
          if (k < 0) { ok = false; break; }
          idx.push(k);
        }
        if (!ok) continue;
        const keys = [];
        for (let s = 0; s < MATCH; s++) keys.push((r + s) + ":" + idx[s]);
        note(keys);
        for (let s = 0; s < keys.length; s++) cross.add(keys[s]);
      }
    }
  }
  state.rowLines = rowLines;
  state.crossHits = cross;
  return hit;
}

function edgeLoss() {
  let left = false;
  let right = false;
  for (let r = 0; r < ROWS; r++) {
    const slots = slotsOf(state.rows[r]);
    for (let i = 0; i < slots.length; i++) {
      if (slots[i] <= -END) left = true;
      if (slots[i] >= END) right = true;
    }
  }
  return { left: left, right: right };
}

function slotX(slot) { return state.wellX + slot * state.half; }
function rowY(r) { return state.boardTop + (r + 0.5) * state.pitch; }

function layoutTargets() {
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    const slots = slotsOf(row);
    const y = rowY(r);
    for (let i = 0; i < row.cells.length; i++) {
      row.cells[i].tx = slotX(slots[i]);
      row.cells[i].ty = y;
    }
  }
}

function snapCells() {
  for (let r = 0; r < ROWS; r++) {
    const cells = state.rows[r].cells;
    for (let i = 0; i < cells.length; i++) {
      const c = cells[i];
      c.x = c.tx;
      c.y = c.ty;
      c.vx = 0;
      c.vy = 0;
    }
  }
}

function markPops(hit) {
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    for (let i = 0; i < row.cells.length; i++) {
      if (!hit.has(r + ":" + i)) continue;
      row.cells[i].pop = 1;
    }
  }
}

function finishPops() {
  const me = state.turn;
  const cross = state.crossHits || new Set();
  const add = [];
  for (let r = 0; r < ROWS; r++) add.push(0);
  function ours(bal, slot) {
    if (me === 0) return slot <= bal;
    return slot >= bal;
  }
  if (state.rowLines) {
    for (let n = 0; n < state.rowLines.length; n++) {
      const line = state.rowLines[n];
      const row = state.rows[line.r];
      const slots = slotsOf(row);
      const bal = row.lw - row.rw;
      let pay = false;
      for (let k = 0; k < line.keys.length; k++) {
        const i = Number(line.keys[k].split(":")[1]);
        if (ours(bal, slots[i])) pay = true;
      }
      if (pay) add[line.r]++;
    }
  }
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    const slots = slotsOf(row);
    const bal = row.lw - row.rw;
    const keep = [];
    for (let i = 0; i < row.cells.length; i++) {
      const c = row.cells[i];
      if (!c.pop) { keep.push(c); continue; }
      if (cross.has(r + ":" + i) && ours(bal, slots[i])) add[r]++;
    }
    row.cells = keep;
  }
  for (let r = 0; r < ROWS; r++) {
    if (!add[r]) continue;
    if (me === 0) state.rows[r].lw += add[r];
    else state.rows[r].rw += add[r];
  }
}

function newGame() {
  state.rows = freshRows();
  state.bags = [colorPackOfSets(2), colorPackOfSets(2)];
  state.boardBag = [];
  state.turn = Math.round(Math.random());
  state.shotsLeft = SHOTS;
  settleFront(1 - state.turn, state.bags[state.turn][0]);
  state.phase = "idle";
  state.phaseT = 0;
  state.chain = 0;
  state.chainT = 0;
  state.loser = -1;
  state.shot = null;
  state.mode = "play";
  for (let n = 0; n < 40; n++) {
    const dealt = [];
    for (let r = 0; r < ROWS; r++) {
      const a = takeBoardColor();
      const b = takeBoardColor();
      dealt.push(a, b);
      state.rows[r].cells = [makeCell(a), makeCell(b)];
    }
    if (!findMatches().size) break;
    for (let k = dealt.length - 1; k >= 0; k--) state.boardBag.unshift(dealt[k]);
    shuffle(state.boardBag);
  }
  layoutTargets();
  snapCells();
}

function fillEmptyRows() {
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    if (row.cells.length) continue;
    const cell = makeCell(takeBoardColor());
    const slot = row.lw - row.rw;
    cell.x = slotX(slot);
    cell.tx = cell.x;
    cell.y = rowY(r);
    cell.ty = cell.y;
    row.cells.push(cell);
  }
}

function requestPageFullscreen() {
  const el = document.documentElement;
  const req = el.requestFullscreen || el.webkitRequestFullscreen || el.webkitRequestFullScreen;
  if (!req) return;
  try {
    const p = req.call(el);
    if (p && typeof p.then === "function") p.catch(function () {});
  } catch (err) {}
}

function resize() {
  const dpr = Math.max(1, Math.min(3, window.devicePixelRatio || 1));
  const viewW = window.innerWidth;
  const viewH = window.innerHeight;
  canvas.width = Math.round(viewW * dpr);
  canvas.height = Math.round(viewH * dpr);
  canvas.style.width = viewW + "px";
  canvas.style.height = viewH + "px";
  state.viewW = viewW;
  state.viewH = viewH;
  state.dpr = dpr;
  state.portrait = viewH > viewW;
  state.w = Math.max(viewW, viewH);
  state.h = Math.min(viewW, viewH);
  const availH = state.h * 0.86;
  let pitch = availH / ROWS;
  const gutter = pitch * 0.34 * 2 + pitch * 0.4;
  const maxPitch = (state.w - gutter * 2) / (END + 0.5);
  if (pitch > maxPitch) pitch = maxPitch;
  state.pitch = pitch;
  state.half = pitch * 0.5;
  state.discR = pitch * 0.34;
  state.wellX = state.w * 0.5;
  state.boardTop = (state.h - pitch * ROWS) * 0.5;
  state.boardLeft = state.wellX - (END + 0.5) * state.half;
  state.boardRight = state.wellX + (END + 0.5) * state.half;
  if (state.mode !== "title") {
    layoutTargets();
    if (state.phase !== "settle" && state.phase !== "pop") snapCells();
    if (state.shot) {
      state.shot.cell.y = rowY(state.shot.row);
      state.shot.cell.tx = contactX(state.shot.row, state.shot.side);
    }
  }
}

function screenToWorld(sx, sy) {
  if (!state.portrait) return { x: sx, y: sy };
  return { x: sy, y: state.h - sx };
}

function rowAt(y) {
  const r = Math.floor((y - state.boardTop) / state.pitch);
  if (r < 0 || r >= ROWS) return -1;
  return r;
}

function contactX(row, side) {
  const slots = slotsOf(state.rows[row]);
  if (!slots.length) return slotX(0);
  if (side === 0) return slotX(slots[0]) - state.pitch;
  return slotX(slots[slots.length - 1]) + state.pitch;
}

function shoot(row) {
  if (state.mode !== "play" || state.phase !== "idle") return;
  if (row < 0 || row >= ROWS) return;
  const p = state.turn;
  const color = state.bags[p].shift();
  topUp(p);
  settleFront(1 - p, color);
  const cell = makeCell(color);
  cell.x = slotX(p === 0 ? -END - 2 : END + 2);
  cell.y = rowY(row);
  cell.tx = contactX(row, p);
  cell.ty = cell.y;
  cell.vx = p === 0 ? state.pitch * 9 : -state.pitch * 9;
  state.shot = { cell: cell, row: row, side: p };
  state.phase = "fly";
  state.phaseT = 0;
  state.chain = 0;
}

function afterSettle() {
  snapCells();
  const hit = findMatches();
  if (hit.size) {
    markPops(hit);
    state.chain++;
    state.chainT = 1.1;
    state.phase = "pop";
    state.phaseT = 0;
    return;
  }
  const loss = edgeLoss();
  if (loss.left || loss.right) {
    state.mode = "over";
    state.phase = "idle";
    state.loser = loss.left && loss.right ? 2 : (loss.left ? 0 : 1);
    return;
  }
  state.shotsLeft--;
  if (state.shotsLeft <= 0) {
    fillEmptyRows();
    state.turn = 1 - state.turn;
    state.shotsLeft = SHOTS;
  }
  state.phase = "idle";
}

function update(dt) {
  if (state.mode === "title") return;
  if (state.chainT > 0) state.chainT -= dt;
  const kBal = 78;
  const dampBal = 9.5;
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    const target = row.lw - row.rw;
    row.bvx += ((target - row.bal) * kBal - row.bvx * dampBal) * dt;
    row.bal += row.bvx * dt;
    if (Math.abs(target - row.bal) < 0.02 && Math.abs(row.bvx) < 0.4) {
      row.bal = target;
      row.bvx = 0;
    }
  }
  if (state.mode === "over") return;
  state.phaseT += dt;
  if (state.phase === "fly") {
    const shot = state.shot;
    const c = shot.cell;
    c.tx = contactX(shot.row, shot.side);
    c.ty = rowY(shot.row);
    c.vx += ((c.tx - c.x) * 70 - c.vx * 8) * dt;
    c.x += c.vx * dt;
    c.y += (c.ty - c.y) * Math.min(1, dt * 14);
    const arrived = shot.side === 0 ? c.x >= c.tx - 1 : c.x <= c.tx + 1;
    if (arrived || state.phaseT > 0.7) {
      c.x = c.tx;
      c.vx = shot.side === 0 ? state.pitch * 4 : -state.pitch * 4;
      if (shot.side === 0) state.rows[shot.row].cells.unshift(c);
      else state.rows[shot.row].cells.push(c);
      state.shot = null;
      layoutTargets();
      state.phase = "settle";
      state.phaseT = 0;
    }
    return;
  }
  if (state.phase === "settle") {
    let calm = true;
    const k = 78;
    const damp = 9.5;
    for (let r = 0; r < ROWS; r++) {
      const cells = state.rows[r].cells;
      for (let i = 0; i < cells.length; i++) {
        const c = cells[i];
        if (c.pop) continue;
        c.vx += ((c.tx - c.x) * k - c.vx * damp) * dt;
        c.vy += ((c.ty - c.y) * k - c.vy * damp) * dt;
        c.x += c.vx * dt;
        c.y += c.vy * dt;
        if (Math.abs(c.tx - c.x) > 1.4 || Math.abs(c.vx) > 36) calm = false;
      }
    }
    if ((calm && state.phaseT >= SETTLE_MIN) || state.phaseT >= SETTLE_MAX) afterSettle();
    return;
  }
  if (state.phase === "pop") {
    const t = state.phaseT / POP_MS;
    for (let r = 0; r < ROWS; r++) {
      const cells = state.rows[r].cells;
      for (let i = 0; i < cells.length; i++) {
        if (cells[i].pop) cells[i].sc = Math.max(0, 1 - t);
      }
    }
    if (t >= 1) {
      finishPops();
      layoutTargets();
      state.phase = "settle";
      state.phaseT = 0;
    }
  }
}

function drawDisc(x, y, r, ci, alpha, sc, shine) {
  if (sc <= 0.02 || alpha <= 0.02) return;
  const rr = r * sc;
  const c = COLS[ci];
  const edge = mixHex(c.fill, c.hi, 0.5);
  const outline = Math.max(1.6, rr * 0.11);
  ctx.save();
  ctx.globalAlpha = alpha;
  ctx.translate(x, y);
  ctx.beginPath();
  ctx.arc(0, 0, rr + outline + 3, 0, Math.PI * 2);
  ctx.fillStyle = "#000000";
  ctx.fill();
  ctx.beginPath();
  ctx.arc(0, 0, rr, 0, Math.PI * 2);
  ctx.fillStyle = c.fill;
  ctx.fill();
  ctx.lineWidth = outline;
  ctx.strokeStyle = edge;
  ctx.stroke();
  if (shine) {
    ctx.beginPath();
    ctx.arc(0, 0, rr * 0.72, Math.PI * 1.08, Math.PI * 1.78);
    ctx.strokeStyle = "rgba(255,255,255,0.78)";
    ctx.lineWidth = Math.max(1.5, rr * 0.14);
    ctx.lineCap = "round";
    ctx.stroke();
  }
  ctx.restore();
}

function drawQueue(p) {
  const bag = state.bags[p];
  const mine = state.mode === "play" && state.turn === p && state.phase === "idle";
  const r = state.discR;
  const gap = state.pitch * 0.9;
  const pad = state.pitch * 0.22;
  const x = p === 0 ? state.boardLeft - r - pad : state.boardRight + r + pad;
  const nextY = state.boardTop + state.pitch * ROWS * 0.5;
  const n = QLEN;
  for (let i = 0; i < n; i++) {
    const y = nextY - i * gap;
    const next = i === 0;
    const sc = next && mine ? 1.08 : 0.68;
    drawDisc(x, y, r, bag[i], 1, sc, next);
  }
}

function draw() {
  const dpr = state.dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (state.portrait) {
    ctx.translate(state.viewW, 0);
    ctx.rotate(Math.PI / 2);
  }
  ctx.fillStyle = BG;
  ctx.fillRect(0, 0, state.w, state.h);
  if (state.mode === "title") {
    const font = Math.min(state.w * 0.11, state.h * 0.34);
    ctx.save();
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.lineWidth = 3;
    ctx.strokeStyle = "#d7ecff";
    ctx.fillStyle = "#d7ecff";
    ctx.font = "900 " + font + "px ui-sans-serif, system-ui, sans-serif";
    ctx.globalAlpha = 0.16;
    ctx.fillText("PUSH & PUZ", state.w * 0.5, state.h * 0.46);
    ctx.globalAlpha = 1;
    ctx.strokeText("PUSH & PUZ", state.w * 0.5, state.h * 0.46);
    ctx.font = "400 " + Math.max(14, font * 0.16) + "px ui-sans-serif, system-ui, sans-serif";
    ctx.fillText("tap to start", state.w * 0.5, state.h * 0.68);
    ctx.textAlign = "right";
    ctx.font = "400 " + Math.max(11, font * 0.1) + "px ui-sans-serif, system-ui, sans-serif";
    ctx.fillText(APP_VERSION, state.w * 0.96, state.h * 0.95);
    ctx.restore();
    return;
  }

  ctx.save();
  ctx.fillStyle = "rgba(255,255,255,0.025)";
  ctx.fillRect(state.boardLeft, state.boardTop, state.boardRight - state.boardLeft, state.pitch * ROWS);
  const gridBottom = state.boardTop + state.pitch * ROWS;
  ctx.lineWidth = 1;
  ctx.strokeStyle = "rgba(190, 206, 220, 0.28)";
  ctx.beginPath();
  for (let i = 0; i <= ROWS; i++) {
    const y = state.boardTop + i * state.pitch;
    ctx.moveTo(state.boardLeft, y);
    ctx.lineTo(state.boardRight, y);
  }
  for (let s = -END + (END % 2); s <= END; s += 2) {
    const x = state.wellX + s * state.half;
    ctx.moveTo(x, state.boardTop);
    ctx.lineTo(x, gridBottom);
  }
  ctx.stroke();
  ctx.strokeStyle = "rgba(190, 206, 220, 0.28)";
  ctx.beginPath();
  for (let s = -END + ((END + 1) % 2); s <= END; s += 2) {
    const x = state.wellX + s * state.half;
    ctx.moveTo(x, state.boardTop);
    ctx.lineTo(x, gridBottom);
  }
  ctx.stroke();
  ctx.strokeStyle = "rgba(190, 206, 220, 0.4)";
  ctx.beginPath();
  ctx.moveTo(state.boardLeft, state.boardTop);
  ctx.lineTo(state.boardLeft, gridBottom);
  ctx.moveTo(state.boardRight, state.boardTop);
  ctx.lineTo(state.boardRight, gridBottom);
  ctx.stroke();
  ctx.strokeStyle = "rgba(190, 206, 220, 0.28)";
  ctx.lineWidth = 4;
  ctx.beginPath();
  ctx.moveTo(state.wellX, state.boardTop);
  ctx.lineTo(state.wellX, gridBottom);
  ctx.stroke();
  ctx.restore();

  ctx.save();
  ctx.strokeStyle = "rgba(255, 226, 140, 0.9)";
  ctx.lineWidth = 3;
  ctx.lineCap = "butt";
  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    let x = state.wellX + row.bal * state.half;
    if (x < state.boardLeft) x = state.boardLeft;
    if (x > state.boardRight) x = state.boardRight;
    const y0 = state.boardTop + r * state.pitch;
    ctx.beginPath();
    ctx.moveTo(x, y0);
    ctx.lineTo(x, y0 + state.pitch);
    ctx.stroke();
  }
  ctx.restore();

  for (let r = 0; r < ROWS; r++) {
    const row = state.rows[r];
    const y = rowY(r);
    const net = row.lw - row.rw;
    ctx.save();
    ctx.globalAlpha = 0.55;
    if (net > 0) {
      ctx.fillStyle = PCOL[0];
      ctx.fillRect(state.boardLeft, y - 2, Math.min(state.half * net, state.boardRight - state.boardLeft), 3);
    } else if (net < 0) {
      ctx.fillStyle = PCOL[1];
      const span = Math.min(state.half * -net, state.boardRight - state.boardLeft);
      ctx.fillRect(state.boardRight - span, y - 2, span, 3);
    }
    ctx.restore();
    for (let i = 0; i < row.cells.length; i++) {
      const c = row.cells[i];
      drawDisc(c.x, c.y, state.discR, c.color, 1, c.sc == null ? 1 : c.sc, true);
    }
  }
  if (state.shot) {
    const c = state.shot.cell;
    drawDisc(c.x, c.y, state.discR, c.color, 1, 1, true);
  }

  ctx.save();
  ctx.lineWidth = 3;
  ctx.strokeStyle = PCOL[0];
  ctx.globalAlpha = state.turn === 0 && state.phase === "idle" ? 0.95 : 0.28;
  ctx.strokeRect(state.boardLeft - 2, state.boardTop, 4, state.pitch * ROWS);
  ctx.strokeStyle = PCOL[1];
  ctx.globalAlpha = state.turn === 1 && state.phase === "idle" ? 0.95 : 0.28;
  ctx.strokeRect(state.boardRight - 2, state.boardTop, 4, state.pitch * ROWS);
  ctx.restore();

  drawQueue(0);
  drawQueue(1);

  if (state.mode === "play") {
    ctx.save();
    const pip = Math.max(3.5, state.pitch * 0.09);
    const pipGap = pip * 3.1;
    const pipX = state.turn === 0 ? state.boardLeft + pip * 2.2 : state.boardRight - pip * 2.2;
    const pipY = state.boardTop - pip * 2.4;
    for (let i = 0; i < SHOTS; i++) {
      ctx.beginPath();
      ctx.arc(pipX + (i - (SHOTS - 1) * 0.5) * pipGap, pipY, pip, 0, Math.PI * 2);
      ctx.fillStyle = PCOL[state.turn];
      ctx.globalAlpha = i < state.shotsLeft ? 0.92 : 0.2;
      ctx.fill();
    }
    ctx.restore();
  }

  ctx.save();
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillStyle = "#d7ecff";
  const small = Math.max(13, state.h * 0.04);
  ctx.font = "600 " + small + "px ui-sans-serif, system-ui, sans-serif";
  if (state.mode === "over") {
    const msg = state.loser === 2 ? "BOTH OUT" : (state.loser === 0 ? "LEFT OUT" : "RIGHT OUT");
    ctx.fillText(msg, state.w * 0.5, state.boardTop - small * 0.9);
    ctx.font = "400 " + (small * 0.72) + "px ui-sans-serif, system-ui, sans-serif";
    ctx.fillText("tap to restart", state.w * 0.5, state.boardTop + state.pitch * ROWS + small);
  } else if (state.chainT > 0 && state.chain > 1) {
    ctx.fillText("CHAIN " + state.chain, state.w * 0.5, state.boardTop - small * 0.7);
  }
  ctx.restore();
}

function onPoint(x, y) {
  if (state.mode === "title") {
    requestPageFullscreen();
    resize();
    newGame();
    return;
  }
  if (state.mode === "over") {
    newGame();
    return;
  }
  if (state.phase !== "idle") return;
  const row = rowAt(y);
  if (row < 0) return;
  if (state.turn === 0 && x >= state.wellX) return;
  if (state.turn === 1 && x <= state.wellX) return;
  shoot(row);
}

function bindInput() {
  canvas.addEventListener("pointerdown", function (ev) {
    const r = canvas.getBoundingClientRect();
    const p = screenToWorld(ev.clientX - r.left, ev.clientY - r.top);
    onPoint(p.x, p.y);
  }, { passive: false });
  canvas.addEventListener("contextmenu", function (ev) { ev.preventDefault(); });
  window.addEventListener("keydown", function (ev) {
    if (state.mode === "title" && (ev.code === "Space" || ev.code === "Enter")) {
      onPoint(state.w * 0.5, state.h * 0.5);
      return;
    }
    const n = ev.keyCode >= 49 && ev.keyCode <= 55 ? ev.keyCode - 49 : -1;
    if (n >= 0) shoot(n);
  });
  window.addEventListener("resize", resize);
}

function frame(now) {
  if (!state.last) state.last = now;
  let dt = (now - state.last) / 1000;
  state.last = now;
  if (dt > 0.05) dt = 0.05;
  update(dt);
  draw();
  requestAnimationFrame(frame);
}

bindInput();
resize();
requestAnimationFrame(frame);

