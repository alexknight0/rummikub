"use strict";
// Rummikub: table, rack, drag and drop, turns, computer players.
//
// State S (saved to localStorage after every change):
//   tiles[id] = {c, n}; pool = [id] (drawn from the end)
//   board = {id: [row, col]}  — a set is a horizontal run of adjacent tiles
//   players[i] = {name, type: "human"|"easy"|"hard", rack: {id: slot}, melded}
//   turnStart = {board, rack} at the start of the current turn (for reset and rules)
//   history = undo stack of {board, rack}
//
// Online games (online.js) use the same S, built from Firestore by applyRemote():
// S.online = {id, seat, moveNo}; only this device's rack is known, other players
// have p.count instead, and S.poolCount replaces S.pool. Turns are sent with
// Online.play / Online.draw rather than the local turn loop.

const SAVE_KEY = "rummikub:game";
const SETTINGS_KEY = "rummikub:settings";
const RACK_MIN_ROWS = 2;
const ANIM_MS = 320;
const DRAW_MS = 650;
const AI_MIN_THINK_MS = 900;
const AVATAR_COLOURS = ["#3b7dd8", "#d0533f", "#3aa168", "#9b59b6"];
const DEFAULT_SETTINGS = {
  players: [{ name: "You", type: "human" }, { name: "Computer", type: "hard" }],
  timer: 60,
};

const $ = (sel) => document.querySelector(sel);
const boardEl = $("#board");
const rackEl = $("#rack");
const boardWrap = $("#board-wrap");
const rackWrap = $("#rack-wrap");
const dragLayer = $("#drag-layer");

let S = null;
let covered = false; // pass-and-play hand-off screen is showing
let busy = false; // a turn is ending (animations playing); ignore input
let thinking = null; // index of the computer player currently thinking
let drag = null;
let gameToken = 0; // bumped on every new game so stale timeouts do nothing
let worker = null;
let aiReq = 0;
const aiPending = new Map(); // worker request id -> resolve
const L = { cw: 40, ch: 52, rw: 40, rh: 52, rackCols: 10, rackRows: 2, cols: 14, rows: 8 };
const landscapePhone = matchMedia("(orientation: landscape) and (max-height: 500px)");
const els = new Map(); // tile id -> element
const ghosts = new Map(); // tile id -> flying copy currently animating

const clone = (o) => JSON.parse(JSON.stringify(o));
const keys = (obj) => Object.keys(obj).map(Number);
const tile = (id) => S.tiles[id];
const cur = () => S.players[S.turn];
const humanCount = () => S.players.filter((p) => p.type === "human").length;
const rackCount = (p) => p.count ?? keys(p.rack).length;
const poolLeft = () => (S.online ? S.poolCount : S.pool.length);
// It's this device's turn (always true for a human's turn in a local game).
const myTurn = () => !S.over && (S.online ? S.turn === S.online.seat : cur().type === "human");
const later = (fn, ms) => {
  const token = gameToken;
  setTimeout(() => token === gameToken && fn(), ms);
};

// ---------------------------------------------------------------- state

function save() {
  try {
    // Online, only how this device arranged its rack is kept locally.
    if (S.online) localStorage.setItem(rackKey(), JSON.stringify(S.players[S.online.seat].rack));
    else localStorage.setItem(SAVE_KEY, JSON.stringify(S));
  } catch { /* storage full or blocked */ }
}

const rackKey = () => `rummikub:rack:${S.online.id}:${S.online.uid}`;

function loadLocalGame() {
  try {
    const saved = JSON.parse(localStorage.getItem(SAVE_KEY));
    return saved && saved.v === 1 ? saved : null;
  } catch { return null; }
}

function loadSettings() {
  try { return { ...DEFAULT_SETTINGS, ...JSON.parse(localStorage.getItem(SETTINGS_KEY)) }; } catch { return clone(DEFAULT_SETTINGS); }
}

function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function newGame(settings) {
  localStorage.setItem(SETTINGS_KEY, JSON.stringify(settings));
  localStorage.setItem(MODE_KEY, "local");
  window.Online?.leaveView();
  closeHome();
  gameToken++;
  busy = false;
  thinking = null;

  cancelDrag();
  const tiles = makeDeck();
  S = {
    v: 1,
    tiles,
    pool: shuffle(tiles.map((_, i) => i)),
    board: {},
    players: settings.players.map((p) => ({ name: p.name, type: p.type, rack: {}, melded: false })),
    turn: Math.floor(Math.random() * settings.players.length),
    timer: settings.timer,
    passes: 0,
    lastPlaced: [],
    viewer: null,
    over: null,
    settings,
  };
  for (const p of S.players) for (let i = 0; i < 14; i++) p.rack[S.pool.pop()] = i;
  S.viewer = S.players.findIndex((p) => p.type === "human");
  for (const el of els.values()) el.remove();
  els.clear();
  buildChips();
  startTurn();
}

// Whose rack is shown at the bottom.
function viewerIndex() {
  if (!S) return -1;
  if (S.online) return S.online.seat;
  if (cur().type === "human") return S.turn;
  return S.viewer ?? -1;
}

function isHumanTurn() {
  return !!S && !covered && !busy && myTurn();
}

function snapshot() {
  return { board: clone(S.board), rack: clone(S.players[viewerIndex()].rack) };
}

function restore(snap) {
  S.board = snap.board;
  S.players[viewerIndex()].rack = snap.rack;
}

function getSets(board) {
  const rows = new Map();
  for (const id of keys(board)) {
    const [r, c] = board[id];
    if (!rows.has(r)) rows.set(r, []);
    rows.get(r).push([c, id]);
  }
  const out = [];
  for (const [r, cells] of [...rows].sort((a, b) => a[0] - b[0])) {
    cells.sort((a, b) => a[0] - b[0]);
    let set = null;
    let prev = -2;
    for (const [c, id] of cells) {
      if (c !== prev + 1) out.push((set = { r, c, ids: [] }));
      set.ids.push(id);
      prev = c;
    }
  }
  return out;
}

const setInfo = (ids) => analyzeSet(ids.map(tile));

function placedThisTurn() {
  return keys(S.board).filter((id) => id in S.turnStart.rack);
}

function turnChanged() {
  return JSON.stringify(S.board) !== JSON.stringify(S.turnStart.board);
}

// Points of the first meld so far (sets made only of this turn's tiles).
function meldPoints() {
  let pts = 0;
  for (const s of getSets(S.board)) {
    if (!s.ids.every((id) => id in S.turnStart.rack)) continue;
    const a = setInfo(s.ids);
    if (a.valid) pts += a.value;
  }
  return pts;
}

function validateTurn() {
  const placed = placedThisTurn();
  if (!placed.length) return { err: "Place at least one tile from your rack, or draw." };
  const sets = getSets(S.board);
  if (sets.some((s) => !setInfo(s.ids).valid)) return { err: "Some sets on the table aren't valid yet.", shake: true };
  if (!cur().melded) {
    for (const s of sets) {
      const fresh = s.ids.filter((id) => id in S.turnStart.rack).length;
      if (fresh && fresh < s.ids.length) return { err: "Your first meld must use only tiles from your rack." };
    }
    const pts = meldPoints();
    if (pts < FIRST_MELD) return { err: `Your first meld must be worth at least ${FIRST_MELD} points (you have ${pts}).` };
  }
  return { placed };
}

// ---------------------------------------------------------------- moves

function canDrag(id) {
  if (!S || S.over || covered || busy) return false;
  const v = viewerIndex();
  if (v >= 0 && id in S.players[v].rack) return true; // rearranging your rack is always allowed
  if (!(id in S.board) || !isHumanTurn()) return false;
  return cur().melded || id in S.turnStart.rack;
}

function boardOcc() {
  const occ = new Map();
  for (const id of keys(S.board)) occ.set(S.board[id][0] * 1000 + S.board[id][1], id);
  return occ;
}

// Drops a tile at (r, c). If a set is already there:
// - if putting the tile into the set at that spot makes it valid, it goes in
//   and the set grows (pushing any set it would touch out of the way);
// - otherwise the set moves out of the way to the nearest free spot.
// Before the first meld, sets always move out of the way.
function placeOnBoard(id, r, c) {
  const target = getSets(S.board).find((s) => s.r === r && c >= s.c && c < s.c + s.ids.length);
  if (!target) {
    S.board[id] = [r, c];
    return true;
  }
  const grown = target.ids.slice();
  grown.splice(c - target.c, 0, id);
  if (cur().melded && setInfo(grown).valid) {
    const start = Math.max(0, Math.min(target.c, L.cols - grown.length));
    for (const t of target.ids) delete S.board[t];
    // Sets that would overlap or touch the grown set (found before placing
    // it, while they're still separate sets) move out of the way.
    const blockers = getSets(S.board).filter((s) => s.r === r && s.c <= start + grown.length && s.c + s.ids.length >= start);
    for (const s of blockers) for (const t of s.ids) delete S.board[t];
    grown.forEach((t, i) => { S.board[t] = [r, start + i]; });
    for (const s of blockers) moveSetNear(s.ids, r, s.c);
    return true;
  }
  for (const t of target.ids) delete S.board[t];
  S.board[id] = [r, c];
  moveSetNear(target.ids, r, target.c);
  return true;
}

// Puts a set (currently off the table) in the free spot closest to (r, c),
// with a gap on both sides so it doesn't join another set (or the tile just
// dropped). Uses a new row below if the visible table is full (the table
// then shrinks to fit on the next render).
function moveSetNear(ids, r, c) {
  const len = ids.length;
  const cols = Math.max(L.cols - 1, len);
  for (let rows = L.rows - 1; ; rows++) {
    const occ = boardOcc();
    const free = (rr, x) => x < 0 || x >= cols || !occ.has(rr * 1000 + x);
    let best = null;
    for (let rr = 0; rr < rows; rr++) {
      for (let x = 0; x + len <= cols; x++) {
        let ok = true;
        for (let k = x - 1; k <= x + len && ok; k++) ok = free(rr, k);
        if (!ok) continue;
        const d = Math.abs(rr - r) * 3 + Math.abs(x - c);
        if (!best || d < best.d) best = { rr, x, d };
      }
    }
    if (best) {
      ids.forEach((t, i) => { S.board[t] = [best.rr, best.x + i]; });
      return;
    }
  }
}

// Drops a tile in a rack slot; tiles from there on shift along to the next gap.
function placeInRack(rack, id, slot) {
  const occ = new Map(keys(rack).map((k) => [rack[k], k]));
  let j = slot;
  while (occ.has(j)) j++;
  for (let x = j - 1; x >= slot; x--) rack[occ.get(x)] = x + 1;
  rack[id] = slot;
  return true;
}

function firstFreeSlot(rack) {
  const used = new Set(Object.values(rack));
  let i = 0;
  while (used.has(i)) i++;
  return i;
}

function tryMove(id, dest) {
  const v = viewerIndex();
  if (v < 0) return false;
  const rack = S.players[v].rack;
  const fromRack = id in rack;
  if (dest.area === "board" && !isHumanTurn()) {
    toast(covered || busy ? "" : "Wait for your turn.");
    return false;
  }
  if (dest.area === "rack" && !fromRack && !(id in S.turnStart.rack)) {
    toast("Tiles from the table can't go into your rack.");
    return false;
  }
  const before = snapshot();
  if (fromRack) delete rack[id];
  else delete S.board[id];
  const ok = dest.area === "board" ? placeOnBoard(id, dest.r, dest.c) : placeInRack(S.players[v].rack, id, dest.slot);
  if (!ok) { restore(before); return false; }
  if (isHumanTurn()) S.history.push(before);
  save();
  return true;
}

// Moves a whole table set so the grabbed tile (index idx) lands at dest.
// Sets it would overlap or touch move out of the way.
function tryMoveSet(ids, idx, dest) {
  if (dest.area !== "board" || !isHumanTurn()) {
    if (dest.area === "rack") toast("Drag tiles one at a time to put them back in your rack.");
    return false;
  }
  const n = ids.length;
  const r = dest.r;
  const c = Math.max(0, Math.min(dest.c - idx, L.cols - n));
  const before = snapshot();
  for (const t of ids) delete S.board[t];
  const blockers = getSets(S.board).filter((s) => s.r === r && s.c <= c + n && s.c + s.ids.length >= c);
  for (const s of blockers) for (const t of s.ids) delete S.board[t];
  ids.forEach((t, i) => { S.board[t] = [r, c + i]; });
  for (const s of blockers) moveSetNear(s.ids, r, s.c);
  if (JSON.stringify(S.board) === JSON.stringify(before.board)) return false;
  S.history.push(before);
  save();
  return true;
}

function sortRack(mode) {
  const v = viewerIndex();
  if (v < 0 || covered) return;
  const rack = S.players[v].rack;
  const list = keys(rack).map((id) => ({ id, ...tile(id) }));
  const key = mode === "num" ? (t) => (isJoker(t) ? 1e4 : t.n * 10 + t.c) : (t) => (isJoker(t) ? 1e4 : t.c * 100 + t.n);
  list.sort((a, b) => key(a) - key(b) || a.id - b.id);
  // Sets ready to play come first (777: groups, 789: runs), each in its own
  // block; the leftover tiles follow in one block, sorted as before.
  const ready = mode === "num" ? readyGroups(list) : readyRuns(list);
  const inReady = new Set(ready.flat().map((t) => t.id));
  const seq = [];
  ready.forEach((s, i) => s.forEach((t) => seq.push({ t, g: "set" + i })));
  for (const t of list) if (!inReady.has(t.id)) seq.push({ t, g: "rest" });
  const groups = new Set(seq.map((x) => x.g)).size;
  const gaps = seq.length + groups - 1 <= Math.max(RACK_MIN_ROWS, L.rackRows) * L.rackCols;
  if (isHumanTurn()) S.history.push(snapshot());
  let slot = 0;
  let prev = null;
  for (const { t, g } of seq) {
    if (gaps && prev !== null && g !== prev) slot++;
    rack[t.id] = slot++;
    prev = g;
  }
  save();
  render();
}

// Groups (3-4 different colours of one number) in sorted tiles. Jokers are left out.
function readyGroups(list) {
  const out = [];
  for (let n = 1; n <= 13; n++) {
    const byColour = [[], [], [], []];
    for (const t of list) if (!isJoker(t) && t.n === n) byColour[t.c].push(t);
    for (;;) {
      const have = byColour.filter((a) => a.length);
      if (have.length < 3) break;
      out.push(have.map((a) => a.shift()));
    }
  }
  return out;
}

// Runs (3+ in a row, one colour) in sorted tiles, longest streaks first
// within each colour. Jokers are left out.
function readyRuns(list) {
  const out = [];
  for (let c = 0; c < 4; c++) {
    const byNum = Array.from({ length: 15 }, () => []);
    for (const t of list) if (t.c === c) byNum[t.n].push(t);
    for (;;) {
      let best = null;
      for (let s = 1; s <= 13; s++) {
        if (!byNum[s].length || byNum[s - 1].length) continue;
        let e = s;
        while (byNum[e + 1].length) e++;
        if (e - s + 1 >= 3 && (!best || e - s > best[1] - best[0])) best = [s, e];
      }
      if (!best) break;
      const run = [];
      for (let n = best[0]; n <= best[1]; n++) run.push(byNum[n].shift());
      out.push(run);
    }
  }
  return out;
}

function undo() {
  if (!isHumanTurn() || !S.history.length) return;
  restore(S.history.pop());
  save();
  render();
}

// Puts this turn's tiles back in the rack (keeping how the rack is arranged).
function revertTurn() {
  const rack = cur().rack;
  S.board = clone(S.turnStart.board);
  const used = new Set(Object.values(rack));
  for (const id of keys(S.turnStart.rack)) {
    if (id in rack) continue;
    let slot = S.turnStart.rack[id];
    if (used.has(slot)) slot = firstFreeSlot(rack);
    rack[id] = slot;
    used.add(slot);
  }
  S.history = [];
}

function resetTurn() {
  if (!isHumanTurn()) return;
  revertTurn();
  save();
  render();
}

function drawTile(pi) {
  if (!S.pool.length) return null;
  const id = S.pool.pop();
  const rack = S.players[pi].rack;
  rack[id] = firstFreeSlot(rack);
  return id;
}

// ---------------------------------------------------------------- turns

function startTurn() {
  const p = cur();
  S.turnStart = { board: clone(S.board), rack: clone(p.rack) };
  S.history = [];
  S.turnDeadline = null;
  busy = false;
  if (p.type === "human") {
    S.viewer = S.turn;
    covered = humanCount() > 1;
    if (!covered) armTimer();
  } else covered = false;
  save();
  render();
  if (p.type !== "human") later(runAI, 350);
}

function armTimer() {
  S.turnDeadline = S.timer ? Date.now() + S.timer * 1000 : null;
}

function onMain() {
  if (!isHumanTurn()) return;
  if (!placedThisTurn().length) return submitDraw();
  const v = validateTurn();
  if (v.err) {
    toast(v.err);
    if (v.shake) shakeInvalid();
    return;
  }
  submitPlay(v.placed);
}

function submitPlay(placed) {
  if (S.online) return sendOnline(() => Online.play(placed));
  commitTurn(placed);
}

function submitDraw() {
  if (S.online) {
    cancelDrag();
    revertTurn();
    render();
    return sendOnline(() => Online.draw());
  }
  humanDraw();
}

// Sends a move; the board updates when Firestore sends it back.
async function sendOnline(fn) {
  busy = true;
  renderHUD();
  try {
    await fn();
  } catch (e) {
    console.warn(e);
    busy = false;
    toast(e?.message === "stale" ? "The game moved on without you." : "Couldn't send your move. Check your connection.");
    render();
  }
}

function commitTurn(placed) {
  cur().melded = true;
  S.lastPlaced = placed;
  S.passes = 0;
  busy = true;
  save();
  render();
  later(endTurn, 250);
}

function humanDraw() {
  busy = true;
  revertTurn();
  const id = drawTile(S.turn);
  S.lastPlaced = [];
  if (id === null) {
    S.passes++;
    toast("The pool is empty. You pass.");
  } else S.passes = 0;
  save();
  render(id === null ? {} : { from: new Map([[id, $("#pool").getBoundingClientRect()]]), flip: new Set([id]) });
  later(endTurn, DRAW_MS + 100);
}

function endTurn() {
  if (!keys(cur().rack).length) return gameOver(S.turn);
  if (S.passes >= S.players.length) return gameOver(null);
  S.turn = (S.turn + 1) % S.players.length;
  startTurn();
}

function onTimeout() {
  cancelDrag();
  const v = validateTurn();
  if (!v.err) {
    toast("Time's up. Your move was played.");
    submitPlay(v.placed);
  } else {
    toast("Time's up! Your tiles went back and you drew a tile.");
    submitDraw();
  }
}

function gameOver(winner) {
  const vals = S.players.map((p) => keys(p.rack).reduce((a, id) => a + rackValue(tile(id)), 0));
  if (winner === null) winner = vals.indexOf(Math.min(...vals));
  const scores = vals.map((v) => -(v - vals[winner]));
  scores[winner] = -scores.reduce((a, b) => a + b, 0);
  S.over = { winner, vals, scores };
  S.turnDeadline = null;
  busy = false;
  save();
  render();
  later(showResults, 500);
}

// ---------------------------------------------------------------- computer players

function startWorker() {
  try {
    worker = new Worker("ai.js");
    worker.onmessage = (e) => {
      const done = aiPending.get(e.data.reqId);
      aiPending.delete(e.data.reqId);
      done?.(e.data.result);
    };
    worker.onerror = () => { worker = null; };
  } catch { worker = null; }
}

// Asks the computer for a move. rack: tile ids; resolves to aiMove's result.
function requestAIMove(board, rack, melded, level) {
  const msg = {
    reqId: ++aiReq,
    sets: getSets(board).map((s) => s.ids.map((id) => ({ id, ...tile(id) }))),
    rack: rack.map((id) => ({ id, ...tile(id) })),
    melded,
    level,
    timeLimit: level === "hard" ? 1500 : 300,
  };
  if (!worker) return Promise.resolve(aiMove(msg));
  return new Promise((resolve) => {
    aiPending.set(msg.reqId, resolve);
    worker.postMessage(msg);
  });
}

async function runAI() {
  if (!S || S.over || cur().type === "human") return;
  const pi = S.turn;
  const p = cur();
  const token = gameToken;
  thinking = pi;
  renderHUD();
  const t0 = performance.now();
  const result = await requestAIMove(S.board, keys(p.rack), p.melded, p.type);
  if (token !== gameToken) return;
  later(() => S.turn === pi && !S.over && applyAI(pi, result), Math.max(0, AI_MIN_THINK_MS - (performance.now() - t0)));
}

// p: {rack: {id: slot}, melded}; checks a computer move against the table in S.
function aiMoveIsLegal(p, res) {
  const all = res.sets.flat();
  const old = keys(S.board);
  if (new Set(all).size !== all.length || all.length !== old.length + res.placed.length) return false;
  if (!old.every((id) => all.includes(id)) || !res.placed.every((id) => id in p.rack)) return false;
  if (!res.sets.every((s) => setInfo(s).valid)) return false;
  if (!p.melded) {
    const placed = new Set(res.placed);
    let pts = 0;
    for (const s of res.sets) {
      const k = s.filter((id) => placed.has(id)).length;
      if (k && k < s.length) return false;
      if (k) pts += setInfo(s).value;
    }
    if (pts < FIRST_MELD) return false;
  }
  return true;
}

function applyAI(pi, res) {
  thinking = null;
  const p = S.players[pi];
  if (res && !aiMoveIsLegal(p, res)) {
    console.warn("AI produced an illegal move; drawing instead", res);
    res = null;
  }
  busy = true;
  const chip = chipRect(pi);
  if (!res) {
    const id = drawTile(pi);
    S.lastPlaced = [];
    if (id === null) S.passes++;
    else {
      S.passes = 0;
      flyFaceDown($("#pool").getBoundingClientRect(), chip);
    }
    save();
    render();
    later(endTurn, DRAW_MS);
    return;
  }
  const from = new Map();
  const stagger = new Map();
  res.placed.forEach((id, i) => {
    from.set(id, chip);
    stagger.set(id, i * 90);
    delete p.rack[id];
  });
  S.board = layoutSets(res.sets, S.board);
  p.melded = true;
  S.lastPlaced = res.placed;
  S.passes = 0;
  save();
  render({ from, flip: new Set(res.placed), stagger });
  later(endTurn, DRAW_MS + res.placed.length * 90);
}

// Positions the computer's new table. Sets keep their old spot when they can
// (most of their tiles were already there), the rest go in the first gap.
function layoutSets(sets, old) {
  // Leave the spare last row and column free (see computeLayout).
  const cols = Math.max(L.cols - 1, ...sets.map((s) => s.length));
  for (let rows = L.rows - 1; ; rows++) {
    const out = tryLayout(sets, old, rows, cols);
    if (out) return out;
  }
}

function tryLayout(sets, old, rows, cols) {
  const grid = Array.from({ length: rows }, () => new Array(cols).fill(false));
  const out = {};
  const fits = (r, c, len) => {
    if (r < 0 || r >= rows || c < 0 || c + len > cols) return false;
    for (let x = Math.max(0, c - 1); x <= Math.min(cols - 1, c + len); x++) if (grid[r][x]) return false;
    return true;
  };
  const put = (r, c, ids) => ids.forEach((id, i) => { grid[r][c + i] = true; out[id] = [r, c + i]; });
  const items = sets.map((ids) => {
    const votes = new Map();
    ids.forEach((id, i) => {
      if (!old[id]) return;
      const k = `${old[id][0]},${old[id][1] - i}`;
      votes.set(k, (votes.get(k) || 0) + 1);
    });
    const best = [...votes].sort((a, b) => b[1] - a[1])[0];
    return { ids, anchor: best && best[0].split(",").map(Number), votes: best ? best[1] : 0 };
  });
  items.sort((a, b) => b.votes - a.votes);
  const rest = [];
  for (const it of items) {
    if (it.anchor && fits(it.anchor[0], it.anchor[1], it.ids.length)) put(it.anchor[0], it.anchor[1], it.ids);
    else rest.push(it);
  }
  for (const it of rest) {
    let done = false;
    for (let r = 0; r < rows && !done; r++)
      for (let c = 0; c + it.ids.length <= cols && !done; c++)
        if (fits(r, c, it.ids.length)) { put(r, c, it.ids); done = true; }
    if (!done) return null;
  }
  return out;
}

// ---------------------------------------------------------------- online games

const MODE_KEY = "rummikub:mode"; // "local" or "online": which game the page reopens
const SKIP_GRACE_MS = 30_000; // after a human's timer runs out, others may skip them this much later

// Builds S from a Firestore game (called by online.js) and animates the change.
// g: game doc; hand: this player's tile ids; me: {uid, seat}.
function applyRemote(id, g, hand, me) {
  const same = S?.online?.id === id ? S : null;
  if (same && same.online.moveNo === g.moveNo) return;
  cancelDrag();
  if (!same) {
    gameToken++;
    thinking = null;
    for (const el of els.values()) el.remove();
    els.clear();
  }
  covered = false;
  localStorage.setItem(MODE_KEY, "online");

  // Keep how this device arranged its rack; new tiles go in the first gap.
  let prevRack = same ? same.players[me.seat].rack : null;
  if (!prevRack) {
    try { prevRack = JSON.parse(localStorage.getItem(`rummikub:rack:${id}:${me.uid}`)) || {}; } catch { prevRack = {}; }
  }
  const rack = {};
  const used = new Set();
  for (const t of hand) {
    if (t in prevRack && !used.has(prevRack[t])) { rack[t] = prevRack[t]; used.add(prevRack[t]); }
  }
  for (const t of hand) if (!(t in rack)) rack[t] = firstFreeSlot(rack);

  const board = {};
  for (const [t, rc] of Object.entries(g.board || {})) board[t] = [Math.floor(rc / 100), rc % 100];

  // Animations: another player's new tiles fly from their avatar; tiles new to
  // this rack fly face down from the pool and flip.
  const from = new Map();
  const flip = new Set();
  const stagger = new Map();
  let faceDownTo = null;
  if (same && g.lastMove) {
    const m = g.lastMove.seat;
    if (m !== me.seat && g.lastMove.kind === "play") {
      const chip = chipRect(m);
      let i = 0;
      for (const t of keys(board)) {
        if (t in same.board) continue;
        from.set(t, chip);
        flip.add(t);
        stagger.set(t, i++ * 90);
      }
    } else if (m !== me.seat && g.lastMove.kind === "draw") faceDownTo = m;
    for (const t of hand) {
      if (!(t in prevRack) && !els.has(t)) {
        from.set(t, $("#pool").getBoundingClientRect());
        flip.add(t);
      }
    }
  }

  S = {
    v: 1,
    online: { id, seat: me.seat, uid: me.uid, moveNo: g.moveNo, host: g.host },
    tiles: makeDeck(),
    pool: [],
    poolCount: g.poolCount,
    board,
    players: g.seats.map((s, i) => ({
      name: s.name,
      type: s.type,
      photo: s.photo || null,
      rack: i === me.seat ? rack : {},
      count: i === me.seat ? undefined : g.counts[i],
      melded: g.melded[i],
      resigned: !!s.resigned,
    })),
    turn: g.turn,
    timer: g.timer,
    passes: g.passes,
    lastPlaced: g.lastPlaced || [],
    viewer: me.seat,
    over: g.status === "over" ? { winner: g.over?.winner ?? null } : null,
    settings: null,
  };
  S.turnStart = { board: clone(board), rack: S.turn === me.seat ? clone(rack) : {} };
  S.history = [];
  S.turnDeadline = !S.over && S.timer ? Date.now() + S.timer * 1000 : null;
  busy = false;
  if (!same) buildChips();
  save();
  render({ animate: !!same, from, flip, stagger });
  if (faceDownTo !== null) flyFaceDown($("#pool").getBoundingClientRect(), chipRect(faceDownTo));
}

// Results of a finished online game, once everyone's racks can be read.
// hands[i] = tile ids left in seat i's rack.
function onlineResults(hands) {
  if (!S?.online || !S.over) return;
  const vals = hands.map((h) => h.reduce((a, id) => a + rackValue(tile(id)), 0));
  let winner = S.over.winner;
  if (winner === null) {
    // Blocked game: lowest rack among the players still in wins.
    const inGame = S.players.map((p, i) => i).filter((i) => !S.players[i].resigned);
    winner = inGame.reduce((a, b) => (vals[b] < vals[a] ? b : a));
  }
  const scores = vals.map((v) => -(v - vals[winner]));
  scores[winner] = -scores.reduce((a, b) => a + b, 0);
  S.over = { winner, vals, scores, left: hands.map((h) => h.length) };
  render({ animate: false });
  later(showResults, 500);
}

function resumeLocal(saved) {
  window.Online?.leaveView();
  localStorage.setItem(MODE_KEY, "local");
  gameToken++;
  cancelDrag();
  busy = false;
  thinking = null;
  for (const el of els.values()) el.remove();
  els.clear();
  S = saved;
  buildChips();
  if (S.over) {
    render({ animate: false });
    return showResults();
  }
  if (cur().type === "human") {
    covered = humanCount() > 1;
    S.turnDeadline = null;
    if (!covered) armTimer();
  }
  render({ animate: false });
  if (cur().type !== "human") later(runAI, 500);
}

// ---------------------------------------------------------------- rendering

const JOKER_SVG =
  '<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="10" fill="none" stroke="currentColor" stroke-width="2.2"/>' +
  '<circle cx="8.5" cy="10" r="1.6" fill="currentColor"/><circle cx="15.5" cy="10" r="1.6" fill="currentColor"/>' +
  '<path d="M7.3 14.3q4.7 4.4 9.4 0" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"/></svg>';

function makeTileEl(id) {
  const t = tile(id);
  const el = document.createElement("div");
  el.className = "tile";
  el.dataset.id = id;
  if (isJoker(t)) {
    el.classList.add("joker", id % 2 ? "c3" : "c0");
    el.innerHTML = `<div class="face">${JOKER_SVG}</div><div class="back"></div>`;
  } else {
    el.classList.add("c" + t.c);
    el.innerHTML = `<div class="face">${t.n}</div><div class="back"></div>`;
  }
  return el;
}

function computeLayout() {
  const v = viewerIndex();
  const rack = v >= 0 ? S.players[v].rack : {};
  const W = rackWrap.clientWidth - 16;
  if (landscapePhone.matches) {
    // Like the app: tiles about 1/7 of the screen height, ~10-14 per rack row.
    L.rh = Math.round(Math.max(40, Math.min(66, innerHeight / 7)));
    L.rw = Math.round(L.rh / 1.3);
    L.rackCols = Math.max(10, Math.min(14, Math.floor(W / L.rw)));
  } else {
    L.rackCols = Math.max(10, Math.min(20, Math.floor(W / 44)));
    L.rw = Math.floor(W / L.rackCols);
    L.rh = Math.round(L.rw * 1.3);
    if (L.rh > 66) { L.rh = 66; L.rw = Math.round(66 / 1.3); }
  }
  let max = -1;
  for (const id in rack) max = Math.max(max, rack[id]);
  L.rackRows = Math.max(RACK_MIN_ROWS, Math.ceil((max + 1) / L.rackCols));
  Object.assign(rackEl.style, { width: L.rackCols * L.rw + "px", height: L.rackRows * L.rh + "px" });
  rackEl.style.setProperty("--ch", L.rh + "px");

  // Table tiles are rack-sized and the grid fills the table area, with a free
  // row and column past the furthest tile so any set can be extended. Tiles
  // only shrink when that doesn't fit.
  const bw = boardWrap.clientWidth - 8;
  const bh = boardWrap.clientHeight - 8;
  let maxR = -1;
  let maxC = -1;
  for (const id in S.board) {
    maxR = Math.max(maxR, S.board[id][0]);
    maxC = Math.max(maxC, S.board[id][1]);
  }
  const target = Math.min(L.rw, Math.floor(bw / 10)); // at least 10 columns; longer runs make the table shrink to fit
  const needCols = Math.max(Math.floor(bw / target), maxC + 2);
  const needRows = Math.max(Math.floor(bh / (target * 1.3)), maxR + 2);
  L.cw = Math.max(18, Math.floor(Math.min(target, bw / needCols, bh / needRows / 1.3)));
  L.ch = Math.round(L.cw * 1.3);
  L.cols = Math.max(needCols, Math.floor(bw / L.cw));
  L.rows = Math.max(needRows, Math.floor(bh / L.ch));
  Object.assign(boardEl.style, { width: L.cols * L.cw + "px", height: L.rows * L.ch + "px" });
  boardEl.style.setProperty("--cw", L.cw + "px");
  boardEl.style.setProperty("--ch", L.ch + "px");
}

function tileRect(id) {
  const g = ghosts.get(id);
  if (g) return g.getBoundingClientRect();
  const el = els.get(id);
  return el && el.isConnected ? el.getBoundingClientRect() : null;
}

// Re-renders everything. Tiles that moved fly from where they were (FLIP).
// opts.from: Map id -> DOMRect to fly from; opts.flip: ids that flip face up;
// opts.stagger: Map id -> delay ms; opts.animate=false to jump.
function render(opts = {}) {
  if (!S) return;
  const animate = opts.animate !== false;
  const first = new Map();
  if (animate) for (const id of els.keys()) { const r = tileRect(id); if (r) first.set(id, r); }
  if (opts.from) for (const [id, r] of opts.from) first.set(id, r);

  computeLayout();
  document.body.classList.toggle("covered", covered);
  const v = viewerIndex();
  const rack = v >= 0 ? S.players[v].rack : {};
  const myTurn = !S.over && cur().type === "human";
  const fresh = myTurn ? S.turnStart.rack : {};
  const recent = new Set(S.lastPlaced);
  const invalid = new Set();
  for (const s of getSets(S.board)) if (!setInfo(s.ids).valid) s.ids.forEach((id) => invalid.add(id));

  const want = new Set();
  const place = (id, parent, x, y, w, h) => {
    want.add(id);
    let el = els.get(id);
    if (!el) els.set(id, (el = makeTileEl(id)));
    if (drag && drag.active && drag.ids.includes(id)) return;
    if (el.parentNode !== parent) parent.appendChild(el);
    Object.assign(el.style, { left: x + "px", top: y + "px", width: w + "px", height: h + "px", fontSize: w * 0.5 + "px" });
    el.classList.toggle("fresh", id in fresh && id in S.board);
    el.classList.toggle("recent", recent.has(id) && !(id in fresh));
    el.classList.toggle("invalid", invalid.has(id));
    el.classList.toggle("locked", !canDrag(id));
  };
  for (const id of keys(S.board)) {
    const [r, c] = S.board[id];
    place(id, boardEl, c * L.cw, r * L.ch, L.cw, L.ch);
  }
  for (const id of keys(rack)) {
    const slot = rack[id];
    place(id, rackEl, (slot % L.rackCols) * L.rw, Math.floor(slot / L.rackCols) * L.rh, L.rw, L.rh);
  }
  for (const [id, el] of els) {
    if (want.has(id) || (drag && drag.active && drag.ids.includes(id))) continue;
    el.remove();
    els.delete(id);
  }

  if (animate) {
    for (const id of want) {
      const f = first.get(id);
      if (!f || (drag && drag.active && drag.ids.includes(id))) continue;
      fly(id, f, opts.flip?.has(id), opts.stagger?.get(id) || 0);
    }
  }
  renderHUD();
  const showCover = covered && !S.over;
  $("#cover").hidden = !showCover;
  if (showCover) $("#cover-title").textContent = `${cur().name}'s turn`;
}

// Animates a copy of the tile from rect f to the tile's real position. The
// copy lives in a fixed layer so it isn't clipped by the scrolling table.
function fly(id, f, flip, delay) {
  const el = els.get(id);
  const l = el.getBoundingClientRect();
  const dx = f.left + f.width / 2 - (l.left + l.width / 2);
  const dy = f.top + f.height / 2 - (l.top + l.height / 2);
  const sx = f.width / l.width;
  const sy = f.height / l.height;
  const old = ghosts.get(id);
  if (old) { old.remove(); ghosts.delete(id); }
  if (!flip && Math.abs(dx) < 0.5 && Math.abs(dy) < 0.5 && Math.abs(sx - 1) < 0.01) {
    el.style.visibility = "";
    return;
  }
  const g = el.cloneNode(true);
  g.classList.add("ghost");
  Object.assign(g.style, { left: l.left + "px", top: l.top + "px", width: l.width + "px", height: l.height + "px", visibility: "" });
  dragLayer.appendChild(g);
  ghosts.set(id, g);
  el.style.visibility = "hidden";
  const from = `perspective(900px) translate(${dx}px, ${dy}px) scale(${sx}, ${sy}) rotateY(${flip ? 180 : 0}deg)`;
  const to = "perspective(900px) translate(0px, 0px) scale(1, 1) rotateY(0deg)";
  const frames = flip
    ? [{ transform: from }, { transform: `perspective(900px) translate(${dx * 0.35}px, ${dy * 0.35 - 30}px) scale(1.25, 1.25) rotateY(90deg)`, offset: 0.55 }, { transform: to }]
    : [{ transform: from }, { transform: to }];
  const anim = g.animate(frames, { duration: flip ? DRAW_MS : ANIM_MS, delay, easing: "cubic-bezier(.25,.75,.25,1)", fill: "backwards" });
  anim.onfinish = anim.oncancel = () => {
    g.remove();
    if (ghosts.get(id) === g) {
      ghosts.delete(id);
      el.style.visibility = "";
    }
  };
}

// A face-down tile flying from the pool to an opponent.
function flyFaceDown(f, l) {
  const g = document.createElement("div");
  g.className = "tile facedown";
  g.innerHTML = '<div class="face"></div><div class="back"></div>';
  const w = 26;
  const h = 34;
  Object.assign(g.style, { left: l.left + l.width / 2 - w / 2 + "px", top: l.top + l.height / 2 - h / 2 + "px", width: w + "px", height: h + "px" });
  dragLayer.appendChild(g);
  const dx = f.left + f.width / 2 - (l.left + l.width / 2);
  const dy = f.top + f.height / 2 - (l.top + l.height / 2);
  g.animate(
    [{ transform: `translate(${dx}px, ${dy}px)`, opacity: 1 }, { transform: `translate(${dx / 2}px, ${dy / 2 + 30}px) scale(1.3)`, opacity: 1 }, { transform: "scale(.5)", opacity: 0 }],
    { duration: DRAW_MS, easing: "ease-in-out" },
  ).onfinish = () => g.remove();
}

function chipRect(pi) {
  const chip = document.querySelectorAll("#players .chip")[pi];
  const r = chip.querySelector(".avatar").getBoundingClientRect();
  return new DOMRect(r.left, r.top, r.width, r.width * 1.3);
}

function buildChips() {
  const box = $("#players");
  box.innerHTML = "";
  S.players.forEach((p, i) => {
    const chip = document.createElement("div");
    chip.className = "chip";
    chip.innerHTML = `<div class="avatar"><span></span></div><div class="chip-text"><span class="chip-name"></span><span class="chip-sub"></span></div>`;
    const span = chip.querySelector(".avatar span");
    span.style.setProperty("--av", AVATAR_COLOURS[i % 4]);
    span.textContent = (p.name.trim()[0] || "?").toUpperCase();
    if (p.photo) {
      const img = document.createElement("img");
      img.referrerPolicy = "no-referrer";
      img.alt = "";
      img.src = p.photo;
      img.onerror = () => img.remove();
      span.appendChild(img);
    }
    chip.querySelector(".chip-name").textContent = p.name;
    chip.title = p.type === "human" ? p.name : `${p.name} (computer, ${p.type})`;
    box.appendChild(chip);
  });
}

function renderHUD() {
  const chips = document.querySelectorAll("#players .chip");
  S.players.forEach((p, i) => {
    const chip = chips[i];
    if (!chip) return;
    chip.classList.toggle("active", i === S.turn && !S.over);
    const sub = chip.querySelector(".chip-sub");
    const n = rackCount(p);
    sub.textContent = p.resigned ? "Resigned" : `${n} tile${n === 1 ? "" : "s"}${p.type === "human" ? "" : " · AI"}`;
    chip.classList.toggle("out", !!p.resigned);
    sub.classList.toggle("dots", thinking === i || (!!S.online && i === S.turn && !S.over && p.type !== "human"));
  });
  $("#pool-count").textContent = poolLeft();
  const mine = isHumanTurn();
  const v = viewerIndex();
  $("#undo").disabled = !mine || !S.history.length;
  $("#reset").disabled = !mine || !turnChanged();
  $("#sort-num").disabled = $("#sort-run").disabled = v < 0 || covered;
  const main = $("#main-btn");
  const placed = mine && placedThisTurn().length > 0;
  main.disabled = !mine;
  main.classList.toggle("done", placed);
  main.classList.toggle("pulse", placed && !validateTurn().err);
  main.title = placed ? "Finish turn" : poolLeft() ? "Draw a tile and end your turn" : "Pass";
  main.innerHTML = placed ? "✓" : poolLeft() ? '<span class="main-draw">+<i></i></span>' : "Pass";
  renderStatus();
  tick();
}

function renderStatus() {
  let text = "";
  if (S.over) text = S.over.winner === null ? "Game over" : `${S.players[S.over.winner].name} won!`;
  else if (cur().type !== "human") text = `${cur().name} is thinking…`;
  else if (busy && S.online) text = "Sending…";
  else if (isHumanTurn() && !cur().melded) text = `First meld: ${meldPoints()} / ${FIRST_MELD}`;
  else if (isHumanTurn()) text = humanCount() > 1 && !S.online ? `${cur().name}'s turn` : "Your turn";
  else if (S.online) text = `${cur().name}'s turn`;
  $("#status").textContent = text;
}

function tick() {
  if (!S) return;
  const chips = document.querySelectorAll("#players .avatar");
  chips.forEach((a, i) => {
    let p = 0;
    if (i === S.turn && S.turnDeadline && !S.over) {
      const left = S.turnDeadline - Date.now();
      p = Math.max(0, left / (S.timer * 1000));
      a.classList.toggle("low", left < 10000);
    } else a.classList.remove("low");
    a.style.setProperty("--p", p);
  });
  if (S.turnDeadline && Date.now() >= S.turnDeadline && isHumanTurn()) {
    S.turnDeadline = null;
    onTimeout();
  }
  // Online: if another player's time ran out a while ago (they've probably
  // closed the app), skip their turn so the game can carry on.
  if (S.online && !S.over && S.turnDeadline && cur().type === "human" && !myTurn() && !S.online.skipping && Date.now() >= S.turnDeadline + SKIP_GRACE_MS) {
    S.online.skipping = true;
    toast(`${cur().name} isn't responding. Skipping their turn.`);
    Online.skip(S.online.moveNo).catch((e) => console.warn(e));
  }
}

function shakeInvalid() {
  for (const s of getSets(S.board)) {
    if (setInfo(s.ids).valid) continue;
    for (const id of s.ids) {
      const el = els.get(id);
      el.classList.remove("shake");
      void el.offsetWidth;
      el.classList.add("shake");
    }
  }
}

let toastTimer = null;
function toast(msg) {
  if (!msg) return;
  const t = $("#toast");
  t.textContent = msg;
  t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { t.hidden = true; }, 2600);
}

// ---------------------------------------------------------------- dragging

const hint = document.createElement("div");
hint.className = "hint";

function dropTarget(x, y) {
  const inside = (r) => x >= r.left && x <= r.right && y >= r.top && y <= r.bottom;
  if (inside(boardWrap.getBoundingClientRect())) {
    const g = boardEl.getBoundingClientRect();
    const c = Math.floor((x - g.left) / L.cw);
    const r = Math.floor((y - g.top) / L.ch);
    if (c < 0 || r < 0 || c >= L.cols || r >= L.rows) return null;
    return { area: "board", r, c };
  }
  if (inside(rackWrap.getBoundingClientRect()) || inside($("#controls").getBoundingClientRect())) {
    const g = rackEl.getBoundingClientRect();
    const c = Math.max(0, Math.min(L.rackCols - 1, Math.floor((x - g.left) / L.rw)));
    const r = Math.max(0, Math.min(L.rackRows - 1, Math.floor((y - g.top) / L.rh)));
    return { area: "rack", slot: r * L.rackCols + c };
  }
  return null;
}

function showHint(dest) {
  if (!dest) { hint.remove(); return; }
  const board = dest.area === "board";
  const n = drag ? drag.ids.length : 1;
  const [parent, w, h] = board ? [boardEl, L.cw, L.ch] : [rackEl, L.rw, L.rh];
  let [x, y] = board ? [dest.c * w, dest.r * h] : [(dest.slot % L.rackCols) * w, Math.floor(dest.slot / L.rackCols) * h];
  if (board && n > 1) x = Math.max(0, Math.min(dest.c - drag.idx, L.cols - n)) * w;
  if (hint.parentNode !== parent) parent.appendChild(hint);
  Object.assign(hint.style, { left: x + 1 + "px", top: y + 1 + "px", width: (board ? n : 1) * w - 2 + "px", height: h - 2 + "px" });
}

const LONG_PRESS_MS = 380;

function onPointerDown(e) {
  if (drag || e.button > 0) return;
  const el = e.target.closest(".tile");
  if (!el || el.parentNode === dragLayer) return;
  const id = Number(el.dataset.id);
  if (!canDrag(id)) {
    if (isHumanTurn() && id in S.board && !cur().melded)
      toast(`You can rearrange the table after your first meld (${FIRST_MELD}+ points).`);
    return;
  }
  e.preventDefault();
  const r = el.getBoundingClientRect();
  drag = { id, ids: [id], idx: 0, pointerId: e.pointerId, x0: e.clientX, y0: e.clientY, x: e.clientX, y: e.clientY, fx: (e.clientX - r.left) / r.width, fy: (e.clientY - r.top) / r.height, active: false };
  // Holding still on a table tile picks up its whole set.
  if (id in S.board) {
    const set = getSets(S.board).find((s) => s.ids.includes(id));
    if (set.ids.length > 1 && set.ids.every(canDrag)) {
      const d = drag;
      d.timer = setTimeout(() => {
        if (drag !== d || d.active) return;
        d.ids = set.ids;
        d.idx = set.ids.indexOf(id);
        navigator.vibrate?.(15);
        activateDrag();
        moveDrag();
      }, LONG_PRESS_MS);
    }
  }
}

function activateDrag() {
  clearTimeout(drag.timer);
  drag.active = true;
  drag.els = drag.ids.map((id) => {
    const g = ghosts.get(id);
    if (g) { g.remove(); ghosts.delete(id); }
    const el = els.get(id);
    el.style.visibility = "";
    dragLayer.appendChild(el);
    el.classList.add("dragging");
    return el;
  });
}

function onPointerMove(e) {
  if (!drag || e.pointerId !== drag.pointerId) return;
  drag.x = e.clientX;
  drag.y = e.clientY;
  if (!drag.active) {
    if (Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) < 5) return;
    activateDrag();
  }
  moveDrag();
}

// Positions the dragged tile(s) under the finger. For a set, the drop target
// is the cell under the tile that was grabbed.
function moveDrag() {
  const br = boardWrap.getBoundingClientRect();
  const overBoard = drag.x >= br.left && drag.x <= br.right && drag.y >= br.top && drag.y <= br.bottom;
  const [w, h] = overBoard ? [L.cw, L.ch] : [L.rw, L.rh];
  const x = drag.x - drag.fx * w;
  const y = drag.y - drag.fy * h;
  drag.els.forEach((el, i) => {
    Object.assign(el.style, { left: x + (i - drag.idx) * w + "px", top: y + "px", width: w + "px", height: h + "px", fontSize: w * 0.5 + "px" });
  });
  drag.dest = dropTarget(x + w / 2, y + h / 2);
  showHint(drag.dest);
}

function onPointerUp(e) {
  if (!drag || e.pointerId !== drag.pointerId) return;
  finishDrag(e.type === "pointerup");
}

function finishDrag(drop) {
  const d = drag;
  drag = null;
  clearTimeout(d.timer);
  hint.remove();
  if (!d.active) return;
  const from = new Map();
  d.els.forEach((el, i) => {
    el.classList.remove("dragging");
    from.set(d.ids[i], el.getBoundingClientRect());
  });
  if (drop && d.dest && S) d.ids.length > 1 ? tryMoveSet(d.ids, d.idx, d.dest) : tryMove(d.id, d.dest);
  if (S) render({ from });
  else d.els.forEach((el) => el.remove());
}

function cancelDrag() {
  if (drag) finishDrag(false);
}

// ---------------------------------------------------------------- games page

const gamesPage = $("#games-page");
const pageOpen = () => !gamesPage.hidden;

// The full-screen list of games (this device's game and online games).
function openHome() {
  for (const d of ["#results", "#room"]) if ($(d).open) $(d).close();
  cancelDrag();
  gamesPage.hidden = false;
  $("#page-back").hidden = !S;
  renderLocalGames();
  window.Online?.pageOpened();
}

function closeHome() {
  if (gamesPage.hidden) return;
  gamesPage.hidden = true;
  window.Online?.pageClosed();
}

function row(label, sub, buttons, cls = "") {
  const li = document.createElement("li");
  li.className = "game-row " + cls;
  li.innerHTML = '<div><b></b><small></small></div><div class="btns"></div>';
  li.querySelector("b").textContent = label;
  li.querySelector("small").textContent = sub;
  for (const [text, fn, kind] of buttons) {
    const b = document.createElement("button");
    b.type = "button";
    b.textContent = text;
    if (kind) b.className = kind;
    b.onclick = fn;
    li.querySelector(".btns").appendChild(b);
  }
  return li;
}

function renderLocalGames() {
  const ul = $("#local-games");
  ul.innerHTML = "";
  const g = S && !S.online ? S : loadLocalGame();
  const showing = !!S && !S.online;
  if (g && !g.over) {
    const who = g.players[g.turn];
    const sub = who.type === "human" ? `${who.name}'s turn` : `${who.name} is playing`;
    ul.appendChild(row(g.players.map((p) => p.name).join(" vs "), sub, [
      ["New", () => openSetup()],
      ["Open", () => (showing ? closeHome() : (closeHome(), resumeLocal(g))), "primary"],
    ], showing ? "current" : ""));
  } else {
    ul.appendChild(row("Play against the computer", "Or pass the phone around", [["New game", () => openSetup(), "primary"]]));
  }
}

// ---------------------------------------------------------------- dialogs

function openSetup() {
  const settings = loadSettings();
  const box = $("#setup-players");
  box.innerHTML = "";
  for (const p of settings.players) addPlayerRow(p);
  $("#setup-timer").value = String(settings.timer);
  $("#setup-cancel").hidden = !S || !!S.over;
  updateSetupButtons();
  $("#setup").showModal();
}

function addPlayerRow(p) {
  const row = document.createElement("div");
  row.className = "prow";
  row.innerHTML = `<input maxlength="14" placeholder="Name"><select>
    <option value="human">Human</option><option value="easy">Computer (easy)</option><option value="hard">Computer (hard)</option>
  </select><button type="button" class="rm" aria-label="Remove">×</button>`;
  row.querySelector("input").value = p.name;
  row.querySelector("select").value = p.type;
  row.querySelector(".rm").onclick = () => { row.remove(); updateSetupButtons(); };
  $("#setup-players").appendChild(row);
}

function updateSetupButtons() {
  const n = $("#setup-players").children.length;
  $("#add-player").hidden = n >= 4;
  for (const b of document.querySelectorAll("#setup-players .rm")) b.style.visibility = n > 2 ? "" : "hidden";
}

function readSetup() {
  const players = [...document.querySelectorAll("#setup-players .prow")].map((row, i) => {
    const type = row.querySelector("select").value;
    const name = row.querySelector("input").value.trim() || (type === "human" ? `Player ${i + 1}` : `Computer ${i + 1}`);
    return { name, type };
  });
  return { players, timer: Number($("#setup-timer").value) };
}

function showResults() {
  const o = S.over;
  if (!o.vals) return; // online: waiting for everyone's racks (onlineResults)
  $("#results-title").textContent = `${S.players[o.winner].name} won!`;
  const order = S.players.map((p, i) => i).sort((a, b) => o.scores[b] - o.scores[a]);
  $("#results-table").innerHTML = "";
  for (const i of order) {
    const tr = document.createElement("tr");
    if (i === o.winner) tr.className = "win";
    const left = o.left ? o.left[i] : keys(S.players[i].rack).length;
    tr.innerHTML = `<td></td><td>${left} tile${left === 1 ? "" : "s"} left (${o.vals[i]})</td><td>${o.scores[i] > 0 ? "+" : ""}${o.scores[i]}</td>`;
    tr.firstChild.textContent = S.players[i].name + (S.players[i].resigned ? " (resigned)" : "");
    $("#results-table").appendChild(tr);
  }
  $("#results-again").hidden = !!S.online;
  $("#results-new").textContent = S.online ? "All games" : "New game…";
  if (!$("#results").open) $("#results").showModal();
}

// ---------------------------------------------------------------- wiring

function init() {
  startWorker();
  document.addEventListener("pointerdown", onPointerDown);
  window.addEventListener("pointermove", onPointerMove);
  window.addEventListener("pointerup", onPointerUp);
  window.addEventListener("pointercancel", onPointerUp);
  window.addEventListener("resize", () => render({ animate: false }));
  document.addEventListener("contextmenu", (e) => e.target.closest(".tile") && e.preventDefault());

  $("#main-btn").onclick = onMain;
  $("#undo").onclick = undo;
  $("#reset").onclick = resetTurn;
  $("#sort-num").onclick = () => sortRack("num");
  $("#sort-run").onclick = () => sortRack("run");
  $("#menu-btn").onclick = openHome;
  $("#page-back").onclick = closeHome;
  $("#add-player").onclick = () => { addPlayerRow({ name: "", type: "hard" }); updateSetupButtons(); };
  $("#setup-cancel").onclick = () => $("#setup").close();
  $("#setup-form").onsubmit = () => newGame(readSetup());
  $("#results-again").onclick = () => { $("#results").close(); newGame(S.settings); };
  $("#results-new").onclick = () => {
    $("#results").close();
    if (S.online) openHome();
    else openSetup();
  };
  $("#cover-btn").onclick = () => {
    covered = false;
    armTimer();
    save();
    render();
  };
  setInterval(tick, 250);

  // An online game is reopened by online.js once sign-in has loaded.
  if (localStorage.getItem(MODE_KEY) === "online") return;
  const saved = loadLocalGame();
  if (saved) resumeLocal(saved);
  else openHome();
}

// ---------------------------------------------------------------- version check
// VERSION (version.js) is the copy that's running; version.js fetched with no-store is
// what GitHub Pages serves now. Pages lets browsers cache files for 10 min, so a stale
// copy is common right after a deploy. The game is saved after every move, so updating
// (which reloads the page) carries on where you left off.

const APP_FILES = ["./", "index.html", "app.js", "online.js", "ai.js", "rules.js", "version.js", "style.css", "manifest.webmanifest", "icon.svg"];
const VERSION_CHECK_MS = 5 * 60_000;
const versionBtn = $("#version");
let latestVersion = null;

function formatVersion(v) {
  const d = new Date(v);
  return Number.isNaN(d.getTime()) ? v : d.toLocaleString(undefined, { day: "numeric", month: "short", hour: "numeric", minute: "2-digit" });
}

function setVersionState(state) {
  const labels = {
    checking: "Checking for updates…",
    ok: `Up to date (version ${formatVersion(VERSION)})`,
    stale: `Update available: running ${formatVersion(VERSION)}, latest is ${formatVersion(latestVersion)}. Tap to update.`,
    unknown: `Couldn't check for updates (offline?). Running ${formatVersion(VERSION)}.`,
    updating: "Updating…",
  };
  versionBtn.dataset.state = state;
  versionBtn.title = labels[state];
  versionBtn.setAttribute("aria-label", labels[state]);
  versionBtn.querySelector("span").textContent = state === "stale" ? "Update" : "";
}

async function checkVersion() {
  if (versionBtn.dataset.state === "updating") return;
  try {
    const res = await fetch(`version.js?t=${Date.now()}`, { cache: "no-store" });
    if (!res.ok) throw new Error(res.status);
    latestVersion = (await res.text()).match(/VERSION = "([^"]+)"/)?.[1];
    if (!latestVersion) throw new Error("no version");
    // ISO timestamps compare as strings; only a newer live copy counts as an update.
    setVersionState(latestVersion > VERSION ? "stale" : "ok");
  } catch {
    setVersionState("unknown");
  }
}

versionBtn.addEventListener("click", async () => {
  const state = versionBtn.dataset.state;
  if (state !== "stale") {
    toast(versionBtn.title);
    if (state === "unknown") checkVersion();
    return;
  }
  setVersionState("updating");
  cancelDrag();
  if (S) save();
  // Refresh every file in the HTTP cache first; a plain reload could still use the stale copies.
  await Promise.all(APP_FILES.map((f) => fetch(f, { cache: "reload" }).catch(() => {})));
  location.reload();
});

setVersionState("checking");
checkVersion();
setInterval(checkVersion, VERSION_CHECK_MS);
document.addEventListener("visibilitychange", () => { if (!document.hidden) checkVersion(); });
window.addEventListener("online", checkVersion);

init();
