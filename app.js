"use strict";
// Rummikub: table, rack, drag and drop, turns, computer players.
//
// Screens: the Games screen (no URL hash) and a game (#local=<id> or
// #online=<id>); route() switches between them, so the phone's back button
// returns to Games. Only the game on screen is loaded into S.
//
// Games on this device are kept in localStorage as "rummikub:g:<id>" (any
// number of them) and, when signed in, synced through Firestore by online.js
// (window.Cloud). Each has S.id and S.updated (ms, last change wins).
//
// State S (saved after every change):
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

const OLD_SAVE_KEY = "rummikub:game"; // the single saved game before multiple games
const GAME_PREFIX = "rummikub:g:";
const TOMBSTONES_KEY = "rummikub:deleted"; // {id: ms} games removed on this device
const FINISHED_KEEP_MS = 3 * 24 * 3600_000; // finished games stay listed this long
const SETTINGS_KEY = "rummikub:settings";
const RACK_MIN_ROWS = 2;
const ANIM_MS = 320;
const DRAW_MS = 650;
// Computer-turn pacing (ms). Its moves take ~1 ms to work out; the pauses are
// only so you can follow what it did. Animations keep their full length and
// finish during the next turn. "Fast mode" in Settings drops the pauses.
const PREFS_KEY = "rummikub:prefs";
const PACE = {
  normal: { start: 100, think: 250, after: 100, stagger: 275 },
  fast: { start: 0, think: 0, after: 0, stagger: 275 },
};
let prefs = { fast: false, pickup: "hold", move: "drag" }; // pickup: "hold" or "doubletap"; move: "drag" or "tap"
try { prefs = { ...prefs, ...JSON.parse(localStorage.getItem(PREFS_KEY)) }; } catch { /* defaults */ }
const pace = () => PACE[prefs.fast ? "fast" : "normal"];
function setPref(k, v) {
  prefs[k] = v;
  localStorage.setItem(PREFS_KEY, JSON.stringify(prefs));
}
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
// Smallest table grid, the same on every device (see computeLayout). Sized so
// tiles stay large on a portrait phone (width-limited) and a landscape phone
// (height-limited).
const BOARD_COLS = 12;
const BOARD_ROWS = 6;
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
  if (!S) return;
  try {
    // Online, only how this device arranged its rack is kept locally.
    if (S.online) return localStorage.setItem(rackKey(), JSON.stringify(S.players[S.online.seat].rack));
    S.updated = Date.now();
    Store.put(S);
    window.Cloud?.queue(S.id);
  } catch { /* storage full or blocked */ }
}

const rackKey = () => `rummikub:rack:${S.online.id}:${S.online.uid}`;

// Games on this device. The tile list is the same in every game (makeDeck),
// so it isn't stored.
const Store = {
  pack: (g) => JSON.stringify({ ...g, tiles: undefined }),
  unpack(text) {
    const g = JSON.parse(text);
    if (!g || g.v !== 1) return null;
    g.tiles = makeDeck();
    return g;
  },
  get(id) {
    try { return Store.unpack(localStorage.getItem(GAME_PREFIX + id)); } catch { return null; }
  },
  put(g) { localStorage.setItem(GAME_PREFIX + g.id, Store.pack(g)); },
  remove(id) {
    localStorage.removeItem(GAME_PREFIX + id);
    const t = Store.tombstones();
    t[id] = Date.now();
    localStorage.setItem(TOMBSTONES_KEY, JSON.stringify(t));
  },
  tombstones() {
    try { return JSON.parse(localStorage.getItem(TOMBSTONES_KEY)) || {}; } catch { return {}; }
  },
  ids() {
    const out = [];
    for (let i = 0; i < localStorage.length; i++) {
      const k = localStorage.key(i);
      if (k.startsWith(GAME_PREFIX)) out.push(k.slice(GAME_PREFIX.length));
    }
    return out;
  },
  all: () => Store.ids().map(Store.get).filter(Boolean),
};

const newId = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);

// The one saved game from before multiple games becomes a game in the store.
function migrateOldSave() {
  try {
    const old = JSON.parse(localStorage.getItem(OLD_SAVE_KEY));
    if (old && old.v === 1) {
      old.id = newId();
      old.updated = old.created = Date.now();
      Store.put(old);
    }
  } catch { /* unreadable: drop it */ }
  localStorage.removeItem(OLD_SAVE_KEY);
  localStorage.removeItem("rummikub:mode");
  localStorage.removeItem("rummikub:onlineGame");
}

// Removes finished games older than FINISHED_KEEP_MS (and old tombstones).
function pruneGames() {
  const now = Date.now();
  for (const g of Store.all()) if (g.over && now - g.updated > FINISHED_KEEP_MS && g.id !== S?.id) Store.remove(g.id);
  const t = Store.tombstones();
  for (const id in t) if (now - t[id] > 30 * 24 * 3600_000) delete t[id];
  localStorage.setItem(TOMBSTONES_KEY, JSON.stringify(t));
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
  window.Online?.leaveView();
  const fromGame = !!S;
  gameToken++;
  busy = false;
  thinking = null;

  cancelDrag();
  const tiles = makeDeck();
  S = {
    v: 1,
    id: newId(),
    created: Date.now(),
    updated: Date.now(),
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
  save();
  showScreen("game", `#local=${S.id}`, { replace: fromGame });
  buildChips();
  startTurn();
}

// Whose rack is shown at the bottom.
function viewerIndex(st = S) {
  if (!st) return -1;
  if (st.online) return st.online.seat;
  if (st.players[st.turn].type === "human") return st.turn;
  return st.viewer ?? -1;
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

// Moves a group of tiles (a table set or neighbouring rack tiles) so the
// grabbed tile (index idx) lands at dest. On the table, sets it would overlap
// or touch move out of the way; in the rack, tiles shift along as usual.
function tryMoveSet(ids, idx, dest) {
  const v = viewerIndex();
  const rack = S.players[v].rack;
  if (dest.area === "board" && !isHumanTurn()) {
    toast(covered || busy ? "" : "Wait for your turn.");
    return false;
  }
  if (dest.area === "rack" && !ids.every((t) => t in rack || t in S.turnStart.rack)) {
    toast("Tiles from the table can't go into your rack.");
    return false;
  }
  const before = snapshot();
  for (const t of ids) {
    delete rack[t];
    delete S.board[t];
  }
  if (dest.area === "rack") {
    const start = Math.max(0, dest.slot - idx);
    ids.forEach((t, k) => placeInRack(rack, t, start + k));
  } else {
    const n = ids.length;
    const r = dest.r;
    const c = Math.max(0, Math.min(dest.c - idx, L.cols - n));
    const blockers = getSets(S.board).filter((s) => s.r === r && s.c <= c + n && s.c + s.ids.length >= c);
    for (const s of blockers) for (const t of s.ids) delete S.board[t];
    ids.forEach((t, i) => { S.board[t] = [r, c + i]; });
    for (const s of blockers) moveSetNear(s.ids, r, s.c);
  }
  if (isHumanTurn()) S.history.push(before);
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
  // Sets ready to play come first (777: groups, 789: runs), each with a gap
  // on both sides and never split across two rows; the leftover tiles follow,
  // packed together and sorted as before. The rack grows a row if needed.
  const ready = mode === "num" ? readyGroups(list) : readyRuns(list);
  const inReady = new Set(ready.flat().map((t) => t.id));
  const cols = L.rackCols;
  if (isHumanTurn()) S.history.push(snapshot());
  let slot = 0;
  for (const set of ready) {
    const col = slot % cols;
    if (col !== 0 && col + set.length > cols) slot += cols - col; // start it on the next row
    for (const t of set) rack[t.id] = slot++;
    if (slot % cols !== 0) slot++; // gap after it (none needed at the end of a row)
  }
  for (const t of list) if (!inReady.has(t.id)) rack[t.id] = slot++;
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
  selection = null;
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
  if (p.type !== "human") later(runAI, pace().start);
}

// No timer when only one person is playing (the rest are computers).
const timed = () => !!S.timer && humanCount() > 1;

function armTimer() {
  S.turnDeadline = timed() ? Date.now() + S.timer * 1000 : null;
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
  later(endTurn, pace().after); // the drawn tile finishes flying in during the next turn
}

function endTurn() {
  if (!keys(cur().rack).length) return gameOver(S.turn);
  if (S.passes >= S.players.filter((p) => !p.resigned).length) return gameOver(null);
  S.turn = nextLocalSeat(S.turn);
  startTurn();
}

function nextLocalSeat(from) {
  let i = from;
  do i = (i + 1) % S.players.length; while (S.players[i].resigned && i !== from);
  return i;
}

// The question asked before resigning a local game `st` (S or a saved game).
function resignQuestion(st) {
  const pi = viewerIndex(st);
  const left = st.players.map((q, i) => i).filter((i) => i !== pi && !st.players[i].resigned);
  return left.length > 1 && left.some((i) => st.players[i].type === "human")
    ? `Resign, ${st.players[pi].name}? You'll be out and the others carry on.`
    : `Resign this game? ${left.length === 1 ? st.players[left[0]].name + " wins." : "The computer with the fewest tiles wins."}`;
}

// Resign on this device: the player whose rack is showing is out. The game
// ends if nobody (or only computers) would be left to play.
// `asked`: the Games screen already confirmed before opening the game.
function resignLocal({ asked = false } = {}) {
  const pi = viewerIndex();
  if (!S || S.online || S.over || pi < 0) return;
  const p = S.players[pi];
  const left = S.players.map((q, i) => i).filter((i) => i !== pi && !S.players[i].resigned);
  if (!asked && !confirm(resignQuestion(S))) return;
  cancelDrag();
  if (S.turn === pi) revertTurn();
  p.resigned = true;
  if (left.length === 1 || !left.some((i) => S.players[i].type === "human")) {
    const winner = left.reduce((a, b) => (keys(S.players[b].rack).length < keys(S.players[a].rack).length ? b : a));
    return gameOver(winner, true);
  }
  if (S.turn === pi) {
    gameToken++;
    S.turn = nextLocalSeat(pi);
    startTurn();
  } else {
    save();
    render();
  }
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

function gameOver(winner, quiet = false) {
  const vals = S.players.map((p) => keys(p.rack).reduce((a, id) => a + rackValue(tile(id)), 0));
  if (winner === null) {
    const inGame = S.players.map((p, i) => i).filter((i) => !S.players[i].resigned);
    winner = inGame.reduce((a, b) => (vals[b] < vals[a] ? b : a));
  }
  S.over = { winner, vals, scores: scoresFor(vals, winner), quiet };
  S.turnDeadline = null;
  busy = false;
  save();
  render();
  if (quiet) goLobby();
  else later(showResults, 500);
}

// Rummikub scoring: each loser loses their rack total; the winner gains the sum.
function scoresFor(vals, winner) {
  const scores = vals.map((v, i) => (i === winner ? 0 : -v));
  scores[winner] = -scores.reduce((a, b) => a + b, 0);
  return scores;
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
  later(() => S.turn === pi && !S.over && applyAI(pi, result), Math.max(0, pace().think - (performance.now() - t0)));
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
    later(endTurn, pace().after);
    return;
  }
  const from = new Map();
  const stagger = new Map();
  res.placed.forEach((id, i) => {
    from.set(id, chip);
    stagger.set(id, i * pace().stagger);
    delete p.rack[id];
  });
  S.board = layoutSets(res.sets, S.board);
  p.melded = true;
  S.lastPlaced = res.placed;
  S.passes = 0;
  save();
  render({ from, flip: new Set(res.placed), stagger });
  later(endTurn, pace().after + res.placed.length * pace().stagger);
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
  // New sets go in the free spot closest to a point a little below the middle
  // of the table, so they land near the rack instead of at the far top edge.
  const ty = Math.min(rows, L.rows - 1) * 0.6;
  const tx = cols / 2;
  for (const it of rest) {
    const len = it.ids.length;
    let best = null;
    for (let r = 0; r < rows; r++)
      for (let c = 0; c + len <= cols; c++) {
        if (!fits(r, c, len)) continue;
        const d = Math.hypot((r + 0.5 - ty) * 1.3, c + len / 2 - tx);
        if (!best || d < best.d) best = { r, c, d };
      }
    if (!best) return null;
    put(best.r, best.c, it.ids);
  }
  return out;
}

// ---------------------------------------------------------------- online games

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
        stagger.set(t, i++ * pace().stagger);
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
  S.turnDeadline = !S.over && timed() ? Date.now() + S.timer * 1000 : null;
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
  const quiet = !!S.players[S.online.seat].resigned; // you resigned: no results box
  S.over = { winner, vals, scores: scoresFor(vals, winner), left: hands.map((h) => h.length), quiet };
  render({ animate: false });
  if (quiet) goLobby();
  else later(showResults, 500);
}

// Shows a game from the store. Also used when a newer copy arrives from
// another device for the game on screen.
function resumeLocal(saved) {
  window.Online?.leaveView();
  gameToken++;
  cancelDrag();
  busy = false;
  thinking = null;
  for (const el of els.values()) el.remove();
  els.clear();
  S = saved;
  if ($("#results").open) $("#results").close();
  buildChips();
  if (S.over) {
    render({ animate: false });
    // A resigned game shows its final table without the results box.
    return S.over.quiet ? undefined : showResults();
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

  // Table tiles are rack-sized where they fit. The grid is the same size on
  // every device (BOARD_COLS x BOARD_ROWS) so a table laid out on a laptop
  // also fits a phone, portrait or landscape. It only grows past that to keep
  // a free row and column past the furthest tile (so any set can be
  // extended), and tiles shrink when the bigger grid doesn't fit.
  const bw = boardWrap.clientWidth - 8;
  const bh = boardWrap.clientHeight - 8;
  let maxR = -1;
  let maxC = -1;
  for (const id in S.board) {
    maxR = Math.max(maxR, S.board[id][0]);
    maxC = Math.max(maxC, S.board[id][1]);
  }
  L.cols = Math.max(BOARD_COLS, maxC + 2);
  L.rows = Math.max(BOARD_ROWS, maxR + 2);
  L.cw = Math.max(18, Math.floor(Math.min(L.rw, bw / L.cols, bh / L.rows / 1.3)));
  L.ch = Math.round(L.cw * 1.3);
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
  if (!S || gameScreen.hidden) return;
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
    el.classList.toggle("selected", !!selection && selection.includes(id));
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
  const me = S.players[viewerIndex()];
  $("#resign-btn").hidden = !!S.over || covered || !me || me.type !== "human" || !!me.resigned;
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
  if (!board && n > 1) x = Math.max(0, dest.slot - drag.idx) % L.rackCols * w;
  if (hint.parentNode !== parent) parent.appendChild(hint);
  Object.assign(hint.style, { left: x + 1 + "px", top: y + 1 + "px", width: n * w - 2 + "px", height: h - 2 + "px" });
}

const LONG_PRESS_MS = 380;
// How far a finger can wobble while holding before it counts as a drag. A real
// thumb moves a few pixels, so touch needs more slack than a mouse.
const dragSlop = (e) => (e.pointerType === "mouse" ? 5 : 14);

// The tiles that move together with `id` on a long press (or double-tap):
// `id` plus the tiles to its right in the same row (on the table or in the
// rack), for as long as they could still be part of one meld with it (same
// number in different colours, or consecutive numbers in one colour; jokers
// fit either). Tiles to its left are never included.
function groupOf(id) {
  const onBoard = id in S.board;
  const next = new Map(); // tile id -> the tile directly to its right
  if (onBoard) {
    const occ = boardOcc();
    for (const t of keys(S.board)) {
      const [r, c] = S.board[t];
      const right = occ.get(r * 1000 + c + 1);
      if (right !== undefined) next.set(t, right);
    }
  } else {
    const rack = S.players[viewerIndex()].rack;
    const bySlot = new Map(keys(rack).map((t) => [rack[t], t]));
    for (const t of keys(rack)) {
      const s = rack[t];
      if ((s + 1) % L.rackCols !== 0 && bySlot.has(s + 1)) next.set(t, bySlot.get(s + 1));
    }
  }
  const ids = [id];
  for (let t = next.get(id); t !== undefined; t = next.get(t)) {
    if (!couldBeMeld([...ids, t].map(tile))) break;
    ids.push(t);
  }
  return ids;
}

// Whether these tiles, in this order, could be all or the start of a valid set.
function couldBeMeld(tiles) {
  const real = tiles.filter((t) => !isJoker(t));
  if (!real.length) return tiles.length <= 2;
  const group = tiles.length <= 4 && real.every((t) => t.n === real[0].n) && new Set(real.map((t) => t.c)).size === real.length;
  if (group) return true;
  if (!real.every((t) => t.c === real[0].c)) return false;
  const i0 = tiles.findIndex((t) => !isJoker(t));
  const s = tiles[i0].n - i0;
  return s >= 1 && s + tiles.length - 1 <= 13 && tiles.every((t, i) => isJoker(t) || t.n === s + i);
}

// "doubletap" setting: tapping a tile twice selects its set (outlined); then
// dragging any selected tile moves them all. Tapping anything else clears it.
const DOUBLE_TAP_MS = 350;
let lastTap = null; // {id, t}
let selection = null; // tile ids

function setSelection(ids) {
  selection = ids;
  for (const [id, el] of els) el.classList.toggle("selected", !!ids && ids.includes(id));
}

// "tap" setting (Moving tiles → Tap): tapping a tile picks it up (selects it);
// tapping it again adds the rest of its set (groupOf), and once more puts it
// down. Tapping an empty table cell or rack slot moves the selection there,
// first tile on the tapped spot. Dragging still works as usual. In this mode
// "Moving a whole set" is always Hold (a double-tap would clash).
const tapMode = () => prefs.move === "tap";
const pickupMode = () => (tapMode() ? "hold" : prefs.pickup);

function showPickupSetting() {
  for (const el of document.querySelectorAll(".pickup-setting")) el.hidden = tapMode();
}

function tapTile(id) {
  if (!selection?.includes(id)) return setSelection([id]);
  const group = groupOf(id);
  if (selection.length === 1 && group.length > 1 && group.every(canDrag)) {
    navigator.vibrate?.(15);
    return setSelection(group);
  }
  setSelection(null);
}

// A tap on the table or rack (not on a tile) while tiles are picked up.
function onTapPlace(e) {
  if (!tapMode() || !selection || !S || e.target.closest(".tile, button, dialog")) return;
  const ids = selection;
  const dest = dropTarget(e.clientX, e.clientY);
  setSelection(null);
  if (!dest || !ids.every(canDrag)) return render();
  ids.length > 1 ? tryMoveSet(ids, 0, dest) : tryMove(ids[0], dest);
  render();
}

function onPointerDown(e) {
  if (drag || e.button > 0) return;
  const el = e.target.closest(".tile");
  if (!el || el.parentNode === dragLayer) {
    // In tap mode the click that follows places the selection (onTapPlace).
    if (selection && !tapMode() && !e.target.closest("button")) setSelection(null);
    return;
  }
  const id = Number(el.dataset.id);
  if (!canDrag(id)) {
    if (isHumanTurn() && id in S.board && !cur().melded)
      toast(`You can rearrange the table after your first meld (${FIRST_MELD}+ points).`);
    return;
  }
  e.preventDefault();
  const r = el.getBoundingClientRect();
  drag = { id, ids: [id], idx: 0, pointerId: e.pointerId, slop: dragSlop(e), x0: e.clientX, y0: e.clientY, x: e.clientX, y: e.clientY, fx: (e.clientX - r.left) / r.width, fy: (e.clientY - r.top) / r.height, active: false };
  const group = groupOf(id);
  const groupOk = group.length > 1 && group.every(canDrag);
  if (tapMode() && selection?.includes(id) && selection.every(canDrag)) {
    // Dragging a picked-up tile carries everything picked up.
    drag.ids = selection;
    drag.idx = selection.indexOf(id);
  }
  if (pickupMode() === "doubletap") {
    if (selection?.includes(id) && selection.every(canDrag)) {
      drag.ids = selection;
      drag.idx = selection.indexOf(id);
    } else if (groupOk && lastTap?.id === id && performance.now() - lastTap.t < DOUBLE_TAP_MS) {
      lastTap = null;
      navigator.vibrate?.(15);
      setSelection(group);
      drag.ids = group;
      drag.idx = group.indexOf(id);
      drag.selecting = true; // this tap made the selection; don't count it as a first tap
    } else if (selection) setSelection(null);
    return;
  }
  // Holding still picks up the whole set (on the table or in the rack).
  if (groupOk && drag.ids.length === 1) {
    const d = drag;
    d.timer = setTimeout(() => {
      if (drag !== d || d.active) return;
      d.ids = group;
      d.idx = group.indexOf(id);
      navigator.vibrate?.(15);
      activateDrag();
      moveDrag();
    }, LONG_PRESS_MS);
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
    if (Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) < drag.slop) return;
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
  if (!d.active) {
    if (drop && tapMode()) return tapTile(d.id);
    // A tap: remember it so a second tap on the same tile selects its set.
    if (drop && !d.selecting) lastTap = { id: d.id, t: performance.now() };
    return;
  }
  setSelection(null);
  lastTap = null;
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

// ---------------------------------------------------------------- screens

const gamesPage = $("#games-page");
const gameScreen = $("#game-screen");
const pageOpen = () => !gamesPage.hidden;
const onGameScreen = () => !gameScreen.hidden;
let lastGameHash = null; // the game you just left; outlined in the Games list

// Changes the URL (unless it's already `hash`) and shows that screen.
// History entries let the phone's back button go from a game to Games.
function showScreen(name, hash, { replace = false } = {}) {
  const url = location.pathname + location.search + (hash || "");
  if ((location.hash || "") !== (hash || "")) {
    const st = { fromLobby: name === "game" && pageOpen() };
    if (replace) history.replaceState(st, "", url);
    else history.pushState(st, "", url);
  }
  const lobby = name === "lobby";
  if (lobby === pageOpen() && lobby !== onGameScreen()) return;
  $("#settings-page").hidden = true;
  gamesPage.hidden = !lobby;
  gameScreen.hidden = lobby;
  if (lobby) {
    renderLocalGames();
    // The new-game form starts closed, unless "New game" in a results box asked for it.
    $("#setup").hidden = true;
    if (setupOnLobby) openSetup();
    setupOnLobby = false;
    window.Online?.pageOpened();
  } else window.Online?.pageClosed();
}

// Back to the Games screen; the game that was showing stops (it's saved).
function goLobby({ replace = false } = {}) {
  if (S && location.hash) lastGameHash = location.hash;
  for (const d of ["#results", "#room"]) if ($(d).open) $(d).close();
  cancelDrag();
  setSelection(null);
  if (S && !S.online) save();
  window.Online?.leaveView();
  gameToken++;
  S = null;
  busy = false;
  thinking = null;
  covered = false;
  for (const el of els.values()) el.remove();
  els.clear();
  dragLayer.innerHTML = "";
  ghosts.clear();
  $("#cover").hidden = true;
  // Came here from the Games screen: step back instead of adding history.
  if (!replace && history.state?.fromLobby && location.hash) return history.back();
  showScreen("lobby", "", { replace });
}
const openHome = () => goLobby();

function openGame(kind, id) {
  showScreen("game", `#${kind}=${id}`);
  route();
}

// Shows whatever the URL says. Online games wait for sign-in (online.js
// calls route() again once it knows who's signed in).
function route() {
  const m = location.hash.match(/^#(local|online)=([\w-]+)$/);
  if (!m) {
    if (S) return goLobby({ replace: true });
    return showScreen("lobby", "", { replace: true });
  }
  const [, kind, id] = m;
  if (kind === "local") {
    if (S && !S.online && S.id === id) return showScreen("game", location.hash, { replace: true });
    const g = Store.get(id);
    if (!g) {
      toast("That game isn't on this device.");
      return goLobby({ replace: true });
    }
    showScreen("game", location.hash, { replace: true });
    return resumeLocal(g);
  }
  if (S?.online?.id === id) return showScreen("game", location.hash, { replace: true });
  if (S) {
    if (!S.online) save();
    gameToken++;
    S = null;
  }
  showScreen("game", location.hash, { replace: true });
  $("#status").textContent = "Loading…";
  window.Online?.followGame(id); // no-op until signed in
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

function ago(ms) {
  const m = Math.round((Date.now() - ms) / 60000);
  if (m < 1) return "just now";
  if (m < 60) return `${m} min ago`;
  const h = Math.round(m / 60);
  if (h < 24) return `${h} h ago`;
  return `${Math.round(h / 24)} d ago`;
}

function renderLocalGames() {
  if (!pageOpen()) return;
  const ul = $("#local-games");
  ul.innerHTML = "";
  pruneGames();
  const games = Store.all().sort((a, b) => !!a.over - !!b.over || b.updated - a.updated);
  for (const g of games) {
    const names = g.players.map((p) => p.name).join(" vs ");
    let sub;
    if (g.over) sub = `Finished · ${g.players[g.over.winner]?.name ?? "?"} won · ${ago(g.updated)}`;
    else {
      const who = g.players[g.turn];
      const turn = who.type !== "human" ? `${who.name} to play` : who.name === "You" ? "Your turn" : `${who.name}'s turn`;
      const tiles = g.players.map((p) => keys(p.rack).length).join(" / ");
      sub = `${turn} · ${tiles} tiles · ${ago(g.updated)}`;
    }
    const buttons = g.over
      ? [["Remove", () => { Store.remove(g.id); window.Cloud?.remove(g.id); renderLocalGames(); }], ["View", () => openGame("local", g.id)]]
      : [["Resign", () => {
        // Ask first, so Cancel leaves you on the Games screen.
        if (viewerIndex(g) < 0 || !confirm(resignQuestion(g))) return;
        openGame("local", g.id);
        resignLocal({ asked: true });
      }, "danger"], ["Open", () => openGame("local", g.id), "primary"]];
    ul.appendChild(row(names, sub, buttons, `#local=${g.id}` === lastGameHash ? "current" : ""));
  }
  if (!games.length) ul.innerHTML = '<li class="empty">No local games yet.</li>';
  $("#local-sync-note").textContent = !$("#lobby-checking").hidden ? "" : window.Cloud?.signedIn()
    ? "Synced with your Google account, so they're on your other devices too."
    : "Sign in below to have these on your other devices too.";
}

// ---------------------------------------------------------------- dialogs

// The "New local game" form on the Games screen, laid out like "Create online
// game": player count, how many are computers, their level, then names (only
// with two or more people; one person is "You") and the turn timer (also only
// with two or more people).
let setupNames = []; // names typed for the people, kept while the counts change
let setupOnLobby = false; // open the form when the Games screen next shows

function openSetup(toggle = false) {
  const form = $("#setup");
  if (toggle && !form.hidden) { form.hidden = true; return; }
  const settings = loadSettings();
  const people = settings.players.filter((p) => p.type === "human");
  const computers = settings.players.filter((p) => p.type !== "human");
  setupNames = people.length > 1 ? people.map((p) => p.name) : [];
  $("#setup-players").value = String(Math.min(4, Math.max(2, settings.players.length)));
  updateSetup();
  $("#setup-ai").value = String(Math.min(computers.length, settings.players.length - 1));
  $("#setup-level").value = computers[0]?.type === "easy" ? "easy" : "hard";
  $("#setup-timer").value = String(settings.timer);
  updateSetup();
  form.hidden = false;
  form.scrollIntoView({ block: "nearest" });
}

function updateSetup() {
  const total = Number($("#setup-players").value);
  const ai = $("#setup-ai");
  const keep = Math.min(Number(ai.value), total - 1);
  ai.innerHTML = "";
  for (let i = 0; i < total; i++) ai.add(new Option(String(i), String(i)));
  ai.value = String(keep);
  const humans = total - keep;
  $("#setup-level-row").hidden = keep === 0;
  $("#setup-timer-row").hidden = humans < 2; // no timer when only one person plays
  $("#setup-names-row").hidden = humans < 2;
  const box = $("#setup-names");
  for (const [i, input] of [...box.querySelectorAll("input")].entries()) setupNames[i] = input.value;
  box.innerHTML = "";
  if (humans < 2) return;
  for (let i = 0; i < humans; i++) {
    const input = document.createElement("input");
    input.maxLength = 14;
    input.placeholder = `Player ${i + 1}`;
    input.setAttribute("aria-label", `Player ${i + 1}'s name`);
    input.value = setupNames[i] ?? "";
    box.appendChild(input);
  }
}

function readSetup() {
  const total = Number($("#setup-players").value);
  const ai = Number($("#setup-ai").value);
  const level = $("#setup-level").value;
  const names = [...document.querySelectorAll("#setup-names input")].map((el, i) => el.value.trim() || `Player ${i + 1}`);
  const players = [];
  for (let i = 0; i < total - ai; i++) players.push({ name: total - ai > 1 ? names[i] : "You", type: "human" });
  for (let i = 0; i < ai; i++) players.push({ name: ai > 1 ? `Computer ${i + 1}` : "Computer", type: level });
  // Kept even with one person (it's ignored then) so it's remembered for next time.
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
  // Online, the second button already goes to Games.
  $("#results-again").hidden = !!S.online;
  $("#results-home").hidden = !!S.online;
  $("#results-new").textContent = S.online ? "All games" : "New game";
  if (!$("#results").open) $("#results").showModal();
}

// ---------------------------------------------------------------- wiring

function init() {
  startWorker();
  document.addEventListener("pointerdown", onPointerDown);
  document.addEventListener("click", onTapPlace);
  window.addEventListener("pointermove", onPointerMove);
  window.addEventListener("pointerup", onPointerUp);
  window.addEventListener("pointercancel", onPointerUp);
  window.addEventListener("resize", () => render({ animate: false }));
  // When the keyboard opens, keep the text box being typed in on screen.
  document.addEventListener("focusin", (e) => {
    if (e.target.matches("input")) setTimeout(() => e.target.scrollIntoView({ block: "nearest" }), 350);
  });
  document.addEventListener("contextmenu", (e) => e.target.closest(".tile") && e.preventDefault());

  $("#main-btn").onclick = onMain;
  $("#undo").onclick = undo;
  $("#reset").onclick = resetTurn;
  $("#sort-num").onclick = () => sortRack("num");
  $("#sort-run").onclick = () => sortRack("run");
  $("#hud-home").onclick = (e) => { e.preventDefault(); goLobby(); };
  $("#resign-btn").onclick = () => (S.online ? Online.resignCurrent() : resignLocal());
  $("#settings-btn").onclick = () => {
    $("#pref-fast").checked = prefs.fast;
    $(`input[name=pref-pickup][value=${prefs.pickup}]`).checked = true;
    $(`input[name=pref-move][value=${prefs.move}]`).checked = true;
    showPickupSetting();
    $("#settings-page").hidden = false;
  };
  window.addEventListener("popstate", route);
  $("#settings-back").onclick = () => { $("#settings-page").hidden = true; };
  $("#pref-fast").onchange = (e) => setPref("fast", e.target.checked);
  for (const r of document.querySelectorAll("input[name=pref-pickup]")) r.onchange = () => { setPref("pickup", r.value); setSelection(null); };
  for (const r of document.querySelectorAll("input[name=pref-move]")) r.onchange = () => { setPref("move", r.value); setSelection(null); showPickupSetting(); };
  $("#new-local").onclick = () => openSetup(true);
  $("#setup-players").onchange = updateSetup;
  $("#setup-ai").onchange = updateSetup;
  $("#setup").onsubmit = (e) => {
    e.preventDefault();
    $("#setup").hidden = true;
    newGame(readSetup());
  };
  $("#results-home").onclick = () => goLobby();
  $("#results-again").onclick = () => { $("#results").close(); newGame(S.settings); };
  $("#results-new").onclick = () => {
    $("#results").close();
    setupOnLobby = !S.online; // the form is on the Games screen
    goLobby();
  };
  $("#cover-btn").onclick = () => {
    covered = false;
    armTimer();
    save();
    render();
  };
  setInterval(tick, 250);

  migrateOldSave();
  route();
}

// ---------------------------------------------------------------- version check
// The update light is shared by Alex's Pages sites (github.com/alexknight0/pages-common).
// The game is saved after every move, so updating (which reloads the page) carries on
// where you left off. Loaded dynamically so the game still runs if jsDelivr is unreachable.

import("https://cdn.jsdelivr.net/gh/alexknight0/pages-common@1.0.0/update.js")
  .then(({ initUpdateLight }) => initUpdateLight({
    version: VERSION,
    buttons: ".version", // in a game and on the Games screen
    report: toast,
    beforeUpdate() {
      cancelDrag();
      if (S) save();
    },
  }))
  .catch((e) => {
    console.warn("update light:", e);
    for (const b of document.querySelectorAll(".version")) {
      b.dataset.state = "unknown";
      b.title = "Couldn't load the update check (offline?).";
    }
  });

init();
