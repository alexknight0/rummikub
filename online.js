// Online play: Google sign-in, a lobby of open games, and games synced through
// Firestore (project rummikub-10501b; access rules in firestore.rules).
//
//   games/{id}: status "open" | "playing" | "over", host (uid), hostName,
//     created / updated (ms), timer (s), seats [{uid, name, photo, type}],
//     playerUids [uid], and once playing: board {tileId: row * 100 + col},
//     turn, moveNo, counts [tiles per seat], melded [bool], lastPlaced [ids],
//     lastMove {seat, kind: "play" | "draw" | "pass" | "skip"}, passes,
//     poolCount, over {winner: seat | null}
//   games/{id}/hands/{uid or "ai<seat>"}: {tiles: [ids], moveNo}. A person's
//     hand can only be read by them until the game ends.
//   games/{id}/secret/pool: {pool: [ids]} (drawn from the end), readable by
//     the game's players.
//
// There's no server: the host's browser deals, and every move is a Firestore
// transaction that checks moveNo so two devices can't both move. A player could
// read the pool order (or, for the host, the opening hands) with developer
// tools; that's accepted for games among friends.
//
// Uses globals from app.js: S, applyRemote, onlineResults, resumeLocal,
// loadLocalGame, openHome, toast, requestAIMove, aiMoveIsLegal, layoutSets,
// shuffle, keys, makeDeck, AI_MIN_THINK_MS, MODE_KEY.

import { initializeApp } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-app.js";
import { getAuth, GoogleAuthProvider, signInWithPopup, signOut, onAuthStateChanged } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-auth.js";
import { getFirestore, doc, collection, query, where, onSnapshot, runTransaction, addDoc, getDoc } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-firestore.js";

const firebaseConfig = {
  apiKey: "AIzaSyBiB5Jk4IxiYqwvvsfk5A6-n_ia3tBpRVg",
  authDomain: "rummikub-10501b.firebaseapp.com",
  projectId: "rummikub-10501b",
  storageBucket: "rummikub-10501b.firebasestorage.app",
  messagingSenderId: "226803527375",
  appId: "1:226803527375:web:6e6d74390f22f3e1be51ba",
};

const GAME_KEY = "rummikub:onlineGame";
const LOBBY_MAX_AGE_MS = 24 * 3600_000;
const AI_BACKUP_DELAY_MS = 8000; // other players' devices take over computer turns after this

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);
const db = getFirestore(app);
const $ = (sel) => document.querySelector(sel);

let user = null;
let lobbySubs = [];
let lobbyData = { open: [], mine: [] };
let cur = null; // {id, g, hand, seat, unsubs}
let aiTimer = null;
let resultsFor = null;

const gameRef = (id) => doc(db, "games", id);
const handRef = (id, h) => doc(db, "games", id, "hands", h);
const poolRef = (id) => doc(db, "games", id, "secret", "pool");
const firstName = (u) => (u.displayName || u.email || "Player").split(/[\s@]/)[0].slice(0, 14);
const meSeat = () => ({ uid: user.uid, name: firstName(user), photo: user.photoURL || null, type: "human" });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ---------------------------------------------------------------- sign-in

async function signIn() {
  try {
    await signInWithPopup(auth, new GoogleAuthProvider());
  } catch (e) {
    if (e.code !== "auth/popup-closed-by-user" && e.code !== "auth/cancelled-popup-request") toast(`Sign-in failed: ${e.code || e.message}`);
  }
}

function renderAccount() {
  const box = $("#account");
  box.innerHTML = "";
  $("#lobby-signin").hidden = !!user;
  $("#lobby-body").hidden = !user;
  if (!user) return;
  if (user.photoURL) {
    const img = document.createElement("img");
    img.referrerPolicy = "no-referrer";
    img.alt = "";
    img.src = user.photoURL;
    box.appendChild(img);
  }
  const name = document.createElement("span");
  name.textContent = firstName(user);
  const out = document.createElement("button");
  out.type = "button";
  out.className = "link";
  out.textContent = "Sign out";
  out.onclick = async () => {
    leaveView();
    await signOut(auth);
  };
  box.append(name, out);
}

// ---------------------------------------------------------------- lobby

function openLobby() {
  for (const d of ["#home", "#results", "#room"]) if ($(d).open) $(d).close();
  renderAccount();
  $("#create-form").hidden = true;
  if (!$("#lobby").open) $("#lobby").showModal();
  subscribeLobby();
}

function subscribeLobby() {
  unsubscribeLobby();
  if (!user || !$("#lobby").open) return;
  // Don't show lists from the last time the lobby was open.
  lobbyData = { open: null, mine: null };
  $("#my-games-wrap").hidden = true;
  $("#open-games").innerHTML = '<li class="empty">Loading…</li>';
  const games = collection(db, "games");
  const list = (snap) => snap.docs.map((d) => ({ id: d.id, ...d.data() }));
  const fail = (e) => { console.warn(e); $("#open-games").textContent = "Couldn't load games. Check your connection."; };
  lobbySubs.push(onSnapshot(query(games, where("status", "==", "open")), (s) => { lobbyData.open = list(s); renderLobby(); }, fail));
  lobbySubs.push(onSnapshot(query(games, where("playerUids", "array-contains", user.uid)), (s) => { lobbyData.mine = list(s); renderLobby(); }, fail));
}

function unsubscribeLobby() {
  for (const u of lobbySubs) u();
  lobbySubs = [];
}

function describe(g) {
  const humans = g.seats.filter((s) => s.type === "human");
  const ais = g.seats.length - humans.length;
  const bits = [`${humans.filter((s) => s.uid).length}/${humans.length} players`];
  if (ais) bits.push(`${ais} computer${ais > 1 ? "s" : ""}`);
  bits.push(g.timer ? `${g.timer}s turns` : "no timer");
  return bits.join(" · ");
}

function gameRow(g, label, sub, action) {
  const li = document.createElement("li");
  li.className = "game-row";
  li.innerHTML = '<div><b></b><small></small></div><button type="button"></button>';
  li.querySelector("b").textContent = label;
  li.querySelector("small").textContent = sub;
  const btn = li.querySelector("button");
  btn.textContent = action;
  btn.className = action === "Join" ? "primary" : "";
  btn.onclick = () => (action === "Join" ? joinGame(g.id) : enterGame(g.id));
  return li;
}

function renderLobby() {
  if (!lobbyData.open || !lobbyData.mine) return; // wait for both lists
  const now = Date.now();
  const mineBox = $("#my-games");
  const openBox = $("#open-games");
  mineBox.innerHTML = "";
  openBox.innerHTML = "";
  const mine = lobbyData.mine
    .filter((g) => g.status !== "over" || now - g.updated < LOBBY_MAX_AGE_MS)
    .sort((a, b) => b.updated - a.updated);
  for (const g of mine) {
    let sub;
    if (g.status === "open") sub = `Waiting to start · ${describe(g)}`;
    else if (g.status === "over") sub = "Finished";
    else sub = g.seats[g.turn]?.uid === user.uid ? "Your turn" : `${g.seats[g.turn]?.name}'s turn`;
    mineBox.appendChild(gameRow(g, `${g.hostName}'s game`, sub, "Open"));
  }
  const open = lobbyData.open
    .filter((g) => !g.playerUids.includes(user.uid) && now - g.created < LOBBY_MAX_AGE_MS)
    .filter((g) => g.seats.some((s) => s.type === "human" && !s.uid))
    .sort((a, b) => b.created - a.created);
  for (const g of open) openBox.appendChild(gameRow(g, `${g.hostName}'s game`, describe(g), "Join"));
  $("#my-games-wrap").hidden = !mine.length;
  if (!open.length) openBox.innerHTML = '<li class="empty">No open games right now. Create one and ask a friend to join.</li>';
}

function updateCreateForm() {
  const total = Number($("#create-players").value);
  const ai = $("#create-ai");
  const keep = Math.min(Number(ai.value), total - 1);
  ai.innerHTML = "";
  for (let i = 0; i < total; i++) ai.add(new Option(String(i), String(i)));
  ai.value = String(keep);
  $("#create-level-row").hidden = keep === 0;
}

async function createGame() {
  const total = Number($("#create-players").value);
  const ai = Number($("#create-ai").value);
  const level = $("#create-level").value;
  const seats = [meSeat()];
  for (let i = 1; i < total - ai; i++) seats.push({ uid: null, name: "", photo: null, type: "human" });
  for (let i = 0; i < ai; i++) seats.push({ uid: null, name: `Computer${ai > 1 ? " " + (i + 1) : ""}`, photo: null, type: level });
  const now = Date.now();
  try {
    const ref = await addDoc(collection(db, "games"), {
      status: "open", host: user.uid, hostName: firstName(user), created: now, updated: now,
      timer: Number($("#create-timer").value), seats, playerUids: [user.uid],
    });
    enterGame(ref.id);
  } catch (e) {
    console.warn(e);
    toast("Couldn't create the game. Check your connection.");
  }
}

async function joinGame(id) {
  try {
    await runTransaction(db, async (tx) => {
      const snap = await tx.get(gameRef(id));
      if (!snap.exists()) throw new Error("That game no longer exists.");
      const g = snap.data();
      if (g.playerUids.includes(user.uid)) return;
      if (g.status !== "open") throw new Error("That game has already started.");
      const i = g.seats.findIndex((s) => s.type === "human" && !s.uid);
      if (i < 0) throw new Error("That game is full.");
      const seats = g.seats.slice();
      seats[i] = meSeat();
      tx.update(gameRef(id), { seats, playerUids: [...g.playerUids, user.uid], updated: Date.now() });
    });
    enterGame(id);
  } catch (e) {
    console.warn(e);
    toast(e.message?.startsWith("That game") ? e.message : "Couldn't join. Check your connection.");
  }
}

// ---------------------------------------------------------------- waiting room

function renderRoom(g) {
  const isHost = g.host === user.uid;
  $("#room-title").textContent = `${g.hostName}'s game`;
  const ul = $("#room-seats");
  ul.innerHTML = "";
  for (const s of g.seats) {
    const li = document.createElement("li");
    if (s.type !== "human") li.textContent = `${s.name} (computer, ${s.type})`;
    else if (s.uid) li.textContent = s.uid === user.uid ? `${s.name} (you)` : s.name;
    else { li.textContent = "Waiting for a player…"; li.className = "muted"; }
    ul.appendChild(li);
  }
  const filled = g.seats.filter((s) => s.type !== "human" || s.uid).length;
  $("#room-start").hidden = !isHost;
  $("#room-start").disabled = filled < 2;
  $("#room-leave").textContent = isHost ? "Cancel game" : "Leave";
  $("#room-note").textContent = isHost
    ? filled < 2 ? "Others can join from Play online → Open games." : "Start whenever you're ready. Empty seats are dropped."
    : "Waiting for the host to start…";
  for (const d of ["#lobby", "#home", "#results"]) if ($(d).open) $(d).close();
  if (!$("#room").open) $("#room").showModal();
}

async function startGame() {
  const id = cur?.id;
  if (!id) return;
  $("#room-start").disabled = true;
  try {
    await runTransaction(db, async (tx) => {
      const g = (await tx.get(gameRef(id))).data();
      if (g.status !== "open") return;
      const seats = g.seats.filter((s) => s.type !== "human" || s.uid);
      if (seats.length < 2) throw new Error("Need at least 2 players.");
      const pool = shuffle(makeDeck().map((_, i) => i));
      seats.forEach((s, i) => tx.set(handRef(id, s.type === "human" ? s.uid : "ai" + i), { tiles: pool.splice(0, 14), moveNo: 1 }));
      tx.set(poolRef(id), { pool });
      tx.update(gameRef(id), {
        status: "playing", seats, board: {}, turn: Math.floor(Math.random() * seats.length), moveNo: 1,
        counts: seats.map(() => 14), melded: seats.map(() => false), lastPlaced: [], lastMove: null,
        passes: 0, poolCount: pool.length, over: null, updated: Date.now(),
      });
    });
  } catch (e) {
    console.warn(e);
    toast(e.message === "Need at least 2 players." ? e.message : "Couldn't start the game. Check your connection.");
    $("#room-start").disabled = false;
  }
}

async function leaveRoom() {
  const id = cur?.id;
  if (!id) return;
  try {
    await runTransaction(db, async (tx) => {
      const snap = await tx.get(gameRef(id));
      if (!snap.exists()) return;
      const g = snap.data();
      if (g.status !== "open") return;
      if (g.host === user.uid) return tx.delete(gameRef(id));
      const seats = g.seats.map((s) => (s.uid === user.uid ? { uid: null, name: "", photo: null, type: "human" } : s));
      tx.update(gameRef(id), { seats, playerUids: g.playerUids.filter((u) => u !== user.uid), updated: Date.now() });
    });
  } catch (e) {
    console.warn(e);
  }
  leaveView();
  openLobby();
}

// ---------------------------------------------------------------- following a game

function enterGame(id) {
  leaveView();
  localStorage.setItem(GAME_KEY, id);
  localStorage.setItem(MODE_KEY, "online");
  if ($("#lobby").open) $("#lobby").close();
  cur = { id, g: null, hand: null, seat: -1, unsubs: [] };
  const mine = cur;
  cur.unsubs.push(onSnapshot(gameRef(id), (snap) => {
    if (cur !== mine) return;
    if (!snap.exists()) {
      toast("The host cancelled that game.");
      leaveView();
      return openLobby();
    }
    const g = snap.data();
    cur.g = g;
    cur.seat = g.seats.findIndex((s) => s.uid === user.uid);
    if (cur.seat < 0) {
      leaveView();
      return openLobby();
    }
    if (g.status === "open") return renderRoom(g);
    if ($("#room").open) $("#room").close();
    if (!cur.handSub) {
      cur.handSub = true;
      cur.unsubs.push(onSnapshot(handRef(id, user.uid), (h) => {
        if (cur !== mine || !h.exists()) return;
        cur.hand = h.data();
        combine();
      }, (e) => console.warn(e)));
    }
    combine();
  }, (e) => {
    console.warn(e);
    toast("Lost touch with the game. Check your connection.");
  }));
}

function leaveView() {
  clearTimeout(aiTimer);
  if (cur) for (const u of cur.unsubs) u();
  cur = null;
  localStorage.removeItem(GAME_KEY);
  if ($("#room").open) $("#room").close();
}

// The game doc and this player's hand arrive separately; a move that changed
// both is shown once both have arrived.
function combine() {
  const { g, hand, seat, id } = cur;
  if (!g || !hand || g.status === "open") return;
  const touchedHand = g.lastMove && g.lastMove.seat === seat && (g.lastMove.kind === "play" || g.lastMove.kind === "draw");
  if ((touchedHand && hand.moveNo < g.moveNo) || hand.moveNo > g.moveNo) return;
  applyRemote(id, g, hand.tiles, { uid: user.uid, seat });
  scheduleAI(g);
  if (g.status === "over" && resultsFor !== id + ":" + g.moveNo) {
    resultsFor = id + ":" + g.moveNo;
    fetchResults(id, g);
  }
}

async function fetchResults(id, g) {
  try {
    const hands = await Promise.all(g.seats.map((s, i) => getDoc(handRef(id, s.type === "human" ? s.uid : "ai" + i))));
    onlineResults(hands.map((h) => (h.exists() ? h.data().tiles : [])));
  } catch (e) {
    console.warn(e);
  }
}

// ---------------------------------------------------------------- moves

// The game update for a finished turn. Tile ids and board are this move's.
function nextState(g, seat, kind, { board, count, placed, poolCount } = {}) {
  const n = g.seats.length;
  const counts = g.counts.slice();
  if (count !== undefined) counts[seat] = count;
  const melded = g.melded.slice();
  if (kind === "play") melded[seat] = true;
  const passes = kind === "pass" || kind === "skip" ? g.passes + 1 : 0;
  const upd = {
    counts, melded, passes, lastMove: { seat, kind }, lastPlaced: placed || [],
    moveNo: g.moveNo + 1, turn: (g.turn + 1) % n, updated: Date.now(),
  };
  if (board) upd.board = board;
  if (poolCount !== undefined) upd.poolCount = poolCount;
  if (kind === "play" && count === 0) Object.assign(upd, { status: "over", over: { winner: seat }, turn: g.turn });
  else if (passes >= n) Object.assign(upd, { status: "over", over: { winner: null } });
  return upd;
}

function encodeBoard(board) {
  const out = {};
  for (const t of keys(board)) out[t] = board[t][0] * 100 + board[t][1];
  return out;
}

function checkTurn(g, moveNo, seat) {
  if (!g || g.status !== "playing" || g.moveNo !== moveNo || g.turn !== seat) throw new Error("stale");
}

async function play(placed) {
  const { id, seat, moveNo } = S.online;
  const board = encodeBoard(S.board);
  const remaining = keys(S.players[seat].rack);
  await runTransaction(db, async (tx) => {
    const g = (await tx.get(gameRef(id))).data();
    checkTurn(g, moveNo, seat);
    tx.update(handRef(id, user.uid), { tiles: remaining, moveNo: g.moveNo + 1 });
    tx.update(gameRef(id), nextState(g, seat, "play", { board, count: remaining.length, placed }));
  });
}

async function drawFor(id, seat, moveNo, hand) {
  await runTransaction(db, async (tx) => {
    const g = (await tx.get(gameRef(id))).data();
    checkTurn(g, moveNo, seat);
    const pool = (await tx.get(poolRef(id))).data().pool;
    const tiles = (await tx.get(handRef(id, hand))).data().tiles;
    const t = pool.pop();
    if (t === undefined) return tx.update(gameRef(id), nextState(g, seat, "pass", {}));
    tx.update(poolRef(id), { pool });
    tx.update(handRef(id, hand), { tiles: [...tiles, t], moveNo: g.moveNo + 1 });
    tx.update(gameRef(id), nextState(g, seat, "draw", { count: tiles.length + 1, poolCount: pool.length }));
  });
}

function draw() {
  const { id, seat, moveNo } = S.online;
  return drawFor(id, seat, moveNo, user.uid);
}

async function skip(moveNo) {
  const id = S.online.id;
  await runTransaction(db, async (tx) => {
    const g = (await tx.get(gameRef(id))).data();
    if (!g || g.status !== "playing" || g.moveNo !== moveNo) throw new Error("stale");
    tx.update(gameRef(id), nextState(g, g.turn, "skip", {}));
  });
}

// Computer turns are played by the first person's device; the others take
// over (one at a time) if it doesn't happen, e.g. because that person left.
function scheduleAI(g) {
  clearTimeout(aiTimer);
  if (g.status !== "playing" || g.seats[g.turn].type === "human") return;
  const humans = g.seats.map((s, i) => (s.type === "human" ? i : -1)).filter((i) => i >= 0);
  const rank = Math.max(0, humans.indexOf(cur.seat));
  const { id } = cur;
  const moveNo = g.moveNo;
  aiTimer = setTimeout(() => runAITurn(id, moveNo).catch((e) => e.message !== "stale" && console.warn(e)), rank * AI_BACKUP_DELAY_MS);
}

async function runAITurn(id, moveNo) {
  const g = cur?.g;
  if (!g || cur.id !== id || g.moveNo !== moveNo) return;
  const seat = g.turn;
  const p = g.seats[seat];
  const hand = "ai" + seat;
  const tiles = (await getDoc(handRef(id, hand))).data().tiles;
  const t0 = performance.now();
  const res = await requestAIMove(S.board, tiles, g.melded[seat], p.type);
  await sleep(Math.max(0, AI_MIN_THINK_MS - (performance.now() - t0)));
  if (cur?.id !== id || cur.g.moveNo !== moveNo) return;
  const legal = res && aiMoveIsLegal({ rack: Object.fromEntries(tiles.map((t) => [t, 0])), melded: g.melded[seat] }, res);
  if (res && !legal) console.warn("AI produced an illegal move; drawing instead", res);
  if (!legal) return drawFor(id, seat, moveNo, hand);
  const board = encodeBoard(layoutSets(res.sets, S.board));
  const placed = new Set(res.placed);
  const remaining = tiles.filter((t) => !placed.has(t));
  await runTransaction(db, async (tx) => {
    const g2 = (await tx.get(gameRef(id))).data();
    checkTurn(g2, moveNo, seat);
    tx.update(handRef(id, hand), { tiles: remaining, moveNo: g2.moveNo + 1 });
    tx.update(gameRef(id), nextState(g2, seat, "play", { board, count: remaining.length, placed: res.placed }));
  });
}

// ---------------------------------------------------------------- wiring

$("#signin").onclick = signIn;
$("#lobby-close").onclick = () => $("#lobby").close();
$("#lobby").addEventListener("close", unsubscribeLobby);
$("#create-open").onclick = () => {
  $("#create-form").hidden = !$("#create-form").hidden;
  updateCreateForm();
};
$("#create-players").onchange = updateCreateForm;
$("#create-ai").onchange = updateCreateForm;
$("#create-form").onsubmit = (e) => {
  e.preventDefault();
  createGame();
};
$("#room-start").onclick = startGame;
$("#room-leave").onclick = leaveRoom;
$("#room-lobby").onclick = () => {
  $("#room").close();
  openLobby();
};
// Escape on the waiting room just closes it; reopen it from the lobby.
$("#room").addEventListener("cancel", (e) => e.preventDefault());

window.Online = { openLobby, leaveView, play, draw, skip };

let first = true;
onAuthStateChanged(auth, (u) => {
  user = u;
  renderAccount();
  if (first) {
    first = false;
    // Reopen the online game the page was showing, if any.
    if (localStorage.getItem(MODE_KEY) === "online") {
      const id = localStorage.getItem(GAME_KEY);
      if (u && id) enterGame(id);
      else {
        const saved = loadLocalGame();
        if (saved) resumeLocal(saved);
        else openHome();
        if (!u) openLobby();
      }
    }
  }
  if ($("#lobby").open) subscribeLobby();
  if (!u && cur) leaveView();
});
