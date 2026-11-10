// Online play: Google or guest sign-in, a lobby of open games, and games synced through
// Firestore (project rummikub-10501b; access rules in firestore.rules).
//
//   games/{id}: status "open" | "playing" | "over", host (uid), hostName,
//     created / updated (ms), timer (s), seats [{uid, name, photo, type}],
//     playerUids [uid], and once playing: board {tileId: row * 100 + col},
//     turn, moveNo, counts [tiles per seat], melded [bool], lastPlaced [ids],
//     lastMove {seat, kind: "play" | "draw" | "pass" | "skip"}, passes,
//     poolCount, over {winner: seat | null}, turnAt (ms, when the current
//     turn began; the turn timer counts from it)
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
// Guests use Firebase anonymous sign-in: a uid kept in this browser's
// localStorage, with the name they typed as the profile's displayName. The
// rules only need request.auth, so guests play online like anyone else.
// "Sign in" on a guest links a Google account to the same uid, so their games
// carry over (unless that Google account was already used here; then they
// switch to it). Guests' local games aren't synced.
//
// It also syncs the Google-signed-in player's games on this device (against the
// computer / pass and play) between their devices:
//   users/{uid}/games/{id}: {state: JSON of the game (as app.js stores it,
//     without the undo history), updated (ms), deleted (bool)}
// The newest copy (by `updated`) wins; a removed game leaves deleted: true so
// other devices remove it too.
//
// Uses globals from app.js: S, Store, GAME_PREFIX, applyRemote, onlineResults,
// resumeLocal, route, openGame, goLobby, pageOpen, renderLocalGames, showWelcome, row,
// toast, requestAIMove, aiMoveIsLegal, layoutSets, shuffle, keys, makeDeck, pace.
//
// A player who resigns keeps their seat with seats[i].resigned = true; turns
// skip them, and the game ends when one player (or no person) is left.

import { initializeApp } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-app.js";
import { initializeAuth, browserLocalPersistence, browserPopupRedirectResolver, GoogleAuthProvider, signInWithPopup, signOut, onAuthStateChanged, signInAnonymously, updateProfile, linkWithPopup, signInWithCredential } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-auth.js";
import { getFirestore, doc, collection, query, where, onSnapshot, runTransaction, addDoc, getDoc, setDoc } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-firestore.js";

const firebaseConfig = {
  apiKey: "AIzaSyBiB5Jk4IxiYqwvvsfk5A6-n_ia3tBpRVg",
  authDomain: "rummikub-10501b.firebaseapp.com",
  projectId: "rummikub-10501b",
  storageBucket: "rummikub-10501b.firebasestorage.app",
  messagingSenderId: "226803527375",
  appId: "1:226803527375:web:6e6d74390f22f3e1be51ba",
};

const LOBBY_MAX_AGE_MS = 24 * 3600_000;
const AI_BACKUP_DELAY_MS = 8000; // other players' devices take over computer turns after this

const app = initializeApp(firebaseConfig);
// Sign-in is kept in localStorage, not Firebase's default IndexedDB: all of Alex's sites share
// one origin and so one sign-in database, and Firebase waits forever if another site's page
// blocks opening it (seen on Android 2026-11-02: blank page until site data was cleared).
const auth = initializeAuth(app, { persistence: browserLocalPersistence, popupRedirectResolver: browserPopupRedirectResolver });
const db = getFirestore(app);
const $ = (sel) => document.querySelector(sel);

let user = null;
let lobbySubs = [];
let lobbyData = { open: [], mine: [] };
let cur = null; // {id, g, hand, seat, unsubs}
let aiTimer = null;
let resultsFor = null;
let pendingGame = null; // online game in the URL, waiting for sign-in to load
const joinedAt = new Map(); // game id -> when this device joined it (ms)
const JOIN_GRACE_MS = 10_000;

const gameRef = (id) => doc(db, "games", id);
const handRef = (id, h) => doc(db, "games", id, "hands", h);
const poolRef = (id) => doc(db, "games", id, "secret", "pool");
// A guest's name is used whole (they typed it); a Google name is cut to the first name.
const firstName = (u) => (u.isAnonymous ? (u.displayName || "Guest").slice(0, 14) : (u.displayName || u.email || "Player").split(/[\s@]/)[0].slice(0, 14));
const syncing = () => !!user && !user.isAnonymous; // local games sync only to a Google account
const meSeat = () => ({ uid: user.uid, name: firstName(user), photo: user.photoURL || null, type: "human" });
const gameScreenHidden = () => $("#game-screen").hidden;
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ---------------------------------------------------------------- sign-in

const popupClosed = (e) => e.code === "auth/popup-closed-by-user" || e.code === "auth/cancelled-popup-request";

async function signIn() {
  try {
    await signInWithPopup(auth, new GoogleAuthProvider());
  } catch (e) {
    if (!popupClosed(e)) toast(`Sign-in failed: ${e.code || e.message}`);
  }
}

// Returns true once signed in as a guest called `name`.
async function signInGuest(name) {
  try {
    const { user: u } = await signInAnonymously(auth);
    await updateProfile(u, { displayName: name });
    user = auth.currentUser;
    renderAccount();
    if (pageOpen()) renderLobby();
    return true;
  } catch (e) {
    console.warn(e);
    return false;
  }
}

async function renameGuest() {
  const name = prompt("Your name (for new games):", firstName(user))?.trim().slice(0, 14);
  if (!name) return;
  try {
    await updateProfile(user, { displayName: name });
    localStorage.setItem("rummikub:guestName", name);
    renderAccount();
  } catch (e) {
    console.warn(e);
    toast("Couldn't change your name. Check your connection.");
  }
}

// A guest signs in with Google: the Google account joins the guest's uid, so
// their online and local games stay. If that Google account has been used
// for Rummikub before it can't join; offer to switch to it instead.
async function linkGoogle() {
  try {
    const res = await linkWithPopup(user, new GoogleAuthProvider());
    const g = res.user.providerData.find((p) => p.providerId === "google.com");
    await updateProfile(res.user, { displayName: g?.displayName || res.user.displayName, photoURL: g?.photoURL || null });
    user = auth.currentUser;
    renderAccount();
    startSync();
    renderLocalGames();
    toast("Signed in. Your games are kept.");
  } catch (e) {
    if (popupClosed(e)) return;
    const cred = GoogleAuthProvider.credentialFromError(e);
    if (e.code === "auth/credential-already-in-use" && cred) {
      if (!confirm("That Google account already has Rummikub games. Switch to it? Your guest games stay with the guest account, which you won't be able to get back to.")) return;
      leaveView();
      await signInWithCredential(auth, cred).catch((e2) => toast(`Sign-in failed: ${e2.code || e2.message}`));
    } else toast(`Sign-in failed: ${e.code || e.message}`);
  }
}

function renderAccount() {
  const box = $("#account");
  box.innerHTML = "";
  $("#lobby-signin").hidden = !!user || !$("#lobby-checking").hidden; // not until we know
  $("#lobby-body").hidden = !user;
  if (!user) return;
  if (user.photoURL) {
    const img = document.createElement("img");
    img.referrerPolicy = "no-referrer";
    img.alt = "";
    img.src = user.photoURL;
    box.appendChild(img);
  }
  const name = document.createElement(user.isAnonymous ? "button" : "span");
  name.textContent = firstName(user);
  const out = document.createElement("button");
  out.type = "button";
  out.className = "link";
  if (user.isAnonymous) {
    // Guests can't sign out (the account would be lost); they can rename or sign in.
    name.type = "button";
    name.className = "name-btn";
    name.title = "Change your name";
    name.onclick = renameGuest;
    out.textContent = "Sign in";
    out.title = "Sign in with Google to keep your games on all your devices";
    out.onclick = linkGoogle;
  } else {
    out.textContent = "Sign out";
    out.onclick = async () => {
      leaveView();
      await signOut(auth);
    };
  }
  box.append(name, out);
}

// ---------------------------------------------------------------- games page (online part)

function pageOpened() {
  renderAccount();
  $("#create-form").hidden = true;
  subscribeLobby();
}

const pageClosed = () => unsubscribeLobby();

function subscribeLobby() {
  unsubscribeLobby();
  if (!user || !pageOpen()) return;
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
    const meIn = g.seats.find((s) => s.uid === user.uid);
    const yours = g.status === "playing" && g.seats[g.turn]?.uid === user.uid;
    let sub;
    if (g.status === "open") sub = `Waiting to start · ${describe(g)}`;
    else if (g.status === "over") sub = g.over?.winner != null ? `Finished · ${g.seats[g.over.winner].name} won` : "Finished";
    else if (meIn?.resigned) sub = "You resigned";
    else sub = yours ? "Your turn" : `${g.seats[g.turn]?.name}'s turn`;
    const others = g.seats.filter((s) => s.uid !== user.uid).map((s) => s.name || "?").join(", ");
    const buttons = [];
    if (g.status === "playing" && !meIn?.resigned) buttons.push(["Resign", () => resign(g), "danger"]);
    buttons.push(["Open", () => openGame("online", g.id), "primary"]);
    const cls = (lastGameHash === `#online=${g.id}` ? "current " : "") + (yours ? "yours" : "");
    mineBox.appendChild(row(`vs ${others || "nobody yet"}`, sub, buttons, cls));
  }
  const open = lobbyData.open
    .filter((g) => !g.playerUids.includes(user.uid) && now - g.created < LOBBY_MAX_AGE_MS)
    .filter((g) => g.seats.some((s) => s.type === "human" && !s.uid))
    .sort((a, b) => b.created - a.created);
  for (const g of open) openBox.appendChild(row(`${g.hostName}'s game`, describe(g), [["Join", () => joinGame(g.id), "primary"]]));
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
  $("#create-timer-row").hidden = total - keep < 2; // no timer when you're the only person
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
    openGame("online", ref.id);
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
    joinedAt.set(id, Date.now());
    openGame("online", id);
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
  if (!$("#room").open && !pageOpen()) $("#room").showModal();
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
        passes: 0, poolCount: pool.length, over: null, updated: Date.now(), turnAt: Date.now(),
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
  goLobby();
}

async function resign(g) {
  const others = g.seats.filter((s) => s.uid !== user.uid && !s.resigned);
  const msg = others.length > 1
    ? "Resign this game? You'll be out, and the others carry on without you."
    : `Resign this game? ${others[0]?.name ?? "The other player"} wins.`;
  if (!confirm(msg)) return;
  try {
    await runTransaction(db, async (tx) => {
      const snap = await tx.get(gameRef(g.id));
      if (!snap.exists()) return;
      const d = snap.data();
      const seat = d.seats.findIndex((s) => s.uid === user.uid);
      if (d.status !== "playing" || seat < 0 || d.seats[seat].resigned) return;
      const seats = d.seats.map((s, i) => (i === seat ? { ...s, resigned: true } : s));
      const upd = { seats, moveNo: d.moveNo + 1, lastMove: { seat, kind: "resign" }, lastPlaced: [], updated: Date.now() };
      const left = seats.map((s, i) => i).filter((i) => !seats[i].resigned);
      if (left.length === 1 || !left.some((i) => seats[i].type === "human")) {
        // Last one in wins; if only computers are left, the one with the fewest tiles.
        const winner = left.reduce((a, b) => (d.counts[b] < d.counts[a] ? b : a));
        Object.assign(upd, { status: "over", over: { winner } });
      } else if (d.turn === seat) Object.assign(upd, { turn: nextSeat(seats, seat), turnAt: Date.now() });
      tx.update(gameRef(g.id), upd);
    });
    toast("You resigned.");
  } catch (e) {
    console.warn(e);
    toast("Couldn't resign. Check your connection.");
  }
}

// ---------------------------------------------------------------- following a game

// Follows the online game shown in the URL (called by route() in app.js).
function followGame(id) {
  if (!user) {
    pendingGame = id; // onAuthStateChanged picks it up
    return;
  }
  pendingGame = null;
  if (cur?.id === id) { // already following it
    if (cur.g?.status === "open") renderRoom(cur.g);
    return;
  }
  leaveView();
  cur = { id, g: null, hand: null, seat: -1, unsubs: [] };
  const mine = cur;
  cur.unsubs.push(onSnapshot(gameRef(id), (snap) => {
    if (cur !== mine) return;
    if (!snap.exists()) {
      toast("The host cancelled that game.");
      return goLobby({ replace: true });
    }
    const g = snap.data();
    cur.g = g;
    cur.seat = g.seats.findIndex((s) => s.uid === user.uid);
    if (cur.seat < 0) {
      // Just joined: the first copy can be the one the lobby had cached from
      // before the join (transactions don't update the cache), so wait for
      // the server's copy instead of saying you're not in it.
      if (snap.metadata?.fromCache || (joinedAt.get(id) ?? 0) > Date.now() - JOIN_GRACE_MS) return;
      toast("You're not in that game.");
      return goLobby({ replace: true });
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
  if ($("#room").open) $("#room").close();
}

// ---------------------------------------------------------------- syncing games on this device

const PUSH_DELAY_MS = 1500;
const cloudRef = (id) => doc(db, "users", user.uid, "games", id);
const pushTimers = new Map(); // game id -> timeout
const remoteSeen = new Map(); // game id -> `updated` of the copy in Firestore
let cloudUnsub = null;

// Called by app.js after every change to a game; uploads it shortly after.
function queue(id) {
  if (!syncing()) return;
  clearTimeout(pushTimers.get(id));
  pushTimers.set(id, setTimeout(() => push(id), PUSH_DELAY_MS));
}

async function push(id) {
  pushTimers.delete(id);
  if (!syncing()) return;
  const g = Store.get(id);
  if (!g || (remoteSeen.get(id) ?? -1) >= g.updated) return;
  try {
    await setDoc(cloudRef(id), { state: Store.pack({ ...g, history: [] }), updated: g.updated, deleted: false });
    remoteSeen.set(id, g.updated);
  } catch (e) {
    console.warn("couldn't sync game", id, e);
  }
}

function flushPushes() {
  for (const [id, t] of pushTimers) {
    clearTimeout(t);
    push(id);
  }
}

async function removeRemote(id) {
  if (!syncing()) return;
  try {
    await setDoc(cloudRef(id), { state: "", updated: Date.now(), deleted: true });
  } catch (e) {
    console.warn(e);
  }
}

function startSync() {
  stopSync();
  cloudUnsub = onSnapshot(collection(db, "users", user.uid, "games"), (snap) => {
    const tomb = Store.tombstones();
    const remote = new Set();
    let changed = false;
    for (const d of snap.docs) {
      const id = d.id;
      const r = d.data();
      remote.add(id);
      remoteSeen.set(id, r.updated);
      const local = Store.get(id);
      if (r.deleted) {
        if (local && local.updated <= r.updated) {
          Store.remove(id);
          changed = true;
          if (S && !S.online && S.id === id) goLobby({ replace: true });
        }
        continue;
      }
      if (tomb[id] && tomb[id] >= r.updated) { removeRemote(id); continue; } // removed here
      if (!local || r.updated > local.updated) {
        const g = Store.unpack(r.state);
        if (!g) continue;
        g.updated = r.updated;
        Store.put(g);
        changed = true;
        // A newer copy of the game on screen, played on another device.
        if (S && !S.online && S.id === id) resumeLocal(g);
      }
    }
    // Upload games the account doesn't have yet, or has an older copy of.
    for (const g of Store.all()) if (!remote.has(g.id) || g.updated > (remoteSeen.get(g.id) ?? 0)) queue(g.id);
    if (changed) renderLocalGames();
  }, (e) => console.warn("game sync stopped", e));
}

function stopSync() {
  cloudUnsub?.();
  cloudUnsub = null;
}

document.addEventListener("visibilitychange", () => document.hidden && flushPushes());
window.addEventListener("pagehide", flushPushes);

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

// The next seat after `from` that hasn't resigned.
function nextSeat(seats, from) {
  let i = from;
  do i = (i + 1) % seats.length; while (seats[i].resigned && i !== from);
  return i;
}

// The game update for a finished turn. Tile ids and board are this move's.
function nextState(g, seat, kind, { board, count, placed, poolCount } = {}) {
  const n = g.seats.filter((s) => !s.resigned).length;
  const counts = g.counts.slice();
  if (count !== undefined) counts[seat] = count;
  const melded = g.melded.slice();
  if (kind === "play") melded[seat] = true;
  const passes = kind === "pass" || kind === "skip" ? g.passes + 1 : 0;
  const upd = {
    counts, melded, passes, lastMove: { seat, kind }, lastPlaced: placed || [],
    moveNo: g.moveNo + 1, turn: nextSeat(g.seats, g.turn), updated: Date.now(), turnAt: Date.now(),
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
  const humans = g.seats.map((s, i) => (s.type === "human" && !s.resigned ? i : -1)).filter((i) => i >= 0);
  const rank = humans.includes(cur.seat) ? humans.indexOf(cur.seat) : humans.length; // resigned players are the last backup
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
  await sleep(Math.max(0, pace().think - (performance.now() - t0)));
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
$("#room-lobby").onclick = () => goLobby();
// Escape on the waiting room just closes it; reopen it from the lobby.
$("#room").addEventListener("cancel", (e) => e.preventDefault());

window.Online = { pageOpened, pageClosed, leaveView, followGame, play, draw, skip, resignCurrent: () => cur?.g && resign({ id: cur.id, ...cur.g }) };
window.Cloud = { queue, remove: removeRemote, signedIn: syncing };
Object.assign(window.Online, { signIn, signInGuest });

// app.js routed before this module loaded: pick up an online game in the URL.
{
  const m = location.hash.match(/^#online=([\w-]+)$/);
  if (m && !gameScreenHidden()) pendingGame = m[1];
}

onAuthStateChanged(auth, (u) => {
  user = u;
  $("#lobby-checking").hidden = true;
  renderAccount();
  if (u && !u.isAnonymous) startSync();
  else stopSync();
  // Nobody signed in on this device: ask (Google or guest). An online game in
  // the URL waits behind it and loads once they've chosen.
  showWelcome(!u);
  if (u && pendingGame) followGame(pendingGame);
  else if (!u && cur) goLobby({ replace: true });
  if (pageOpen()) {
    subscribeLobby();
    renderLocalGames();
  }
});
