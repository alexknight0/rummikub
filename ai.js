"use strict";
// Computer player. Runs in a Web Worker (or on the page as a fallback).
//
// aiMove({sets, rack, melded, level, timeLimit}) where sets is the table as
// arrays of {id, c, n} and rack is an array of {id, c, n}. Returns null (draw)
// or {sets: [[id, ...], ...] (the whole new table), placed: [id, ...]}.
//
// The search works on tile counts per (colour, number) rather than tile ids,
// so duplicate tiles don't multiply the work. Table tiles must all end up in
// a set; rack tiles are optional. It always branches on the lowest remaining
// tile, so every set it builds starts at that tile (or at jokers before it).

if (typeof importScripts === "function" && typeof window === "undefined") {
  importScripts("rules.js");
  self.onmessage = (e) => self.postMessage({ reqId: e.data.reqId, result: aiMove(e.data) });
}

const ORDER = [];
for (let n = 1; n <= 13; n++) for (let c = 0; c < 4; c++) ORDER.push(c * 14 + n);
const JOKER_COST = 700; // score penalty for spending a rack joker (worth 1000 per tile placed)

function aiMove({ sets, rack, melded, level, timeLimit = 1500 }) {
  const tableIds = sets.map((s) => s.map((t) => t.id));
  if (!melded) {
    const r = search([], rack, { need30: true, deadline: Date.now() + timeLimit });
    if (!r) return null;
    return finishMove(tableIds.concat(toIds(r.sets, [], rack, [])), rack);
  }
  const base = baseline(sets, rack, Date.now() + timeLimit / 3);
  let best = base;
  if (level === "hard") {
    const r = search(sets.flat(), rack, { deadline: Date.now() + timeLimit, minScore: base.score });
    if (r && r.score > base.score) best = { sets: toIds(r.sets, sets.flat(), rack, sets), score: r.score };
  }
  return finishMove(best.sets, rack);
}

function finishMove(newSets, rack) {
  const onTable = new Set(newSets.flat());
  const placed = rack.map((t) => t.id).filter((id) => onTable.has(id));
  return placed.length ? { sets: newSets, placed } : null;
}

// Plays sets made only from the rack, then adds leftover rack tiles to the
// ends of sets already on the table. Never rearranges the table.
function baseline(sets, rack, deadline) {
  const r = search([], rack, { deadline });
  const byId = new Map(rack.map((t) => [t.id, t]));
  const table = sets.map((s) => s.slice());
  if (r) for (const ids of toIds(r.sets, [], rack, [])) table.push(ids.map((id) => byId.get(id)));
  const used = new Set(table.flat().map((t) => t.id));
  let changed = true;
  while (changed) {
    changed = false;
    for (const t of rack) {
      if (used.has(t.id)) continue;
      for (const s of table) {
        if (analyzeSet([...s, t]).valid) s.push(t);
        else if (analyzeSet([t, ...s]).valid) s.unshift(t);
        else continue;
        used.add(t.id);
        changed = true;
        break;
      }
    }
  }
  let score = 0;
  for (const t of rack) if (used.has(t.id)) score += 1000 + (isJoker(t) ? -JOKER_COST : t.n);
  return { sets: table.map((s) => s.map((t) => t.id)), score };
}

function search(tableTiles, rackTiles, opts) {
  const bc = new Int8Array(56); // table counts per key c*14+n
  const rc = new Int8Array(56); // rack counts
  let bj = 0;
  let rj = 0;
  for (const t of tableTiles) isJoker(t) ? bj++ : bc[t.c * 14 + t.n]++;
  for (const t of rackTiles) isJoker(t) ? rj++ : rc[t.c * 14 + t.n]++;
  let rackLeft = rackTiles.length; // rack tiles not yet decided
  let placed = 0;
  let score = 0; // excluding the 1000 per placed tile
  let meld = 0; // points of rack tiles placed (jokers count as the tile they stand for)
  const sets = [];
  let best = null;
  let bestScore = opts.minScore ?? 0;
  let nodes = 0;
  let stop = false;

  const takeK = (k) => {
    if (bc[k] > 0) { bc[k]--; return false; }
    rc[k]--; rackLeft--; placed++;
    return true;
  };
  const giveK = (k, fromRack) => {
    if (fromRack) { rc[k]++; rackLeft++; placed--; } else bc[k]++;
  };
  const takeJ = () => {
    if (bj > 0) { bj--; return false; }
    rj--; rackLeft--; placed++;
    return true;
  };
  const giveJ = (fromRack) => {
    if (fromRack) { rj++; rackLeft++; placed--; } else bj++;
  };
  const giveAll = (items) => {
    for (let q = items.length - 1; q >= 0; q--) {
      const it = items[q];
      it.k < 0 ? giveJ(it.r) : giveK(it.k, it.r);
    }
  };
  const itemScore = (it) => (it.k < 0 ? -JOKER_COST : it.num);
  const rec = (set) => {
    let sc = 0;
    let mv = 0;
    for (const it of set.items) if (it.r) { sc += itemScore(it); mv += it.num; }
    set.sc = sc;
    set.mv = mv;
    score += sc;
    meld += mv;
    sets.push(set);
  };
  const unrec = () => {
    const s = sets.pop();
    score -= s.sc;
    meld -= s.mv;
  };

  // All tiles are decided; place leftover jokers on the ends of sets.
  function finish() {
    const added = [];
    const attach = (fromRack) => {
      for (const s of sets) {
        const len = s.items.length;
        let it;
        if (s.type === "run") {
          if (s.s + len <= 13) s.items.push((it = { k: -1, r: fromRack, num: s.s + len }));
          else if (s.s > 1) { s.s--; s.items.unshift((it = { k: -1, r: fromRack, num: s.s })); }
          else continue;
        } else if (len < 4) s.items.push((it = { k: -1, r: fromRack, num: s.n }));
        else continue;
        added.push([s, it]);
        return true;
      }
      return false;
    };
    let ok = true;
    for (let q = 0; q < bj; q++) if (!attach(false)) { ok = false; break; }
    if (ok) {
      let extra = 0;
      let extraScore = 0;
      let extraMeld = 0;
      for (let q = 0; q < rj; q++) {
        if (!attach(true)) break;
        const it = added[added.length - 1][1];
        extra++;
        extraScore += itemScore(it);
        extraMeld += it.num;
      }
      const total = (placed + extra) * 1000 + score + extraScore;
      if (total > bestScore && (!opts.need30 || meld + extraMeld >= FIRST_MELD)) {
        bestScore = total;
        best = sets.map((s) => ({ type: s.type, c: s.c, n: s.n, s: s.s, items: s.items.map((it) => ({ ...it })) }));
      }
    }
    for (let q = added.length - 1; q >= 0; q--) {
      const [s, it] = added[q];
      if (s.items[0] === it) { s.items.shift(); s.s++; } else s.items.pop();
    }
  }

  function dfs(i) {
    if (stop) return;
    if ((++nodes & 1023) === 0 && Date.now() > opts.deadline) { stop = true; return; }
    if ((placed + rackLeft) * 1000 + 999 <= bestScore) return;
    while (i < 52 && bc[ORDER[i]] + rc[ORDER[i]] === 0) i++;
    if (i === 52) { finish(); return; }
    const k = ORDER[i];
    const c = (k / 14) | 0;
    const n = k % 14;
    const mandatory = bc[k] > 0;

    // Runs of colour c containing n, with 0-2 jokers before n.
    for (let j0 = 0; j0 <= 2; j0++) {
      const s = n - j0;
      if (s < 1 || bj + rj < j0) break;
      const items = [];
      for (let q = 0; q < j0; q++) items.push({ k: -1, r: takeJ(), num: s + q });
      items.push({ k, r: takeK(k), num: n });
      for (let m = n + 1; ; m++) {
        if (items.length >= 3) {
          rec({ type: "run", c, s, items: items.slice() });
          dfs(i);
          unrec();
          if (stop) break;
        }
        if (m > 13) break;
        const km = c * 14 + m;
        if (bc[km] + rc[km] > 0) items.push({ k: km, r: takeK(km), num: m });
        else if (bj + rj > 0) items.push({ k: -1, r: takeJ(), num: m });
        else break;
      }
      giveAll(items);
      if (stop) return;
    }

    // Groups of number n containing colour c.
    const others = [];
    for (let c2 = c + 1; c2 < 4; c2++) if (bc[c2 * 14 + n] + rc[c2 * 14 + n] > 0) others.push(c2 * 14 + n);
    for (let mask = (1 << others.length) - 1; mask >= 0; mask--) {
      const chosen = others.filter((_, b) => mask & (1 << b));
      for (let jj = 0; jj <= 2; jj++) {
        const len = 1 + chosen.length + jj;
        if (len > 4 || bj + rj < jj) break;
        if (len < 3) continue;
        const items = [{ k, r: takeK(k), num: n }];
        for (const k2 of chosen) items.push({ k: k2, r: takeK(k2), num: n });
        for (let q = 0; q < jj; q++) items.push({ k: -1, r: takeJ(), num: n });
        rec({ type: "group", n, items });
        dfs(i);
        unrec();
        giveAll(items);
        if (stop) return;
      }
    }

    // Keep this rack tile in hand.
    if (!mandatory) {
      rc[k]--;
      rackLeft--;
      dfs(i);
      rc[k]++;
      rackLeft++;
    }
  }

  dfs(0);
  return best ? { sets: best, score: bestScore } : null;
}

// Signature of a set by content, so unchanged table sets keep their tile ids
// (and therefore their place on the table).
function sigOf(type, cOrN, s, len, keys) {
  return `${type}${cOrN}.${s}.${len}.${keys.sort((a, b) => a - b).join(",")}`;
}

// Turns search output (counts) back into tile ids.
function toIds(resultSets, tableTiles, rackTiles, originalSets) {
  const pool = (tiles) => {
    const m = new Map();
    for (const t of tiles) {
      const k = isJoker(t) ? -1 : t.c * 14 + t.n;
      if (!m.has(k)) m.set(k, []);
      m.get(k).push(t.id);
    }
    return m;
  };
  const bPool = pool(tableTiles);
  const rPool = pool(rackTiles);
  const origSigs = originalSets.map((s) => {
    const a = analyzeSet(s);
    const keys = s.map((t) => (isJoker(t) ? -1 : t.c * 14 + t.n));
    return a.type === "run" ? sigOf("r", a.c, a.s, s.length, keys) : sigOf("g", a.n, 0, s.length, keys);
  });
  const usedOrig = new Set();
  const out = [];
  const pending = [];
  for (const rs of resultSets) {
    if (rs.items.every((it) => !it.r)) {
      const keys = rs.items.map((it) => it.k);
      const sig = rs.type === "run" ? sigOf("r", rs.c, rs.s, keys.length, keys) : sigOf("g", rs.n, 0, keys.length, keys);
      const idx = origSigs.findIndex((x, j) => x === sig && !usedOrig.has(j));
      if (idx >= 0) {
        usedOrig.add(idx);
        const ids = originalSets[idx].map((t) => t.id);
        for (const t of originalSets[idx]) {
          const list = bPool.get(isJoker(t) ? -1 : t.c * 14 + t.n);
          list.splice(list.indexOf(t.id), 1);
        }
        out.push(ids);
        continue;
      }
    }
    pending.push(rs);
  }
  for (const rs of pending) {
    if (rs.type === "group") rs.items.sort((a, b) => (a.k < 0) - (b.k < 0) || a.k - b.k);
    out.push(rs.items.map((it) => (it.r ? rPool : bPool).get(it.k).pop()));
  }
  return out;
}
