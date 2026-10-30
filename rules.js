"use strict";
// Core Rummikub rules shared by the page and the AI worker.
// A tile is {c, n}: c = colour 0..3 (red, blue, orange, black), n = 1..13.
// Jokers have c = -1, n = 0.

const COLOURS = ["red", "blue", "orange", "black"];
const JOKER_PENALTY = 30;
const FIRST_MELD = 30;

function makeDeck() {
  const tiles = [];
  for (let copy = 0; copy < 2; copy++)
    for (let c = 0; c < 4; c++)
      for (let n = 1; n <= 13; n++) tiles.push({ c, n });
  tiles.push({ c: -1, n: 0 }, { c: -1, n: 0 });
  return tiles;
}

const isJoker = (t) => t.c < 0;

// Value of a tile left in a rack at the end of the game.
const rackValue = (t) => (isJoker(t) ? JOKER_PENALTY : t.n);

// tiles: array in left-to-right order.
// Returns {valid: false} or {valid: true, type: "group"|"run", value, n | c+s}.
function analyzeSet(tiles) {
  const len = tiles.length;
  if (len < 3) return { valid: false };
  const real = tiles.filter((t) => !isJoker(t));
  if (!real.length) return { valid: false };
  let group = null;
  let run = null;
  if (len <= 4) {
    const n = real[0].n;
    if (real.every((t) => t.n === n) && new Set(real.map((t) => t.c)).size === real.length)
      group = { valid: true, type: "group", n, value: n * len };
  }
  if (len <= 13) {
    const c = real[0].c;
    if (real.every((t) => t.c === c)) {
      const i0 = tiles.findIndex((t) => !isJoker(t));
      const s = tiles[i0].n - i0;
      if (s >= 1 && s + len - 1 <= 13 && tiles.every((t, i) => isJoker(t) || t.n === s + i))
        run = { valid: true, type: "run", c, s, value: len * s + (len * (len - 1)) / 2 };
    }
  }
  if (group && run) return group.value >= run.value ? group : run;
  return group || run || { valid: false };
}
