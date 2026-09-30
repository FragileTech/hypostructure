import Hypostructure.Graph.WindowExchange.X15Data
import Hypostructure.Graph.WindowExchange.Transport
import Hypostructure.Core.DyadicLength

/-!
# A copy of `X15` between two windows: the rung search

**Configuration graph.**  `hpA x a y b F` on `0 … 40`: vertices `0 … 14` are a copy of
`X15`, `15 + i` is `P[i]` and `28 + j` is `Q[j]` for two 13-vertex windows `P`, `Q`; the exit
`x` of the copy is joined to `P[a]`, the exit `y` to `Q[b]`, and every pair `(i, j)` of the
rung list `F` is an edge `P[i] — Q[j]`.  The rung `(i, j)` has index `13 i + j < 169`.

**Witnesses.**  A witness against a rung list is a cycle of power-of-two length
(`RWit.cyc`), or a window vertex with four distinct neighbours (`RWit.deg`); `chkRWit`
checks one.  `hpFind` searches for one (untrusted: proofs only use `chkRWit`), and
`wRej cfg sub` holds when the search returns a checked witness against the sub-list `sub`.

**Search.**  `mkTabs` tabulates `wRej` on single rungs, on pairs and on triples of rungs.
`noExtG rej F s k` explores every increasing extension of the accepted list `F` by `k` rung
indices `≥ s`; a candidate `r` is cut when `rej r F` holds.  `tabRej` cuts by the tables, and
from depth `d₀` on also by `wRej` on the whole list.  `noExtG_sound`: if `noExtG` holds, then
every increasing list of `k` indices is cut at some position; `tabRej_sound`: a cut exhibits
a sub-list of the accepted rungs with a checked witness.
-/

namespace Hypostructure.Graph.WindowExchange

/-- A simple path of `X15` from the exit `s` to the exit `t` with `l` edges
(`[]` off the table). -/
def xpath : ℕ → ℕ → ℕ → List ℕ
  | 4, 6, 3 => [4, 10, 1, 6]
  | 4, 6, 4 => [4, 10, 14, 1, 6]
  | 4, 6, 5 => [4, 10, 14, 7, 13, 6]
  | 4, 6, 6 => [4, 10, 1, 14, 7, 13, 6]
  | 4, 6, 7 => [4, 10, 1, 14, 7, 2, 13, 6]
  | 4, 6, 8 => [4, 11, 0, 8, 3, 12, 2, 13, 6]
  | 4, 6, 9 => [4, 11, 0, 5, 9, 3, 12, 2, 13, 6]
  | 4, 6, 10 => [4, 11, 0, 5, 9, 3, 8, 12, 2, 13, 6]
  | 4, 6, 11 => [4, 11, 0, 5, 9, 3, 8, 12, 2, 7, 13, 6]
  | 4, 6, 12 => [4, 11, 0, 5, 9, 3, 8, 12, 2, 7, 14, 1, 6]
  | 4, 6, 13 => [4, 11, 0, 5, 9, 3, 8, 12, 2, 7, 14, 10, 1, 6]
  | 4, 6, 14 => [4, 11, 0, 5, 9, 3, 8, 12, 2, 13, 7, 14, 10, 1, 6]
  | 4, 9, 3 => [4, 11, 5, 9]
  | 4, 9, 4 => [4, 11, 0, 5, 9]
  | 4, 9, 5 => [4, 11, 0, 8, 3, 9]
  | 4, 9, 6 => [4, 11, 0, 8, 12, 3, 9]
  | 4, 9, 7 => [4, 10, 14, 7, 2, 12, 3, 9]
  | 4, 9, 8 => [4, 10, 1, 6, 13, 2, 12, 3, 9]
  | 4, 9, 9 => [4, 10, 1, 6, 13, 2, 12, 8, 3, 9]
  | 4, 9, 10 => [4, 10, 1, 6, 13, 2, 12, 8, 0, 5, 9]
  | 4, 9, 11 => [4, 10, 1, 6, 13, 2, 12, 3, 8, 0, 5, 9]
  | 4, 9, 12 => [4, 10, 1, 6, 13, 2, 12, 3, 8, 0, 11, 5, 9]
  | 4, 9, 13 => [4, 10, 1, 6, 13, 7, 2, 12, 3, 8, 0, 11, 5, 9]
  | 4, 9, 14 => [4, 10, 14, 1, 6, 13, 7, 2, 12, 3, 8, 0, 11, 5, 9]
  | 6, 4, 3 => [6, 1, 10, 4]
  | 6, 4, 4 => [6, 1, 14, 10, 4]
  | 6, 4, 5 => [6, 13, 7, 14, 10, 4]
  | 6, 4, 6 => [6, 13, 2, 7, 14, 10, 4]
  | 6, 4, 7 => [6, 13, 2, 7, 14, 1, 10, 4]
  | 6, 4, 8 => [6, 13, 2, 12, 3, 8, 0, 11, 4]
  | 6, 4, 9 => [6, 1, 14, 7, 2, 12, 8, 0, 11, 4]
  | 6, 4, 10 => [6, 1, 10, 14, 7, 2, 12, 8, 0, 11, 4]
  | 6, 4, 11 => [6, 1, 10, 14, 7, 2, 12, 3, 8, 0, 11, 4]
  | 6, 4, 12 => [6, 1, 10, 14, 7, 2, 12, 3, 8, 0, 5, 11, 4]
  | 6, 4, 13 => [6, 1, 10, 14, 7, 2, 12, 8, 3, 9, 5, 0, 11, 4]
  | 6, 4, 14 => [6, 1, 10, 14, 7, 13, 2, 12, 8, 3, 9, 5, 0, 11, 4]
  | 6, 9, 5 => [6, 13, 2, 12, 3, 9]
  | 6, 9, 6 => [6, 1, 10, 4, 11, 5, 9]
  | 6, 9, 7 => [6, 1, 10, 4, 11, 0, 5, 9]
  | 6, 9, 8 => [6, 1, 10, 4, 11, 0, 8, 3, 9]
  | 6, 9, 9 => [6, 1, 10, 4, 11, 0, 8, 12, 3, 9]
  | 6, 9, 10 => [6, 1, 10, 4, 11, 5, 0, 8, 12, 3, 9]
  | 6, 9, 11 => [6, 1, 10, 14, 7, 2, 12, 3, 8, 0, 5, 9]
  | 6, 9, 12 => [6, 1, 10, 14, 7, 2, 12, 3, 8, 0, 11, 5, 9]
  | 6, 9, 13 => [6, 1, 10, 14, 7, 13, 2, 12, 3, 8, 0, 11, 5, 9]
  | 6, 9, 14 => [6, 13, 2, 7, 14, 1, 10, 4, 11, 5, 0, 8, 12, 3, 9]
  | 9, 4, 3 => [9, 5, 11, 4]
  | 9, 4, 4 => [9, 5, 0, 11, 4]
  | 9, 4, 5 => [9, 3, 8, 0, 11, 4]
  | 9, 4, 6 => [9, 3, 8, 0, 5, 11, 4]
  | 9, 4, 7 => [9, 3, 12, 2, 7, 14, 10, 4]
  | 9, 4, 8 => [9, 3, 8, 12, 2, 7, 14, 10, 4]
  | 9, 4, 9 => [9, 3, 8, 12, 2, 7, 14, 1, 10, 4]
  | 9, 4, 10 => [9, 3, 8, 12, 2, 7, 13, 6, 1, 10, 4]
  | 9, 4, 11 => [9, 3, 8, 12, 2, 7, 13, 6, 1, 14, 10, 4]
  | 9, 4, 12 => [9, 5, 0, 8, 3, 12, 2, 7, 13, 6, 1, 10, 4]
  | 9, 4, 13 => [9, 5, 0, 8, 3, 12, 2, 7, 13, 6, 1, 14, 10, 4]
  | 9, 4, 14 => [9, 5, 11, 0, 8, 3, 12, 2, 7, 13, 6, 1, 14, 10, 4]
  | 9, 6, 5 => [9, 3, 12, 2, 13, 6]
  | 9, 6, 6 => [9, 3, 8, 12, 2, 13, 6]
  | 9, 6, 7 => [9, 3, 8, 12, 2, 7, 13, 6]
  | 9, 6, 8 => [9, 3, 8, 0, 11, 4, 10, 1, 6]
  | 9, 6, 9 => [9, 3, 8, 0, 5, 11, 4, 10, 1, 6]
  | 9, 6, 10 => [9, 3, 8, 0, 5, 11, 4, 10, 14, 1, 6]
  | 9, 6, 11 => [9, 3, 8, 0, 5, 11, 4, 10, 14, 7, 13, 6]
  | 9, 6, 12 => [9, 3, 8, 0, 5, 11, 4, 10, 1, 14, 7, 13, 6]
  | 9, 6, 13 => [9, 3, 8, 0, 5, 11, 4, 10, 1, 14, 7, 2, 13, 6]
  | 9, 6, 14 => [9, 3, 12, 8, 0, 5, 11, 4, 10, 1, 14, 7, 2, 13, 6]
  | _, _, _ => []

/-- Adjacency of the configuration graph. -/
def hpA (x a y b : ℕ) (F : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  if u < 15 then
    if v < 15 then x15A u v
    else (u == x && v == 15 + a) || (u == y && v == 28 + b)
  else if v < 15 then (v == x && u == 15 + a) || (v == y && u == 28 + b)
  else if u < 28 then
    if v < 28 then (u + 1 == v || v + 1 == u)
    else F.contains (u - 15, v - 28)
  else if v < 28 then F.contains (v - 15, u - 28)
  else (u + 1 == v || v + 1 == u)

/-- A witness against a rung list. -/
inductive RWit
  | cyc (l : List ℕ)
  | deg (v : ℕ) (l : List ℕ)

/-- Checker for a witness. -/
def chkRWit (x a y b : ℕ) (F : List (ℕ × ℕ)) : RWit → Bool
  | .cyc l => chkCycle (hpA x a y b F) 41 l &&
      decide (Core.DyadicLength.PowerOfTwoLength l.length)
  | .deg v l => 15 ≤ v && v < 41 && decide l.Nodup && l.all (· < 41) &&
      l.all (hpA x a y b F v) && 4 ≤ l.length

/-- The rung pairs of a list of rung indices. -/
def toPairs (F : List ℕ) : List (ℕ × ℕ) := F.map fun r => (r / 13, r % 13)

/-- Window neighbours of a window vertex. -/
def wNb (F : List (ℕ × ℕ)) (v : ℕ) : List ℕ :=
  if v < 28 then
    (if 15 < v then [v - 1] else []) ++ (if v < 27 then [v + 1] else []) ++
      F.filterMap fun r => if r.1 == v - 15 then some (28 + r.2) else none
  else
    (if 28 < v then [v - 1] else []) ++ (if v < 40 then [v + 1] else []) ++
      F.filterMap fun r => if r.2 == v - 28 then some (15 + r.1) else none

/-- Depth-first search for a simple path to `t` whose number of edges passes `goal`; the
path is built backwards in the accumulator. -/
def pathSearch (nb : ℕ → List ℕ) (t : ℕ) (goal : ℕ → Bool) : ℕ → List ℕ → Option (List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, cur :: rest =>
    if cur == t then (if goal rest.length then some (cur :: rest).reverse else none)
    else (nb cur).findSome? fun w =>
      if (cur :: rest).contains w then none else pathSearch nb t goal fuel (w :: cur :: rest)

/-- Powers of two in range. -/
def pow2 (n : ℕ) : Bool := n == 4 || n == 8 || n == 16 || n == 32 || n == 64

/-- An internal length `l ∈ [lo, 14]` of the copy closing a power-of-two cycle with a window
path of `d` edges. -/
def badLen (lo d : ℕ) : Option ℕ := (List.range' lo (15 - lo)).find? fun l => pow2 (d + l + 2)

/-- Untrusted witness search against the rung list `F`: a window vertex of degree `≥ 4` at a
rung, a window cycle of length `4`, `8` or `16` through a rung, or a window path between the
landings closing a power-of-two cycle through the copy. -/
def hpFind (x a y b lo : ℕ) (F : List (ℕ × ℕ)) : Option RWit :=
  let degW : Option RWit := F.findSome? fun r =>
    let nbP := wNb F (15 + r.1) ++ (if r.1 == a then [x] else [])
    let nbQ := wNb F (28 + r.2) ++ (if r.2 == b then [y] else [])
    if 4 ≤ nbP.length then some (.deg (15 + r.1) nbP)
    else if 4 ≤ nbQ.length then some (.deg (28 + r.2) nbQ) else none
  match degW with
  | some w => some w
  | none =>
    let cycW : Option RWit := F.findSome? fun r =>
      (pathSearch (wNb (F.erase r)) (28 + r.2) (fun d => d == 3 || d == 7 || d == 15) 17
        [15 + r.1]).map RWit.cyc
    match cycW with
    | some w => some w
    | none =>
      match pathSearch (wNb F) (28 + b) (fun d => (badLen lo d).isSome) 28 [15 + a] with
      | some w =>
        match badLen lo (w.length - 1) with
        | some l => some (.cyc (w ++ xpath y x l))
        | none => none
      | none => none

/-- The rung-index list `sub` is refuted by a checked witness. -/
def wRej (lo x a y b : ℕ) (sub : List ℕ) : Bool :=
  match hpFind x a y b lo (toPairs sub) with
  | some w => chkRWit x a y b (toPairs sub) w
  | none => false

/-- Rejection tables of one configuration: single rungs (by index), and pairs and triples
of the admitted single rungs (by position in `allowed`). -/
structure Tabs where
  single : Array Bool
  allowed : Array ℕ
  pos : Array ℕ
  pair : Array Bool
  trip : Array Bool

/-- Single-rung table: `wRej` on `[r]`. -/
def tSingle (lo x a y b : ℕ) : Array Bool := Array.ofFn (n := 169) fun r => wRej lo x a y b [r.1]

/-- The admitted single rungs, in increasing order. -/
def tAllowed (single : Array Bool) : Array ℕ :=
  ((List.range 169).filter fun r => !single.getD r true).toArray

/-- Pair table over positions `(i, j)`, `j < i`, of admitted rungs (index `i·m + j`). -/
def tPair (lo x a y b : ℕ) (allowed : Array ℕ) : Array Bool :=
  Array.ofFn (n := allowed.size * allowed.size) fun k =>
    decide (k.1 % allowed.size < k.1 / allowed.size) &&
      wRej lo x a y b [allowed.getD (k.1 / allowed.size) 0, allowed.getD (k.1 % allowed.size) 0]

/-- Triple table over positions `(i, j, l)`, `l < j < i`, of admitted rungs whose three pairs
pass the pair table (index `i·m² + j·m + l`). -/
def tTrip (lo x a y b : ℕ) (allowed : Array ℕ) (pair : Array Bool) : Array Bool :=
  let m := allowed.size
  Array.ofFn (n := m * m * m) fun k =>
    (decide (k.1 % m < k.1 / m % m) && decide (k.1 / m % m < k.1 / (m * m)) &&
      !pair.getD (k.1 / (m * m) * m + k.1 / m % m) true &&
      !pair.getD (k.1 / (m * m) * m + k.1 % m) true &&
      !pair.getD (k.1 / m % m * m + k.1 % m) true) &&
    wRej lo x a y b [allowed.getD (k.1 / (m * m)) 0, allowed.getD (k.1 / m % m) 0,
      allowed.getD (k.1 % m) 0]

/-- Build the tables. -/
def mkTabs (lo x a y b : ℕ) : Tabs :=
  let single := tSingle lo x a y b
  let allowed := tAllowed single
  let pos := Array.ofFn (n := 169) fun r => allowed.toList.idxOf r.1
  let pair := tPair lo x a y b allowed
  ⟨single, allowed, pos, pair, tTrip lo x a y b allowed pair⟩

/-- Table cut of the pair `r > s`: the table entry at the positions of `r`, `s` is set, and
it decodes back to `r`, `s`. -/
def pairHit (T : Tabs) (r s : ℕ) : Bool :=
  let m := T.allowed.size
  let k := T.pos.getD r 0 * m + T.pos.getD s 0
  T.pair.getD k false && T.allowed.getD (k / m) 0 == r && T.allowed.getD (k % m) 0 == s

/-- Table cut of the triple `r > s > t`, decoded as in `pairHit`. -/
def tripHit (T : Tabs) (r s t : ℕ) : Bool :=
  let m := T.allowed.size
  let k := T.pos.getD r 0 * m * m + T.pos.getD s 0 * m + T.pos.getD t 0
  T.trip.getD k false && T.allowed.getD (k / (m * m)) 0 == r &&
    T.allowed.getD (k / m % m) 0 == s && T.allowed.getD (k % m) 0 == t

/-- Some pair `(s, t)` of the list (`s` before `t`) passes `f`. -/
def anyPair (f : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => false
  | s :: F => F.any (f s) || anyPair f F

/-- The cut of a candidate `r` against the accepted list `F` (newest first). -/
def tabRej (lo x a y b d₀ : ℕ) (T : Tabs) (r : ℕ) (F : List ℕ) : Bool :=
  T.single.getD r false || F.any (pairHit T r) || anyPair (tripHit T r) F ||
    (d₀ ≤ F.length + 1 && wRej lo x a y b (r :: F))

/-- Every increasing extension of `F` by `k` rung indices `≥ s` meets a cut. -/
def noExtG (rej : ℕ → List ℕ → Bool) : List ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | F, s, k + 1 => (List.range' s (169 - s)).all fun r =>
      rej r F || noExtG rej (r :: F) (r + 1) k

/-- The certificate of one configuration: no increasing list of `k` rungs survives. -/
def certCfg (lo x a y b d₀ k : ℕ) : Bool :=
  let T := mkTabs lo x a y b
  noExtG (tabRej lo x a y b d₀ T) [] 0 k

end Hypostructure.Graph.WindowExchange
