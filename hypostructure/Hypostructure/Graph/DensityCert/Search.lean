import Hypostructure.Graph.DensityCert.Data

/-!
# Density certificate: witness search and the per-member check

Untrusted search code producing the witnesses consumed by `closureOK` and `dpOK`:
simple paths (forbidden cycles through an ear), induced paths on 13 vertices,
isomorphism records decoded from a witness string, and longest induced paths.
None of it is trusted: `memberOK_sound` holds for every output of the searches.
-/

namespace Hypostructure.Graph.DensityCert

namespace CertSearch

open CertCheck

/-- Neighbour lists of `M`. -/
def nbrs (M : CG) : Array (List ℕ) :=
  Array.ofFn fun v : Fin M.n => (List.range M.n).filter fun w => M.A v w

/-- Neighbour bitmasks from neighbour lists. -/
def masks (nb : Array (List ℕ)) : Array ℕ :=
  nb.map fun l => l.foldl (fun acc u => acc ||| (1 <<< u)) 0

/-- Simple-path enumeration from a fixed start: `acc[t * 32 + k]` receives the first
path found with `k` vertices ending at `t` (stored from `t` back to the start). -/
def spDFS (nb : Array (List ℕ)) : ℕ → ℕ → ℕ → ℕ → List ℕ → Array (List ℕ) → Array (List ℕ)
  | 0, _, _, _, _, acc => acc
  | fuel + 1, v, on, k, path, acc =>
    let idx := v * 32 + k
    let acc := if (acc.getD idx []).isEmpty then acc.set! idx path else acc
    (nb.getD v []).foldl (fun acc u =>
      if on.testBit u then acc else spDFS nb fuel u (on ||| (1 <<< u)) (k + 1) (u :: path) acc) acc

/-- For one target: a set of stored paths covering every `m ≤ 11` for which some
stored length closes a forbidden cycle. -/
def pickPaths (found : Array (List ℕ)) (t : ℕ) : List (List ℕ) :=
  let ks := (List.range 11).filterMap fun m' =>
    (List.range' 2 21).find? fun k => forbB (m' + 1 + k) && !(found.getD (t * 32 + k) []).isEmpty
  ks.eraseDups.map fun k => found.getD (t * 32 + k) []

/-- `pathTable M nb`: entry `[b][a]` lists candidate paths from `a` to `b`
(only for `b` of degree at most 2). -/
def pathTable (M : CG) (nb : Array (List ℕ)) : Array (Array (List (List ℕ))) :=
  Array.ofFn fun b : Fin M.n =>
    if (nb.getD b []).length ≤ 2 then
      let found := spDFS nb (M.n + 1) b (1 <<< b.1) 1 [b.1] (Array.replicate (M.n * 32 + 32) [])
      Array.ofFn fun a : Fin M.n => pickPaths found a
    else Array.replicate M.n []

/-- Neighbour lists of the ear extension. -/
def earNbrs (nb : Array (List ℕ)) (n m x y : ℕ) (z : Option ℕ) : Array (List ℕ) :=
  Array.ofFn fun v : Fin (n + m) =>
    if v.1 < n then
      nb.getD v [] ++ (if v.1 == x then [n] else []) ++ (if v.1 == y then [n + m - 1] else []) ++
        (if z == some v.1 then [n] else [])
    else
      let k := v.1 - n
      (if 0 < k then [v.1 - 1] else []) ++ (if k + 1 < m then [v.1 + 1] else []) ++
        (if k == 0 then [x] else []) ++ (if k + 1 == m then [y] else []) ++
        (if k == 0 then (match z with | some w => [w] | none => []) else [])

/-- Depth-first search for an induced path with 13 vertices (stored reversed). -/
def ipDFS (nb : Array (List ℕ)) (nbm : Array ℕ) :
    ℕ → ℕ → ℕ → List ℕ → ℕ → Option (List ℕ)
  | 0, _, _, _, _ => none
  | fuel + 1, v, forbid, path, len =>
    if 13 ≤ len then some path else
    let f2 := forbid ||| nbm.getD v 0
    (nb.getD v []).findSome? fun u =>
      if forbid.testBit u then none else ipDFS nb nbm fuel u (f2 ||| (1 <<< u)) (u :: path) (len + 1)

/-- An induced 13-vertex path of the ear extension, searched from the ear first. -/
def findP13 (nb : Array (List ℕ)) (n m x y : ℕ) (z : Option ℕ) : Option (List ℕ) :=
  let nbE := earNbrs nb n m x y z
  let nbm := masks nbE
  (List.range' n m ++ List.range n).findSome? fun s => ipDFS nbE nbm 14 s (1 <<< s) [s] 1

/-- An isomorphism record: ear `(m, x, y, z)` (with `z` coded as `0` or `w + 1`),
target index `k`, and the vertex map `π`. -/
structure Rec where
  m : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  k : ℕ
  π : Array ℕ

/-- Decode the records of one member (characters offset by 63). -/
def parseRecs (n : ℕ) (s : String) : List Rec :=
  let rec go : ℕ → List ℕ → List Rec
    | 0, _ => []
    | fuel + 1, m :: x :: y :: z :: k1 :: k2 :: k3 :: rest =>
      let N := n + m
      ⟨m, x, y, z, k1 * 4096 + k2 * 64 + k3, (rest.take N).toArray⟩ :: go fuel (rest.drop N)
    | _ + 1, _ => []
  go (s.length + 1) (s.toList.map fun c => c.toNat - 63)

/-- The witness for ear `(m, a, b, z)`: an isomorphism record (for `m ≥ 2` and
`a > b` the record of `(m, b, a)` composed with the ear reversal), else an induced
path on 13 vertices. -/
def finder (nb : Array (List ℕ)) (n : ℕ) (recs : List Rec) (m a b : ℕ) (z : Option ℕ) : Wit :=
  let zc := match z with | some w => w + 1 | none => 0
  let (x, y, rev) := if m ≥ 2 && b < a then (b, a, true) else (a, b, false)
  match recs.find? (fun r => r.m == m && r.x == x && r.y == y && r.z == zc) with
  | some r =>
    if rev then
      .iso r.k (Array.ofFn fun i : Fin (n + m) =>
        r.π.getD (if i.1 < n then i.1 else 2 * n + m - 1 - i.1) 0)
    else .iso r.k r.π
  | none =>
    match findP13 nb n m a b z with
    | some l => .ip l
    | none => .none

/-- Longest induced paths from a fixed start: for each end vertex, the longest path
found (stored reversed) and its number of vertices. -/
def lpDFS (nb : Array (List ℕ)) (nbm : Array ℕ) :
    ℕ → ℕ → ℕ → List ℕ → ℕ → Array (List ℕ) × Array ℕ → Array (List ℕ) × Array ℕ
  | 0, _, _, _, _, acc => acc
  | fuel + 1, v, forbid, path, len, acc =>
    let acc := if acc.2.getD v 0 < len then (acc.1.set! v path, acc.2.set! v len) else acc
    let f2 := forbid ||| nbm.getD v 0
    (nb.getD v []).foldl (fun acc u =>
      if forbid.testBit u then acc else lpDFS nb nbm fuel u (f2 ||| (1 <<< u)) (u :: path) (len + 1) acc)
      acc

/-- For every start of degree at most 2: longest induced paths to every end vertex
(`[r][t]`, from `r` to `t`) and the longest one overall. -/
def lpTable (M : CG) (nb : Array (List ℕ)) : Array (Array (List ℕ)) × Array (List ℕ) :=
  let nbm := masks nb
  let tab : Array (Array (List ℕ)) := Array.ofFn fun r : Fin M.n =>
    if (nb.getD r []).length ≤ 2 then
      let res := lpDFS nb nbm (M.n + 1) r (1 <<< r.1) [r.1] 1
        (Array.replicate M.n [], Array.replicate M.n 0)
      res.1.map List.reverse
    else Array.replicate M.n []
  let best : Array (List ℕ) := tab.map fun row =>
    row.foldl (fun b l => if b.length < l.length then l else b) []
  (tab, best)

/-- The isomorphism `X15`-member → `CG.x15` (member index 1763). -/
def x15wit (i : ℕ) : Array ℕ :=
  if i == 1763 then #[4, 6, 9, 12, 2, 8, 7, 0, 14, 3, 13, 10, 11, 5, 1] else #[]

/-- The full check of member `i` of `L`, with its isomorphism-record string. -/
def memberOK (L : Array CG) (i : ℕ) (recStr : String) : Bool :=
  let M := L.getD i CG.K2
  let nb := nbrs M
  let pt := pathTable M nb
  let recs := parseRecs M.n recStr
  let lp := lpTable M nb
  closureOK L M (fun a b => (pt.getD b #[]).getD a []) (finder nb M.n recs) &&
    dpOK M (x15wit i) (fun r => lp.2.getD r []) (fun r p => (lp.1.getD r #[]).getD p [])

/-- The body of `ClosureCert` for one member. -/
def ClosureBody (L : List CG) (M : CG) : Prop :=
  ∀ m, 1 ≤ m → m ≤ 11 → ∀ x < M.n, ∀ y < M.n, x ≠ y → ∀ z : Option ℕ,
    (2 ≤ m → z = none) → (∀ w, z = some w → w < M.n ∧ w ≠ x ∧ w ≠ y) →
    ¬ AdmIn (M.ear m x y z).graph Finset.univ ∨
      ∃ M' ∈ L, Nonempty ((M.ear m x y z).graph ≃g M'.graph)

theorem memberOK_sound {L : Array CG} {i : ℕ} {s : String} (h : memberOK L i s = true) :
    ClosureBody L.toList (L.getD i CG.K2) ∧ DPBody (L.getD i CG.K2) := by
  unfold memberOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨closureOK_sound h.1, dpOK_sound h.2⟩

/-- The check of the members with indices in `[a, b)`; line `j` of `W` holds the
isomorphism records of member `a + j`. -/
def rangeOK (L : Array CG) (a b : ℕ) (W : String) : Bool :=
  let ws := (W.splitOn "\n").toArray
  (List.range' a (b - a)).all fun i => memberOK L i (ws.getD (i - a) "")

theorem rangeOK_sound {L : Array CG} {a b : ℕ} {W : String} (h : rangeOK L a b W = true) :
    ∀ i, a ≤ i → i < b → ClosureBody L.toList (L.getD i CG.K2) ∧ DPBody (L.getD i CG.K2) := by
  intro i hai hib
  simp only [rangeOK, List.all_eq_true, List.mem_range'_1] at h
  exact memberOK_sound (h i ⟨hai, by omega⟩)

end CertSearch

end Hypostructure.Graph.DensityCert
