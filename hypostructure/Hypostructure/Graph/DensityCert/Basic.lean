import Mathlib

/-!
# Density certificate: shared vocabulary

Proof-agnostic definitions for the density theorem

  *a connected, subcubic finite graph with no cycle of length 4, 8, 16 or 32 and
  no induced path on 13 vertices satisfies `8 e ≤ 11 n`, unless it is
  isomorphic to the 15-vertex graph `X15`.*

Everything is stated relative to a finset `W` of an ambient vertex type, so an
induced subgraph is just a smaller finset.  Paths and cycles are vertex lists.

* `IsIndPath G l`: `l` is an induced path of `G` (distinct vertices, adjacent
  exactly when consecutive).
* `IsCycleList G l`: `l` lists the vertices of a cycle of `G` in order.
* `AdmIn G W`: `G[W]` is subcubic, has no cycle of length 4, 8, 16, 32 and no
  induced path on 13 vertices.
* `ConnIn`, `TwoConnIn`: connectivity and 2-connectivity of `G[W]`.
* `dIn G W = 4·#{ordered adjacent pairs in W} − 11·|W| = 8 e(G[W]) − 11 |W|`.
* `lamIn G W v`: the largest number of vertices of an induced path of `G[W]`
  starting at `v`; `LIn G W u v`: the same for induced `u`–`v` paths.

The concrete side: `CG` is a computable graph on `{0, …, n-1}` given by a Boolean
adjacency function; `CG.graph` is its `SimpleGraph (Fin n)`, and `CG.ear` is
the ear extension used by the closure certificate.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

section Generic

variable {V : Type*}

/-- `l` is an induced path of `G`: distinct vertices, and two entries are
adjacent exactly when their positions are consecutive. -/
def IsIndPath (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
    (G.Adj l[i] l[j] ↔ (i + 1 = j ∨ j + 1 = i))

/-- `l` lists, in cyclic order, the vertices of a cycle of `G` (at least three
distinct vertices, consecutive entries adjacent, last adjacent to first).
Chords are allowed. -/
def IsCycleList (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ 3 ≤ l.length ∧ (∀ (i : ℕ) (h : i + 1 < l.length), G.Adj l[i] l[i + 1]) ∧
    ∀ h : 0 < l.length, G.Adj l[l.length - 1] l[0]

/-- The forbidden cycle lengths. -/
def forbiddenLen (k : ℕ) : Prop := k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32

instance : DecidablePred forbiddenLen := fun _ => by unfold forbiddenLen; infer_instance

/-- Reachability inside `W`. -/
def ReachIn (G : SimpleGraph V) (W : Finset V) : V → V → Prop :=
  Relation.ReflTransGen fun a b => a ∈ W ∧ b ∈ W ∧ G.Adj a b

/-- `G[W]` is connected (and nonempty). -/
def ConnIn (G : SimpleGraph V) (W : Finset V) : Prop :=
  W.Nonempty ∧ ∀ u ∈ W, ∀ v ∈ W, ReachIn G W u v

/-- `G[W]` is 2-connected in the sense: at least two vertices, connected, and
connected after deleting any one vertex (so `K₂` counts). -/
def TwoConnIn [DecidableEq V] (G : SimpleGraph V) (W : Finset V) : Prop :=
  2 ≤ W.card ∧ ConnIn G W ∧ ∀ v ∈ W, ConnIn G (W.erase v)

open Classical in
/-- Degree of `v` inside `G[W]`. -/
noncomputable def degIn (G : SimpleGraph V) (W : Finset V) (v : V) : ℕ :=
  (W.filter fun w => G.Adj v w).card

/-- `G[W]` is admissible: subcubic, no cycle of length 4, 8, 16, 32, no induced
path on 13 vertices. -/
def AdmIn (G : SimpleGraph V) (W : Finset V) : Prop :=
  (∀ v ∈ W, degIn G W v ≤ 3) ∧
    (∀ l : List V, (∀ x ∈ l, x ∈ W) → IsCycleList G l → ¬ forbiddenLen l.length) ∧
    (∀ l : List V, (∀ x ∈ l, x ∈ W) → IsIndPath G l → l.length ≠ 13)

open Classical in
/-- `dIn G W = 4·#{(u,v) ∈ W×W : u ~ v} − 11|W| = 8 e(G[W]) − 11 |W|`. -/
noncomputable def dIn (G : SimpleGraph V) (W : Finset V) : ℤ :=
  4 * ((W ×ˢ W).filter fun p => G.Adj p.1 p.2).card - 11 * W.card

open Classical in
/-- The largest number of vertices of an induced path of `G[W]` that starts at
`v` (`0` when `v ∉ W`). -/
noncomputable def lamIn (G : SimpleGraph V) (W : Finset V) (v : V) : ℕ :=
  Nat.findGreatest
    (fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some v ∧ l.length = k)
    W.card

open Classical in
/-- The largest number of vertices of an induced `u`–`v` path of `G[W]`. -/
noncomputable def LIn (G : SimpleGraph V) (W : Finset V) (u v : V) : ℕ :=
  Nat.findGreatest
    (fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some u ∧
      l.getLast? = some v ∧ l.length = k)
    W.card

/-- `G[W]` is a copy of `H`: an induced embedding of `H` into `G` whose image is
exactly `W`. -/
def EmbOnto {U : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∃ e : H ↪g G, ∀ v, v ∈ W ↔ ∃ i, e i = v

end Generic

/-! ## The rooted density table -/

/-- `fTab l`: the largest value of `8e − 11n` of a connected admissible graph
rooted at a vertex of degree `≤ 2` from which every induced path has `≤ l`
vertices (`l = 1, …, 12`); constant `3` above 12. -/
def fTab (l : ℕ) : ℤ :=
  match l with
  | 0 => -11 | 1 => -11 | 2 => -9 | 3 => -9 | 4 => -8 | 5 => -5 | 6 => -5
  | 7 => -3 | 8 => -2 | 9 => 0 | 10 => 0 | _ => 3

/-! ## Concrete graphs -/

/-- A computable graph on `{0, …, n-1}` given by a Boolean adjacency function
(only its symmetrisation off the diagonal matters). -/
structure CG where
  n : ℕ
  adj : ℕ → ℕ → Bool

namespace CG

/-- Symmetrised, loopless adjacency. -/
def A (M : CG) (i j : ℕ) : Bool := (i != j) && (M.adj i j || M.adj j i)

theorem A_symm (M : CG) (i j : ℕ) : M.A i j = M.A j i := by
  unfold A
  rw [bne_comm, Bool.or_comm (M.adj i j)]

theorem A_irrefl (M : CG) (i : ℕ) : M.A i i = false := by
  simp [A]

/-- The simple graph of a concrete graph. -/
def graph (M : CG) : SimpleGraph (Fin M.n) where
  Adj i j := M.A i j = true
  symm := ⟨fun i j h => by simpa [A_symm] using h⟩
  loopless := ⟨fun i h => by simp [A_irrefl] at h⟩

instance (M : CG) : DecidableRel M.graph.Adj := fun i j =>
  inferInstanceAs (Decidable (M.A i j = true))

@[simp] theorem graph_adj (M : CG) (i j : Fin M.n) : M.graph.Adj i j ↔ M.A i j = true :=
  Iff.rfl

/-- Ear extension of `M` by `m ≥ 1` new vertices `M.n, …, M.n + m - 1` forming a
path `q₀ … q_{m-1}`; `q₀ ~ x`, `q_{m-1} ~ y`, and, when `m = 1`, optionally also
`q₀ ~ z`.  No other new edges. -/
def ear (M : CG) (m x y : ℕ) (z : Option ℕ) : CG where
  n := M.n + m
  adj i j :=
    if i < M.n then
      if j < M.n then M.A i j
      else
        ((j - M.n == 0) && (i == x)) || ((j - M.n + 1 == m) && (i == y)) ||
          ((m == 1) && (z == some i))
    else if j < M.n then false
    else i + 1 == j

/-- Decode a graph6 string (at most 62 vertices). -/
def ofGraph6 (s : String) : CG :=
  let cs : List ℕ := s.toList.map fun c => c.toNat - 63
  let data : Array ℕ := (cs.drop 1).toArray
  let bit : ℕ → Bool := fun k => (data.getD (k / 6) 0).testBit (5 - k % 6)
  { n := cs.headD 0
    adj := fun i j =>
      if i < j then bit (j * (j - 1) / 2 + i)
      else if j < i then bit (i * (i - 1) / 2 + j) else false }

/-- The complete graph `K₂`. -/
def K2 : CG := ⟨2, fun _ _ => true⟩

/-- The exceptional 15-vertex graph `X15` (21 edges, `8e − 11n = 3`). -/
def x15 : CG := ofGraph6 "N?AA@AODAOP_KGGoGH?"

end CG

/-! ## Certificate statements (proved by the checker, consumed by the pen proof) -/

section Cert

/-- Closure of a list `L` of concrete graphs under admissible ear extensions of
at most 11 new vertices: every ear extension is inadmissible or isomorphic to a
member of `L`. -/
def ClosureCert (L : List CG) : Prop :=
  ∀ M ∈ L, ∀ m, 1 ≤ m → m ≤ 11 → ∀ x < M.n, ∀ y < M.n, x ≠ y → ∀ z : Option ℕ,
    (2 ≤ m → z = none) → (∀ w, z = some w → w < M.n ∧ w ≠ x ∧ w ≠ y) →
    ¬ AdmIn (M.ear m x y z).graph Finset.univ ∨
      ∃ M' ∈ L, Nonempty ((M.ear m x y z).graph ≃g M'.graph)

/-- The block profile inequalities of the tree DP, for every member of `L`. -/
def DPCert (L : List CG) : Prop :=
  ∀ M ∈ L,
    let lam := fun i => lamIn M.graph Finset.univ i
    let LL := fun i j => LIn M.graph Finset.univ i j
    let deg := fun i => degIn M.graph Finset.univ i
    let d := dIn M.graph Finset.univ
    -- unrooted: a block centre with no children
    (d ≤ 0 ∨ Nonempty (M.graph ≃g CG.x15.graph)) ∧
    -- rooted, no child
    (∀ r, deg r ≤ 2 → d ≤ fTab (lam r)) ∧
    -- rooted, one child of value `t ≥ 5` at port `p`
    (∀ r p, p ≠ r → deg r ≤ 2 → deg p ≤ 2 → ∀ t, 5 ≤ t → t ≤ 12 →
      lam p + t ≤ 12 → max (lam r) (LL r p + t) ≤ 12 →
      d + fTab t + 8 ≤ fTab (max (lam r) (LL r p + t))) ∧
    -- rooted, two children of values `a, b ≥ 5` at ports `p ≠ q`
    (∀ r p q, p ≠ r → q ≠ r → p ≠ q → deg r ≤ 2 → deg p ≤ 2 → deg q ≤ 2 →
      ∀ a b, 5 ≤ a → a ≤ 12 → 5 ≤ b → b ≤ 12 →
      lam p + a ≤ 12 → lam q + b ≤ 12 → a + LL p q + b ≤ 12 →
      max (lam r) (max (LL r p + a) (LL r q + b)) ≤ 12 →
      d + fTab a + fTab b + 16 ≤ fTab (max (lam r) (max (LL r p + a) (LL r q + b)))) ∧
    -- no three ports (other than the root) pairwise joined by induced paths of ≤ 2 vertices
    (∀ r p q s, p ≠ r → q ≠ r → s ≠ r → p ≠ q → p ≠ s → q ≠ s →
      deg p ≤ 2 → deg q ≤ 2 → deg s ≤ 2 →
      ¬ (LL p q ≤ 2 ∧ LL p s ≤ 2 ∧ LL q s ≤ 2))

end Cert

end Hypostructure.Graph.DensityCert
