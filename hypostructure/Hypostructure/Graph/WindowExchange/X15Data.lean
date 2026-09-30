import Mathlib

/-!
# The graph `X15` as concrete data

`X15` is the 15-vertex graph with graph6 code `N?AA@AODAOP_KGGoGH?`, decoded exactly as
`DensityCert.CG.ofGraph6` decodes it: vertices `0 … 14`, and the vertices `4, 6, 9` are its
three degree-2 vertices (the *exits*).  Its 21 edges are

`0-5 0-8 0-11 1-6 1-10 1-14 2-7 2-12 2-13 3-8 3-9 3-12 4-10 4-11 5-9 5-11 6-13 7-13 7-14
8-12 10-14`

(`x15A_edges`).  The module holds only this data: `x15A` is the symmetrised, loopless Boolean
adjacency on `ℕ`, `x15Graph` the simple graph on `Fin 15`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- The graph6 code of `X15`. -/
def x15Graph6 : String := "N?AA@AODAOP_KGGoGH?"

/-- The upper-triangle adjacency bit of the graph6 code (`i ≠ j`). -/
def x15Raw (i j : ℕ) : Bool :=
  let cs : List ℕ := x15Graph6.toList.map fun c => c.toNat - 63
  let data : Array ℕ := (cs.drop 1).toArray
  let bit : ℕ → Bool := fun k => (data.getD (k / 6) 0).testBit (5 - k % 6)
  if i < j then bit (j * (j - 1) / 2 + i)
  else if j < i then bit (i * (i - 1) / 2 + j) else false

/-- Symmetrised, loopless adjacency of `X15` on `ℕ` (only `0 … 14` carry edges). -/
def x15A (i j : ℕ) : Bool := (i != j) && (x15Raw i j || x15Raw j i)

theorem x15A_symm (i j : ℕ) : x15A i j = x15A j i := by
  unfold x15A
  rw [bne_comm, Bool.or_comm (x15Raw i j)]

theorem x15A_irrefl (i : ℕ) : x15A i i = false := by
  simp [x15A]

/-- `X15` as a simple graph on `Fin 15`. -/
def x15Graph : SimpleGraph (Fin 15) where
  Adj i j := x15A i j = true
  symm := ⟨fun i j h => by simpa [x15A_symm] using h⟩
  loopless := ⟨fun i h => by simp [x15A_irrefl] at h⟩

instance : DecidableRel x15Graph.Adj := fun i j =>
  inferInstanceAs (Decidable (x15A i j = true))

@[simp] theorem x15Graph_adj (i j : Fin 15) : x15Graph.Adj i j ↔ x15A i j = true :=
  Iff.rfl

/-- The three exits (degree-2 vertices) of `X15`. -/
def x15Exits : List ℕ := [4, 6, 9]

/-- The edge list of `X15`, in the labelling of the graph6 code. -/
def x15EdgeList : List (ℕ × ℕ) :=
  [(0, 5), (0, 8), (0, 11), (1, 6), (1, 10), (1, 14), (2, 7), (2, 12), (2, 13), (3, 8),
    (3, 9), (3, 12), (4, 10), (4, 11), (5, 9), (5, 11), (6, 13), (7, 13), (7, 14), (8, 12),
    (10, 14)]

/-- The decoded adjacency is the edge list `x15EdgeList`, and vanishes off `0 … 14`. -/
theorem x15A_edges : ∀ u < 20, ∀ v < 20,
    x15A u v = (x15EdgeList.contains (u, v) || x15EdgeList.contains (v, u)) := by
  native_decide

/-- The exits `4, 6, 9` have degree 2 in `X15`, every other vertex degree 3. -/
theorem x15_degrees : ∀ u < 15,
    ((List.range 15).filter fun v => x15A u v).length = if u ∈ x15Exits then 2 else 3 := by
  native_decide

end Hypostructure.Graph.WindowExchange
