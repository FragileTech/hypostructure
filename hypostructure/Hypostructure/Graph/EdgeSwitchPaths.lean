import Hypostructure.Graph.ReadingProfiles

/-!
# A non-adjacent neighbour of a high vertex

A vertex `h` of degree at least `k + 1` has a neighbour that is neither a given
vertex `c` of degree `k` nor adjacent to it: the input the two-edge and
same-vertex switches (`Graph/SwitchForcedPaths.lean`) need at a high/baseline
edge.  Vocabulary-free.
-/

namespace Hypostructure.Graph.EdgeSwitchPaths

open Hypostructure
open Hypostructure.Graph
open Classical

universe u

variable {object : FiniteObject.{u}}

/-- A vertex `c` of degree `k` and a vertex `h` of degree `≥ k + 1`: some
neighbour `u` of `h` is neither `c` nor adjacent to `c`. -/
theorem exists_nonadj_nbr {k : Nat} {c h : object.Vertex}
    (dc : object.degree c = k) (dh : k + 1 ≤ object.degree h) :
    ∃ u, object.graph.Adj h u ∧ u ≠ c ∧ ¬ object.graph.Adj c u := by
  letI : Finite object.Vertex := by letI := object.vertices; infer_instance
  by_contra none
  push Not at none
  rw [FiniteObject.degree_eq_ncard_neighborSet] at dc dh
  by_cases ch : object.graph.Adj h c
  · have sub : object.graph.neighborSet h ⊆ insert c (object.graph.neighborSet c \ {h}) := by
      intro u hu
      by_cases uc : u = c
      · exact Or.inl uc
      · exact Or.inr ⟨none u hu uc, fun e => object.graph.irrefl
          (show object.graph.Adj h h from (Set.mem_singleton_iff.1 e) ▸ hu)⟩
    have c1 := (Set.ncard_le_ncard sub (Set.toFinite _)).trans (Set.ncard_insert_le _ _)
    have c2 := Set.ncard_sdiff_singleton_add_one
      (show h ∈ object.graph.neighborSet c from ch.symm) (Set.toFinite _)
    omega
  · have sub : object.graph.neighborSet h ⊆ object.graph.neighborSet c := by
      intro u hu
      have uc : u ≠ c := fun e => ch (e ▸ hu)
      exact none u hu uc
    have := Set.ncard_le_ncard sub (Set.toFinite _)
    omega

end Hypostructure.Graph.EdgeSwitchPaths
