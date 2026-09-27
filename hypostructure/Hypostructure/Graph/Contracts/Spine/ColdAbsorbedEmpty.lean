import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Contracts.Spine.ColdGermRouting
import Hypostructure.Graph.Contracts.Spine.ColdMass

/-!
# Contracts: node `[176]` on the empty arm of `[175]`/`[177]`

`lem:absorbed-germ-fan-data` read at G on the arm where node `[175]` finds no
positive germ and node `[177]` no absorbed half-edge.  Proof-agnostic contract
lemma over a `Graph.FiniteObject` with the registered `Parameters`; it imports
no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[176]` on the empty arm.**  With no candidate (the `[175]` no arm)
and every selected corridor subcubic (the `[177]` absent arm), G has no
selected branch-excess half-edge: an outside one would be a candidate, and a
cross-window one always is (`coldCrossWindow_mem_candidates`).  By
`def:cold-skeleton-excess` (nine selected half-edges per ambient-cubic cold
window, `coldSelectedBranchExcess_of_split`) G has no ambient-cubic cold
window. -/
theorem coldSelectedFamilyEmpty_of_absent (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (thresholdEq : data.threshold = 3)
    (fiveLeOrder : 5 ≤ data.windowOrder)
    (split : HotColdWindowStatement data object)
    (routing : ColdFailureRoutingStatement data object)
    (noPositive : ColdNoPositiveGermStatement data object)
    (absent : TypeBAbsorbedHalfEdgeAbsentStatement data object) :
    ColdSelectedFamilyEmptyStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have emptyCandidates : coldRoutedCandidates data object routing = ∅ := by
    by_contra nonempty
    exact noPositive ⟨routing,
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonempty)⟩
  have noOutside : ∀ epsilon : ColdEligibleHalfEdge data object,
      Sum.inl epsilon ∈ coldRoutedCandidates data object routing := by
    intro epsilon
    by_contra outside
    exact (canonicalChoice_eq_none_iff.mp absent) ⟨epsilon, routing, outside⟩
  have selectedEmpty :
      Graph.ColdCorridor.allSelectedStubs object
        ((canonicalColdWindows data object).filter
          (AmbientCubicWindow data object)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro stub member
    by_cases inWindows : stub.2 ∈ coldCorridorWindows data object
    · have cross := coldCrossWindow_mem_candidates data object routing
        ⟨stub, member, inWindows⟩
      rw [emptyCandidates] at cross
      exact Finset.notMem_empty _ cross
    · have outside := noOutside ⟨stub, member, inWindows⟩
      rw [emptyCandidates] at outside
      exact Finset.notMem_empty _ outside
  refine ⟨selectedEmpty, ?_⟩
  have excess := (coldSelectedBranchExcess_of_split data object thresholdEq
    (le_trans (by norm_num) fiveLeOrder) split).1
  change (Graph.ColdCorridor.allSelectedStubs object
      ((canonicalColdWindows data object).filter
        (AmbientCubicWindow data object))).card =
    coldInteriorBranchExcess data *
      ((canonicalColdWindows data object).filter
        (AmbientCubicWindow data object)).card at excess
  rw [selectedEmpty, Finset.card_empty] at excess
  have perWindowPos : 0 < coldInteriorBranchExcess data := by
    simp only [coldInteriorBranchExcess, Graph.ColdCorridor.branchExcessOf]
    omega
  have cardZero : ((canonicalColdWindows data object).filter
      (AmbientCubicWindow data object)).card = 0 := by
    rcases Nat.mul_eq_zero.mp excess.symm with zero | zero
    · omega
    · exact zero
  exact Finset.card_eq_zero.mp cardZero

end Hypostructure.Graph.Contracts.Spine
