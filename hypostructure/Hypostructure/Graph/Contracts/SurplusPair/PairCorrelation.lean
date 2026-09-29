import Hypostructure.Graph.Statements.PairCorrelation
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap

/-!
# Contract lemmas: the correlation mass at node `[178]`

The count failure of G's pair code, read as an exact accounting of correlation
in G's labelled `(n,m)` class.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The class of the skeleton model has the manuscript's binomial count. -/
theorem card_skeleton_toSkeletonModel (system : PairOverlapSystem data object) :
    Nat.card system.toSkeletonModel.Skeleton = Graph.skeletonBudget object := by
  dsimp [Graph.SparsePairSkeletonModel.Skeleton]
  simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
    Graph.PackedWindowRealization.card_skeleton object.vertexCount object.edgeCount

/-- **Node `[178]`: the correlation profile of every pair overlap system.**  The
count failure `¬ 2^{b + index + 1} ≤ |class|` of the first failure leaves a
positive correlation mass along the canonical exposure order, with a first
non-branching index. -/
theorem correlationProfile_of_system (system : PairOverlapSystem data object) :
    system.CorrelationProfile := by
  classical
  let P := Graph.SparsePairSkeletonModel.signatureCount (LengthOK := data.LengthOK)
    system.toSkeletonModel system.failedFamily system.failedOrder
  have step : ∀ k, P k ≤ P (k + 1) ∧ P (k + 1) ≤ 2 * P k := fun k =>
    ⟨Graph.SparsePairSkeletonModel.signatureCount_le_succ _ _ _ k,
      Graph.SparsePairSkeletonModel.signatureCount_succ_le _ _ _ k⟩
  have zero : P 0 = 2 ^ system.first.baselineFamily.card :=
    Graph.SparsePairSkeletonModel.signatureCount_zero _ _ _
  have classCard := card_skeleton_toSkeletonModel system
  have top : P system.failedFamily.card ≤ Graph.skeletonBudget object := by
    have := Graph.SparsePairSkeletonModel.signatureCount_le_class
      (LengthOK := data.LengthOK) system.toSkeletonModel system.failedFamily
      system.failedOrder system.failedFamily.card
    rw [classCard] at this
    exact this
  have mass := Graph.SparsePairSkeletonModel.two_pow_le_class_add_mass
    (LengthOK := data.LengthOK) system.toSkeletonModel system.failedFamily
    system.failedOrder system.failedFamily.card
  rw [classCard] at mass
  have failure : P system.failedFamily.card <
      2 ^ system.failedFamily.card * P 0 := by
    have small : Graph.skeletonBudget object <
        2 ^ (system.first.baselineFamily.card + system.failedFamily.card) := by
      rw [system.failedFamily_card]
      exact Nat.lt_of_not_ge system.first.firstFailure.failedNext
    rw [zero, ← pow_add, add_comm]
    exact lt_of_le_of_lt top small
  refine ⟨⟨system.failedFamily_card, zero, fun k _ => step k, top, mass,
    ?_⟩, ?_, ?_⟩
  · obtain ⟨k, hk, hfree, hcorr⟩ := Graph.SparsePairSkeletonModel.exists_first_nonbranching P
      system.failedFamily.card (fun k _ => (step k).2) failure
    exact ⟨k, hk, hfree, hcorr,
      Graph.SparsePairSkeletonModel.exists_forbidden_extension (LengthOK := data.LengthOK)
        system.toSkeletonModel system.failedFamily system.failedOrder k hcorr⟩
  · have real := system.first.firstFailure.realizedThrough
      system.first.firstFailure.index le_rfl
    have cardEq := system.failedFamily_card
    have : system.first.baselineFamily.card + system.failedFamily.card - 1 =
        system.first.baselineFamily.card + system.first.firstFailure.index := by omega
    rw [this]
    exact real
  · intro k hk
    have w := Graph.SparsePairSkeletonModel.weighted_deficiency_le P
      system.failedFamily.card (fun k _ => (step k).1) (fun k _ => (step k).2) k hk
    rw [zero] at w
    have pos : 1 ≤ system.failedFamily.card := by omega
    calc _ ≤ 2 ^ (system.failedFamily.card - 1) * 2 ^ system.first.baselineFamily.card := w
      _ = _ := by
        rw [← pow_add]
        congr 1
        omega

/-- Node `[178]`: G's canonical overlap system carries the correlation profile. -/
theorem pairCorrelation_of_overlapSystem
    (system : PairOverlapSystemStatement data object) :
    PairCorrelationStatement data object := by
  obtain ⟨system, selected⟩ := system
  exact ⟨system, selected, correlationProfile_of_system system⟩

end Hypostructure.Graph.Contracts.SurplusPair
