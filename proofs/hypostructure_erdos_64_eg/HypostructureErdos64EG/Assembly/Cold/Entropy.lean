import Hypostructure.Graph.Strategy.ColdCorridorRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Cold / Entropy

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Node `[145]` is a control-flow edge: node `[146]` reads node `[22]`'s
`K .hotColdPartition` directly from the same ExactLedger.  The two outputs of
`[146]` are sibling ledgers; neither output is appended to the other. -/
-- EG-NODE [145] cold-branch continuation from the no-edge of [22], after the spine estimate
-- EG-NODE [146] \(\theta<1/78\)?
noncomputable def selectedColdRoute8Dichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  coldRoute8Dichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[148]`: only the no arm of `[146]` reaches the live-hot entropy
decision. -/
-- EG-NODE [148] live-hot entropy cap closes?
noncomputable def selectedColdHotEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  coldHotEntropyDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[149]`: the live-hot entropy comparison closes on `[148]`'s literal
overflow residual.  On the `[22]` cap arm the ledger already carries
`2 ^ (rate·scales·|𝒫_hot|) ≤ skeletonBudget` (`K .barrierCap`); spending the
skeleton budget against the near-cubic spine (`K .surplusAtOrBelow` and the
standing baseline handshake) gives the exact finite cap
`2·rate·scales·|𝒫_hot| ≤ (⌊log₂ n⌋+1)(δn + T(n))`, which the overflow arm
denies.  This is `prop:p13-density`'s entropy step on the current residual. -/
-- EG-NODE [149] \(P_{13}\) density cap
noncomputable def selectedColdHotEntropyCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldHotEntropyOverflow) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .surplusAtOrBelow) known] : False := by
  have overflow := (history.get (K .coldHotEntropyOverflow)).down
  have cap := (history.get (K .barrierCap)).down
  have nearCubic := (history.get (K .surplusAtOrBelow)).down
  have spine : spineData.{u}.threshold * selected.object.vertexCount ≤
      2 * selected.object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount selected.object
      spineData.{u}.threshold fun vertex =>
        le_trans selected.baseline (selected.object.minDegree_le_degree vertex)
  have bound := Graph.two_mul_exponent_le_scale_mul_edgeBudget selected.object
    (spineData.{u}.windowRate *
      spineData.{u}.separatedScaleCount selected.object.vertexCount *
      (canonicalHotWindows spineData.{u} selected.object).card)
    spineData.{u}.threshold (spineData.{u}.surplusThreshold selected.object.vertexCount)
    cap spine spineData.{u}.three_le_threshold nearCubic
  change coldSkeletonAllowance spineData.{u} selected.object <
    coldWindowBitRate spineData.{u} selected.object *
      (canonicalHotWindows spineData.{u} selected.object).card at overflow
  simp only [coldSkeletonAllowance, coldWindowBitRate] at overflow
  rw [Nat.mul_assoc] at overflow
  exact absurd bound (Nat.not_le_of_lt overflow)

end HypostructureErdos64EG
