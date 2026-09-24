import Hypostructure.Graph.Strategy.SpineRows.LiveHotBarrierCap
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Cold / Barrier

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Node `[22]`: the canonical hot/cold partition (`def:cold-window-ledger`),
then the live-hot entropy cap decision on `𝒫_hot`.

The comparison is formed from the current object's own registered quantities:
`skeletonBudget` against `2 ^ (rate · scales · |𝒫_hot|)`.  The overflow cursor
is the live-hot terminal `[23]`; the cap cursor is the literal no-arm residual
forwarded toward `[24]` and the cold continuation. -/
-- EG-NODE [22] hot/cold split $\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold}$: live-hot entropy cap closes?
noncomputable def selectedBarrierDichotomy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .hotColdPartition) known]
    (capFresh : K .barrierCap ∉ known)
    (overflowFresh : K .barrierOverflow ∉ known) :
    Decision (K .barrierCap) (K .barrierOverflow) history := by
  classical
  let _split := (history.get (K .hotColdPartition)).down
  exact Decision.run history (K .barrierCap) (K .barrierOverflow)
    `HypostructureErdos64EG.selectedBarrierDichotomy
    (if overflow : Graph.skeletonBudget selected.object <
        2 ^ (spineData.{u}.windowRate *
          spineData.{u}.separatedScaleCount selected.object.vertexCount *
          (canonicalHotWindows spineData.{u} selected.object).card) then
      .inr ⟨overflow⟩
    else
      .inl ⟨Nat.le_of_not_lt overflow⟩)
    capFresh overflowFresh

/-- Node `[23]`: the live-hot `P₁₃` window entropy overflow closes on the
literal overflow residual.  `liveHotBarrierCapRow` reads the retained hot
package, the package-rate inequality, and the skeleton state-count bound from
that exact ledger and publishes the manuscript's opposite cap.  The framework
atomically runs that row and closes its cap against the visible overflow arm;
the application eliminates only the resulting distinguished closure fact. -/
-- EG-NODE [23] live-hot $P_{13}$ window entropy overflow
noncomputable def selectedBarrierOverflowCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .barrierOverflow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    (capFresh : K .barrierCap ∉ known)
    (closureFresh : closed ∉ known) : False := by
  let closedHistory :=
    (liveHotBarrierCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible
      history (K .barrierOverflow) (K .barrierCap)
      (by simpa using capFresh) (by simp [closureFresh])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[24]`: `prop:p13-density` "after closure" — on `[153]`'s bounded arm
(the cold branch forces no germ), the window-only density cap with its exact
`o(1)` is produced from `K .coldMass`, `K .coldMassBounded`,
`K .coldAmbientCubic`, and the split, on the literal residual. -/
-- EG-NODE [24] bounded cold-mass return from [153]: $\theta\le\theta_{\rm win}+o(1)$; high entropy: $\theta\le0.01198542083\ldots$
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (densityBudgetRow (data := spineData)).run history (by simp [K_eq_iff])

end HypostructureErdos64EG
