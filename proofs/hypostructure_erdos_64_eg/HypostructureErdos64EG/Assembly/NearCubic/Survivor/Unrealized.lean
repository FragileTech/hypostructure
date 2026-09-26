import Hypostructure.Graph.Strategy.BlockedCompressionRows
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.SpineRows.DenseNetDeficiencyCap
import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
import Hypostructure.Graph.Strategy.SpineRows.Route8RateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow
import HypostructureErdos64EG.Assembly.NearCubic.DensePass
import HypostructureErdos64EG.Assembly.NearCubic.Spine

/-!
# Assembly: NearCubic / Survivor / Unrealized

The no-arm of `[158]`, the dense-packing residual of Part XII: `[159]`, the two
exact rate tests `[160]`, the double-yes arm `[161]`, and the dense hot/cold
pass `[162]` on either complement.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **The dense hot/cold pass `[162]` on `[160]`'s second complement**
(`τ(θ) < 1/4`, private-carrier rate failed).  `[22]`--`[23]`; the `[146]` yes
arm `[147]` derives the private-carrier rate from `θ < 1/78` and closes it
against the retained failure; the `[146]` no arm runs `[148]`--`[152]` and
decides `[153]`: the linear arm is the dense linear pass, the bounded arm returns
through `[24]` to `[25]`, retaining the failed rate. -/
noncomputable def Assembly.Internal.nearCubicDensePassRateFailed
    {selected : EGInput.{u}}
    (rateFails : ExactLedger EGInput.{u} selected
      [K .route8RateFails, K .denseDeficiencyBelow, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let cap := nearCubicHotColdCap rateFails
  match coldRoute8Dichotomy (data := spineData) cap
      (by key_fresh) (by key_fresh) with
  | .left coldBelowHistory =>
      exact ((route8RateFromColdBelowRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible
          coldBelowHistory (K .route8RateFails) (K .route8Rate)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
  | .right atOrAboveHistory =>
      let stubs := nearCubicColdStubs atOrAboveHistory
      match coldMassDichotomy (data := spineData) stubs
          (by key_fresh) (by key_fresh) with
      | .left linearHistory => exact nearCubicDenseLinear linearHistory
      | .right boundedHistory =>
          let density :=
            (densityBudgetRow (data := spineData)).run boundedHistory
              (by key_fresh)
          exact nearCubicLargeBudgetRateFailed (nearCubicFullRank density)

set_option maxHeartbeats 8000000 in
/-- **The dense hot/cold pass `[162]` on `[160]`'s first complement**
(`τ(θ) ≥ 1/4`).  `[22]`--`[23]`; the `[146]` yes arm `[147]` runs the spine's
route-8 closure with `τ(θ) < 3/13` from `θ < 1/78`; the `[146]` no arm runs
`[148]`--`[152]` and decides `[153]`: the linear arm is the dense linear pass,
the bounded arm returns through `[24]` to `[25]`. -/
noncomputable def Assembly.Internal.nearCubicDensePassAtOrAbove
    {selected : EGInput.{u}}
    (denseHistory : ExactLedger EGInput.{u} selected
      [K .denseDeficiencyAtOrAbove, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let cap := nearCubicHotColdCap denseHistory
  match coldRoute8Dichotomy (data := spineData) cap
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      let rated :=
        (route8RateFromColdBelowRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          belowHistory (by key_fresh)
      exact nearCubicLargeBudgetColdRate (nearCubicFullRank rated)
  | .right atOrAboveHistory =>
      let stubs := nearCubicColdStubs atOrAboveHistory
      match coldMassDichotomy (data := spineData) stubs
          (by key_fresh) (by key_fresh) with
      | .left linearHistory => exact nearCubicDenseLinear linearHistory
      | .right boundedHistory =>
          let density :=
            (densityBudgetRow (data := spineData)).run boundedHistory
              (by key_fresh)
          exact nearCubicLargeBudgetDensityCap (nearCubicFullRank density)

set_option maxHeartbeats 8000000 in
/-- **The dense-packing residual, the no-arm of `[158]`.**  `[159]`: the exact
package size exceeds the labelled skeleton count (`densePackingOverflowRow`).
`[160]` decides `τ(θ) < 1/4` and, on its yes arm, the private-carrier rate
`τ(θ) < 3/13` (`lem:dense-deficiency-routing`).  The double-yes arm `[161]`
continues at `[25]` with the deficiency cap in place of `[24]`; the spine
consumes `def:cold-window-ledger`'s canonical hot/cold partition of the fixed
packing, so that definitional fact is appended on this arm's own ledger.
Either complement enters the dense hot/cold pass `[162]`. -/
-- EG-NODE [159] dense-packing residual: the no-edge of [158]; exact package size \(2^{b_{\mathcal P}}\) exceeds the labelled skeleton count
-- EG-NODE [160] exact rate split: first \(\tau(\theta)<1/4\)?; on yes, private-carrier rate \(\tau(\theta)<3/13\)?
-- EG-NODE [161] both rates hold: negative-net-charge collision; continue at [25] with the deficiency cap in place of [24]
noncomputable def Assembly.Internal.nearCubicUnrealized
    {selected : EGInput.{u}}
    (unrealizedHistory : ExactLedger EGInput.{u} selected
      [K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let denseOverflow :=
    (densePackingOverflowRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unrealizedHistory (by key_fresh)
  match denseDeficiencyDichotomy (data := spineData) denseOverflow
      (by key_fresh) (by key_fresh) with
  | .right denseHistory =>
      exact Assembly.Internal.nearCubicDensePassAtOrAbove denseHistory
  | .left belowHistory =>
      match route8RateDichotomy (data := spineData) belowHistory
          (by key_fresh) (by key_fresh) with
      | .right rateFails =>
          exact Assembly.Internal.nearCubicDensePassRateFailed rateFails
      | .left ratedHistory =>
          let partitioned :=
            (hotColdPartitionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              ratedHistory (by key_fresh)
          exact nearCubicLargeBudgetDenseRate (nearCubicFullRank partitioned)

end HypostructureErdos64EG
