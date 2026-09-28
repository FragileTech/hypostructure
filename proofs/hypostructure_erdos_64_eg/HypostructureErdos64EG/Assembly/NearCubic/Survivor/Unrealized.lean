import Hypostructure.Graph.Strategy.BlockedCompressionRows
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.SpineRows.DenseNetDeficiencyCap
import Hypostructure.Graph.Strategy.SpineRows.DensityOrder
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
      [K .route8RateFails, K .denseDeficiencyBelow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
         K .admissibleQuotientsLabelInjective, K .replacementExclusion,
         K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
         K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint,
       K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
         K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
         K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
         K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
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
      | .left linearHistory =>
          exact nearCubicDenseLinear linearHistory
            (Or.inr (DenseTauBlock_belowRateFails.ret linearHistory))
      | .right boundedHistory =>
          let density :=
            (densityBudgetRow (data := spineData)).run boundedHistory
              (by key_fresh)
          -- `[24]` on `[146]` no: the density cap (`θ ≤ θ_win + o(1)`) against
          -- `θ ≥ 1/78`, combined at G; the exact size test closes `N₀ ≤ n` and
          -- retains `n < N₀`.
          let ordered :=
            (boundedDensityOrderRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              density (by key_fresh)
          match boundedOrderDichotomy (data := spineData) ordered
              (by key_fresh) (by key_fresh) with
          | .left largeHistory =>
              exact ((closeIncompatible largeHistory (K .boundedDensityOrder)
                (K .boundedOrderLarge) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
          | .right smallHistory =>
              exact nearCubicLargeBudgetRateFailed (nearCubicFullRank smallHistory)

set_option maxHeartbeats 8000000 in
/-- **The dense hot/cold pass `[162]` on `[160]`'s first complement**
(`τ(θ) ≥ 1/4`).  `[22]`--`[23]`; the `[146]` yes arm is empty: `θ < 1/78` gives
`τ(θ) < 3/13 < 1/4` (`def:cold-window-ledger`), against the retained
`τ(θ) ≥ 1/4`; the `[146]` no arm runs `[148]`--`[152]` and decides `[153]`: the
linear arm is the dense linear pass, the bounded arm returns through `[24]` to
`[25]`. -/
noncomputable def Assembly.Internal.nearCubicDensePassAtOrAbove
    {selected : EGInput.{u}}
    (denseHistory : ExactLedger EGInput.{u} selected
      [K .denseDeficiencyAtOrAbove,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
         K .admissibleQuotientsLabelInjective, K .replacementExclusion,
         K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
         K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint,
       K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
         K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
         K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
         K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let cap := nearCubicHotColdCap denseHistory
  match coldRoute8Dichotomy (data := spineData) cap
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      -- `[146]` yes on the retained `τ(θ) ≥ 1/4`: `θ < 1/78` gives
      -- `τ(θ) < 3/13 < 1/4` (`def:cold-window-ledger`), the literal negation of
      -- `[160]`'s first complement, so this arm of the pass is empty.
      exact (closeIncompatible belowHistory (K .denseDeficiencyAtOrAbove)
        (K .coldRoute8Below) (by key_fresh)).elimClosed (by infer_instance) |>.elim
  | .right atOrAboveHistory =>
      let stubs := nearCubicColdStubs atOrAboveHistory
      match coldMassDichotomy (data := spineData) stubs
          (by key_fresh) (by key_fresh) with
      | .left linearHistory =>
          exact nearCubicDenseLinear linearHistory
            (Or.inl (DenseTauBlock_atOrAbove.ret linearHistory))
      | .right boundedHistory =>
          let density :=
            (densityBudgetRow (data := spineData)).run boundedHistory
              (by key_fresh)
          -- `[24]` on `[146]` no: the exact size test, as on the rate-failed arm.
          let ordered :=
            (boundedDensityOrderRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              density (by key_fresh)
          match boundedOrderDichotomy (data := spineData) ordered
              (by key_fresh) (by key_fresh) with
          | .left largeHistory =>
              exact ((closeIncompatible largeHistory (K .boundedDensityOrder)
                (K .boundedOrderLarge) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
          | .right smallHistory =>
              exact nearCubicLargeBudgetDensityCap (nearCubicFullRank smallHistory)
                (Or.inr
                  (Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove.ret
                    smallHistory))

set_option maxHeartbeats 8000000 in
/-- **The dense-packing residual, the no-arm of `[158]`.**  `[159]`: the exact
package size exceeds the labelled skeleton count (`K .windowPackageUnrealized`).
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
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
         K .admissibleQuotientsLabelInjective, K .replacementExclusion,
         K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
         K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint,
       K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
         K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
         K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
         K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  match denseDeficiencyDichotomy (data := spineData) unrealizedHistory
      (by key_fresh) (by key_fresh) with
  | .right denseHistory =>
      exact Assembly.Internal.nearCubicDensePassAtOrAbove denseHistory
  | .left belowHistory =>
      match route8RateDichotomy (data := spineData) belowHistory
          .denseDeficiencyBelow (Or.inr rfl) (by key_fresh) (by key_fresh) with
      | .right rateFails =>
          exact Assembly.Internal.nearCubicDensePassRateFailed rateFails
      | .left ratedHistory =>
          let partitioned :=
            (hotColdPartitionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              ratedHistory (by key_fresh)
          -- `[22]`'s live-hot cap and `[149]`--`[152]` are facts of G on the
          -- `[161]` arm too: `liveHotBarrierCapRow` publishes the cap from the
          -- partition and `[21]`'s skeleton bound.
          let capped :=
            (liveHotBarrierCapRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              partitioned (by key_fresh)
          let stubbed := nearCubicColdStubFacts capped
          exact nearCubicLargeBudgetDenseRate (nearCubicFullRank stubbed)

end HypostructureErdos64EG
