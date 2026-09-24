import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicBelowRateFailureLinear
    {selected : EGInput.{u}}
    (linearHistory : ExactLedger EGInput.{u} selected
      [K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .route8RateFails,
       K .denseDeficiencyBelow, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let normalized :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run linearHistory
      (by simp [K_eq_iff])
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run normalized (by simp [K_eq_iff])
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run relabelingEntropy
      (by simp [K_eq_iff])
  let corridors :=
    (coldReturnCorridorRow (data := spineData)).run bridgeless
      (by simp [K_eq_iff])
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run
      corridors (by simp [K_eq_iff])
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by simp [K_eq_iff])
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state
      (by simp [K_eq_iff])
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run
      terminal (by simp [K_eq_iff])
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by simp [K_eq_iff])
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by simp [K_eq_iff])
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run
      failureDefect (by simp [K_eq_iff])
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run
      failureCompression (by simp [K_eq_iff])
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run
      failureHandoff (by simp [K_eq_iff])
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run
      handoffTransfer
      (by simp [K_eq_iff])
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by simp [K_eq_iff])
  let candidates :=
    (coldGermCandidatesRow (data := spineData)).run extracted
      (by simp [K_eq_iff])
  let positive :=
    (coldGermFamilyPositiveRow (data := spineData)).run candidates
      (by simp [K_eq_iff])
  let neutralConfiguration :=
    (neutralEqualLengthTerminalRow (data := spineData)).run positive
      (by simp [K_eq_iff])
  let trichotomy :=
    (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
      (by simp [K_eq_iff])
  let table :=
    (coldSameInterfaceTableRow (data := spineData)).run trichotomy
      (by simp [K_eq_iff])
  let closed :=
    (coldBranchClosedRow (data := spineData)).run table
      (by simp [K_eq_iff])
  match neutralGermSymmetryDichotomy (data := spineData)
      closed (by simp [K_eq_iff])
      (by simp [K_eq_iff]) with
  | .left canonicalHistory =>
      let swapped :=
        (canonicalReplacementSwapRow (data := spineData)).run
          canonicalHistory (by simp [K_eq_iff])
      exact Or.inr (Or.inr (Or.inl
        (selectedCanonicalReplacementContinuation swapped)))
  | .right genuineHistory =>
      let survivor :=
        (twoStrandSurvivorRow (data := spineData)).run
          genuineHistory (by simp [K_eq_iff])
      let stubbed :=
        (coldWindowStubStructureRow (data := spineData)).run
          survivor (by simp [K_eq_iff])
      let closedHistory :=
        (symmetricPairEndpointExclusionRow
          (data := spineData)).runAndCloseIncompatible
          stubbed (K .coldTwoStrandSurvivor)
            (K .coldSymmetricPairExcluded)
          (by simp [K_eq_iff]) (by simp [K_eq_iff])
      exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
