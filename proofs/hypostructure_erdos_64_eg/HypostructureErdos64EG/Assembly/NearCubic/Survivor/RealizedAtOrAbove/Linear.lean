import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicRealizedAtOrAboveLinear
    {selected : EGInput.{u}}
    (linearHistory : ExactLedger EGInput.{u} selected
      [K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition,
       K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[153]`: `lem:bridgeless`, the return corridors, first-failure
  -- routing, the exchange bound and extraction, and the (F5)
  -- candidate germ family on the linear residual; then `[154]`.
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run linearHistory
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
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run
      state (by simp [K_eq_iff])
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
      handoffTransfer (by simp [K_eq_iff])
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by simp [K_eq_iff])
  let candidates :=
    (coldGermCandidatesRow (data := spineData)).run extracted
      (by simp [K_eq_iff])
  let positive :=
    (coldGermFamilyPositiveRow (data := spineData)).run candidates
      (by simp [K_eq_iff])
  let trichotomy :=
    (coldGermTrichotomyRow (data := spineData)).run positive
      (by simp [K_eq_iff])
  let table :=
    (coldSameInterfaceTableRow (data := spineData)).run trichotomy
      (by simp [K_eq_iff])
  let closed :=
    (coldBranchClosedRow (data := spineData)).run table
      (by simp [K_eq_iff])
  -- The realized-package arm is the ordinary Part-XI oval.
  -- Its paper edge ends at `[157]`; only `[159]`'s dense
  -- residual continues to the neutral split `[163]`.
  exact Or.inr (Or.inr (Or.inr
    (closed.get (K .coldBranchClosed)).down))

end HypostructureErdos64EG
