import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.CorridorState
import Hypostructure.Graph.Strategy.ColdCorridorRows.FailureClauses
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureOccurrence
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureRouting
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermCandidates
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermExtraction
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermFamilyPositive
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.HandoffTransfer
import Hypostructure.Graph.Strategy.ColdCorridorRows.ReturnCorridor
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
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
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
      (by key_fresh)
  let corridors :=
    (coldReturnCorridorRow (data := spineData)).run bridgeless
      (by key_fresh)
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run
      corridors (by key_fresh)
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by key_fresh)
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run
      state (by key_fresh)
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by key_fresh)
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by key_fresh)
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run
      failureDefect (by key_fresh)
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run
      failureCompression (by key_fresh)
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run
      failureHandoff (by key_fresh)
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run
      handoffTransfer (by key_fresh)
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by key_fresh)
  let candidates :=
    (coldGermCandidatesRow (data := spineData)).run extracted
      (by key_fresh)
  let positive :=
    (coldGermFamilyPositiveRow (data := spineData)).run candidates
      (by key_fresh)
  -- `[154]`, `lem:cold-bounded-germ-trichotomy`, as nested exact binary
  -- tests on node `[153]`'s extracted active family.  G1?
  match selectedColdGermRealizationDichotomy positive
      (by key_fresh) (by key_fresh) with
  | .left hitHistory =>
      -- `[155]`: G1, a power-of-two cycle, contradicts the counterexample
      -- condition retained in `K .selection`.
      exact ((closeIncompatible hitHistory (K .coldGermSomeRealizing)
        (K .selection) (by key_fresh)).elimClosed
        (by infer_instance)).elim
  | .right unhitHistory =>
  -- No G1: G2?
  match selectedColdGermDistinctionDichotomy unhitHistory
      (by key_fresh) (by key_fresh) with
  | .left distinguishedHistory =>
      -- `[156]`: G2 is a target-defective identification
      -- (`lem:context-universality`), routed to the target-defect,
      -- exit-(4), or existing handoff ledgers; `thm:cold-branch-quantitative-closure`
      -- then publishes the local cold-terminal exclusion.  `thm:main` retains
      -- that local exclusion at `[187]`: no global contradiction is derived
      -- from it on this ledger.
      let trichotomy :=
        (coldGermTrichotomyRow (data := spineData)).run distinguishedHistory
          (by key_fresh)
      let table :=
        (coldSameInterfaceTableRow (data := spineData)).run trichotomy
          (by key_fresh)
      let closed :=
        (coldBranchClosedRow (data := spineData)).run table
          (by key_fresh)
      exact Or.inr (Or.inr (Or.inr
        (closed.get (K .coldBranchClosed)).down))
  | .right silentHistory =>
      -- `[157]`: every active configuration is silent -- G3 or a row of the
      -- finite same-interface table.  The realized-package arm is the
      -- ordinary Part-XI oval: its edge ends at `[157]` (only `[159]`'s
      -- dense residual continues to `[163]`), and the local cold-terminal
      -- exclusion is the `[187]` outcome.
      let trichotomy :=
        (coldGermTrichotomyRow (data := spineData)).run silentHistory
          (by key_fresh)
      let table :=
        (coldSameInterfaceTableRow (data := spineData)).run trichotomy
          (by key_fresh)
      let closed :=
        (coldBranchClosedRow (data := spineData)).run table
          (by key_fresh)
      exact Or.inr (Or.inr (Or.inr
        (closed.get (K .coldBranchClosed)).down))

end HypostructureErdos64EG
