import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.CorridorState
import Hypostructure.Graph.Strategy.ColdCorridorRows.DenseTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.FailureClauses
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureOccurrence
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureRouting
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermCandidates
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermExtraction
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermFamilyPositive
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.HandoffTransfer
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.ReturnCorridor
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
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
noncomputable def Assembly.Internal.nearCubicDenseAtOrAboveLinear
    {selected : EGInput.{u}}
    (linearHistory : ExactLedger EGInput.{u} selected
      [K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap,
       K .hotColdPartition, K .denseDeficiencyAtOrAbove, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[153]`--`[157]` on the dense linear residual: `lem:bridgeless`,
  -- return corridors, first-failure routing, exchange bound and
  -- extraction, the (F5) candidate family, the germ trichotomy and
  -- the same-interface table.  (F1)/G1 close by `K .selection`,
  -- (F2)/G2 by `lem:context-universality`, (F3)/G3 by
  -- `K .replacementExclusion`; the residual after them is the
  -- neutral equal-length terminal germ `[163]`, a symmetry
  -- (`lem:neutral-germ-symmetry`): canonical-replacement swap
  -- (`[165]`--`[166]`, refined minimality: needs the (F5) exchange
  -- representative `E` built as a piece and the selection order
  -- refined by the canonical atom multiset) or a genuine symmetric
  -- strand pair (`[167]`, `Graph/TwoStrandEnumeration.lean`: closed
  -- by a dyadic cycle iff `2ℓ ∈ Pow ∨ ℓ + d ∈ Pow`; the surviving
  -- pairs `ℓ ∉ Pow ∧ ℓ + d ∉ Pow` are `[168]`).
  let normalized :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      linearHistory (by key_fresh)
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run normalized (by key_fresh)
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      relabelingEntropy (by key_fresh)
  let corridors :=
    (coldReturnCorridorRow (data := spineData)).run bridgeless (by key_fresh)
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run corridors
      (by key_fresh)
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by key_fresh)
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state
      (by key_fresh)
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run terminal
      (by key_fresh)
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by key_fresh)
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by key_fresh)
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run failureDefect
      (by key_fresh)
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run failureCompression
      (by key_fresh)
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run failureHandoff
      (by key_fresh)
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
      (by key_fresh)
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by key_fresh)
  let candidates :=
    (coldGermCandidatesRow (data := spineData)).run extracted (by key_fresh)
  let positive :=
    (coldGermFamilyPositiveRow (data := spineData)).run candidates
      (by key_fresh)
  -- `[154]`, `lem:cold-bounded-germ-trichotomy`, as nested exact binary
  -- tests on node `[153]`'s extracted active family.  G1?
  match selectedColdGermRealizationDichotomy positive
      (by key_fresh) (by key_fresh) with
  | .left hitHistory =>
      -- `[155]`: G1, a power-of-two cycle, contradicts `K .selection`.
      exact ((closeIncompatible hitHistory (K .coldGermSomeRealizing)
        (K .selection) (by key_fresh)).elimClosed
        (by infer_instance)).elim
  | .right unhitHistory =>
  -- No G1: G2?
  match selectedColdGermDistinctionDichotomy unhitHistory
      (by key_fresh) (by key_fresh) with
  | .left distinguishedHistory =>
      -- `[156]`: G2 is a target-defective identification, routed to the
      -- target-defect, exit-(4), or existing handoff ledgers "as before"
      -- (`lem:dense-cold-pass`); the local cold-terminal exclusion is the
      -- `[187]` outcome.  Only `[157]`'s neutral row continues to `[163]`.
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
  -- `[157]`: every active configuration is silent (G3 or the finite
  -- same-interface table); its neutral equal-length row continues to `[163]`.
  let neutralConfiguration :=
    (neutralEqualLengthTerminalRow (data := spineData)).run silentHistory
      (by key_fresh)
  let trichotomy :=
    (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
      (by key_fresh)
  let table :=
    (coldSameInterfaceTableRow (data := spineData)).run trichotomy
      (by key_fresh)
  let closed :=
    (coldBranchClosedRow (data := spineData)).run table (by key_fresh)
  -- `[163]`, `lem:neutral-germ-symmetry`: decide the manuscript's
  -- literal question — whether the neutral equal-length terminal
  -- configuration has a graph-realized second representative.
  match neutralGermSymmetryDichotomy (data := spineData)
      closed
      (by key_fresh) (by key_fresh) with
  | .left canonicalHistory =>
      -- `[165]`: the marked `E ≠ Q` exchange preserves the baseline,
      -- target avoidance, and both graph counts, while replacing the
      -- marked canonical-decomposition piece by a strict predecessor.
      -- `[166]` consumes this literal ledger fact with node `[4]`'s
      -- refined minimality and retains only `Q = E`.
      let swapped :=
        (canonicalReplacementSwapRow (data := spineData)).run
          canonicalHistory (by key_fresh)
      exact Or.inr (Or.inr (Or.inl
        (selectedCanonicalReplacementContinuation swapped)))
  | .right genuineHistory =>
      -- `[167]` retains the finite-check survivor; `[168]` proves
      -- its exclusion from the selected interior occurrence and
      -- closes the two exact facts through Core.
      let survivor :=
        (twoStrandSurvivorRow (data := spineData)).run genuineHistory
          (by key_fresh)
      let stubbed :=
        (coldWindowStubStructureRow (data := spineData)).run survivor
          (by key_fresh)
      let closedHistory :=
        (symmetricPairEndpointExclusionRow
          (data := spineData)).runAndCloseIncompatible
          stubbed (K .coldTwoStrandSurvivor)
            (K .coldSymmetricPairExcluded)
          (by key_fresh) (by key_fresh)
      exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
