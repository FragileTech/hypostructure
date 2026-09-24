import Hypostructure.Graph.Strategy.ColdCorridorRows
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
       K .denseDeficiencyAtOrAbove, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
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
      linearHistory (by simp [K_eq_iff])
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run normalized (by simp [K_eq_iff])
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      relabelingEntropy (by simp [K_eq_iff])
  let corridors :=
    (coldReturnCorridorRow (data := spineData)).run bridgeless (by simp [K_eq_iff])
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run corridors
      (by simp [K_eq_iff])
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by simp [K_eq_iff])
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state
      (by simp [K_eq_iff])
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run terminal
      (by simp [K_eq_iff])
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by simp [K_eq_iff])
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by simp [K_eq_iff])
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run failureDefect
      (by simp [K_eq_iff])
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run failureCompression
      (by simp [K_eq_iff])
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run failureHandoff
      (by simp [K_eq_iff])
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
      (by simp [K_eq_iff])
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by simp [K_eq_iff])
  let candidates :=
    (coldGermCandidatesRow (data := spineData)).run extracted (by simp [K_eq_iff])
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
    (coldBranchClosedRow (data := spineData)).run table (by simp [K_eq_iff])
  -- `[163]`, `lem:neutral-germ-symmetry`: decide the manuscript's
  -- literal question — whether the neutral equal-length terminal
  -- configuration has a graph-realized second representative.
  match neutralGermSymmetryDichotomy (data := spineData)
      closed
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left canonicalHistory =>
      -- `[165]`: the marked `E ≠ Q` exchange preserves the baseline,
      -- target avoidance, and both graph counts, while replacing the
      -- marked canonical-decomposition piece by a strict predecessor.
      -- `[166]` consumes this literal ledger fact with node `[4]`'s
      -- refined minimality and retains only `Q = E`.
      let swapped :=
        (canonicalReplacementSwapRow (data := spineData)).run
          canonicalHistory (by simp [K_eq_iff])
      exact Or.inr (Or.inr (Or.inl
        (selectedCanonicalReplacementContinuation swapped)))
  | .right genuineHistory =>
      -- `[167]` retains the finite-check survivor; `[168]` proves
      -- its exclusion from the selected interior occurrence and
      -- closes the two exact facts through Core.
      let survivor :=
        (twoStrandSurvivorRow (data := spineData)).run genuineHistory
          (by simp [K_eq_iff])
      let stubbed :=
        (coldWindowStubStructureRow (data := spineData)).run survivor
          (by simp [K_eq_iff])
      let closedHistory :=
        (symmetricPairEndpointExclusionRow
          (data := spineData)).runAndCloseIncompatible
          stubbed (K .coldTwoStrandSurvivor)
            (K .coldSymmetricPairExcluded)
          (by simp [K_eq_iff]) (by simp [K_eq_iff])
      exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
