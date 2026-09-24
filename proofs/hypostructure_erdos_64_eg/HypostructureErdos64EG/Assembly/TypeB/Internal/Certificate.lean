import Hypostructure.Graph.Strategy.SpineRows.B2AssignmentDichotomy
import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairFanClosure
import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.DirectCycleDichotomy
import Hypostructure.Graph.Strategy.SpineRows.DisjointPostLedgerComponents
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateResidualMass
import Hypostructure.Graph.Strategy.SpineRows.FanClosedPort
import Hypostructure.Graph.Strategy.SpineRows.FanClosedPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.HybridEntry
import Hypostructure.Graph.Strategy.SpineRows.TypeBExclusionDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBExclusionResidualMass
import Hypostructure.Graph.Strategy.SpineRows.TypeBGlobalLocalBridge
import Hypostructure.Graph.Strategy.SpineRows.TypeBOverlapObstructionMass
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: TypeB / Internal / Certificate

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/- The four non-closing outputs of the common Type B certificate calculation.
They are exactly the paper's two local-payment and two fan-mass boundaries:
certificate failure `[75]/[84]`, successful B2 `[74]/[82]`, the surviving
canonical post-ledger core, and B2 overlap `[73]/[83]`.  No quantitative fact
from the incoming branch is included in this type. -/
abbrev Assembly.Internal.TypeBCertificateBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (ExactLedger EGInput.{u} selected
      ([K .fanCertificateResidualMass, K .fanCertificateResidual] ++ known))
    (Sum
      (ExactLedger EGInput.{u} selected
        ([K .typeBExcluded, K .typeBDisjointLedger, K .typeBB2Choice,
          K .typeBHybridEntry, K .typeBDirectCycleFree,
          K .fanCertificateMarked] ++ known))
      (Sum
        (ExactLedger EGInput.{u} selected
          ([K .typeBExclusionResidualMass, K .typeBExclusionResidual,
            K .typeBDisjointLedger, K .typeBB2Choice,
            K .typeBHybridEntry, K .typeBDirectCycleFree,
            K .fanCertificateMarked] ++ known))
        (ExactLedger EGInput.{u} selected
          ([K .typeBOverlapObstructionMass, K .typeBGlobalLocalBridge,
            K .typeBOverlapObstruction,
            K .typeBHybridEntry, K .typeBDirectCycleFree,
            K .fanCertificateMarked] ++ known))))

/-- The paper's common `[72]` port-routing prefix.  Each fact is published by
its registered producer exactly once; later local alternatives retrieve these
facts from the resulting ExactLedger. -/
noncomputable def Assembly.Internal.selectedTypeBPortRoutingPrefix
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (fanClosedFresh : K .fanClosedPort ∉ known)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known) :
    ExactLedger EGInput selected
      ([K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort] ++ known) := by
  let fanClosed :=
    (fanClosedPortRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, fanClosedFresh])
  let compatibleClosure :=
    (compatiblePairFanClosureRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      fanClosed (by simp [K_eq_iff, compatibleClosureFresh])
  let fanClosedRouting :=
    (fanClosedPortTypeBRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      compatibleClosure (by simp [K_eq_iff, fanClosedRoutingFresh])
  exact
    (compatiblePairTypeBRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      fanClosedRouting (by simp [K_eq_iff, compatibleRoutingFresh])

/-- **The common Type B core `[71]`--`[75]` / `[80]`--`[84]`.**

This function consumes only the facts named by those nodes.  Direct cycles and
the canonical B2-paid negative support close locally.  Every other arm returns
its literal paper residual.  In particular it does not assume the ordinary
`[64]` negative support, a route-8 rate, or a near-cubic surplus estimate; the
enclosing branch decides how `[76]`/`[85]` spends the returned mass. -/
-- EG-NODE [71] certificate labelling present?
-- EG-NODE [75] bridge fan-mass: fan-certificate centers and B2 failures charged to assigned surplus
-- EG-NODE [80] certificate labelling present?
-- EG-NODE [84] fan-mass route: certificate failures and B2 failures charged to assigned surplus
noncomputable def Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .fanClosedPort) known]
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      simp [K_eq_iff])
    :
    Assembly.Internal.TypeBCertificateBoundary selected known := by
  -- `[71]`/`[80]`: certificate labelling present at every assigned centre?
  match fanCertificateDichotomy (data := spineData) history
      (by simp [K_eq_iff, markedFresh]) (by simp [K_eq_iff, residualFresh]) with
  | .right residualHistory =>
      -- `[75]`/`[84]`: the residual centre is charged to the bridge fan mass.
      let mass :=
        (fanCertificateResidualMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          residualHistory (by simp [K_eq_iff, certificateMassFresh])
      exact Sum.inl mass
  | .left markedHistory =>
      -- `[72]`--`[85]` on the common Type B carrier: the direct fan-window
      -- cycle test and the hybrid B1 reading preserve either the canonical
      -- assigned support or the indexed absorbed witness.  B2 is the next
      -- boundary: it may proceed only once its own literal carrier is present.
      match directCycleDichotomy (data := spineData) markedHistory
          (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh]) with
      | .left cycleHistory =>
          have impossible : False := by
            rcases (cycleHistory.get (K .typeBDirectCycle)).down with
              canonical | absorbed | sameToken
            · obtain ⟨packing, valid, _maximal, _component, _present, _centres,
                _assigned, _centre, _member, _high, directCycle⟩ := canonical
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
            · obtain ⟨_marked, _germ, _centre, _witness, directCycle⟩ :=
                absorbed
              have valid : selected.object.IsWindowPacking spineData.windowOrder
                  (canonicalWindowPacking spineData selected.object) :=
                (Classical.choose_spec
                  (selected.object.exists_windowPacking_card_eq
                    spineData.windowOrder)).1
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
            · obtain ⟨packing, valid, _maximal, _core, _envelope, _coreEq,
                  _nonempty, _marked, _centre, _member, _high, directCycle⟩ :=
                sameToken
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
          exact impossible.elim
      | .right freeHistory =>
          -- B1 is a fact of every direct-cycle-free marked fan, independently
          -- of whether B2 succeeds.  Publish it before the B2 split so both
          -- resulting exact ledgers retain the same local incidence proof.
          let hybrid :=
            (hybridEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              freeHistory (by simp [K_eq_iff, hybridFresh])
          match b2AssignmentDichotomy (data := spineData) hybrid
              (by simp [K_eq_iff, choiceFresh])
              (by simp [K_eq_iff, obstructionFresh]) with
          | .left choiceHistory =>
              let ledger :=
                (disjointPostLedgerComponentsRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  choiceHistory (by simp [K_eq_iff, ledgerFresh])
              match typeBExclusionDichotomy (data := spineData) ledger
                  (by simp [K_eq_iff, excludedFresh])
                  (by simp [K_eq_iff, exclusionResidualFresh]) with
              | .left excludedHistory =>
                  -- The exact paid ledger is returned without inspecting its
                  -- carrier.  Ordinary `[64]` closes its canonical alternative;
                  -- `[144]` and `[177]` retain their own handoff alternative.
                  exact Sum.inr (Sum.inl excludedHistory)
              | .right residualHistory =>
                  let mass :=
                    (typeBExclusionResidualMassRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      residualHistory (by simp [K_eq_iff, exclusionMassFresh])
                  exact Sum.inr (Sum.inr (Sum.inl mass))
          | .right obstructionHistory =>
              let reflected :=
                (typeBGlobalLocalBridgeRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  obstructionHistory
                    (by simp [K_eq_iff, globalLocalBridgeFresh])
              let mass :=
                (typeBOverlapObstructionMassRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  reflected (by simp [K_eq_iff, obstructionMassFresh])
              exact Sum.inr (Sum.inr (Sum.inr mass))

end HypostructureErdos64EG
