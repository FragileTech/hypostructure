import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Surplus / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **The strict-surplus Type B outcome**: the Type B fan entry fact
`K .typeBFanEntry`.  No Type B continuation runs on the `surplusAbove` arm; its
quantitative tail `typeBBridgeSublinearRow` requires `K .surplusAtOrBelow`, the
exact negation of this arm's `K .surplusAbove`. -/
-- EG-NODE none (establishes no manuscript DAG node)
abbrev StrictSurplusTypeBOutcome (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile spineData .typeBFanEntry selected.object

/-- The four non-closing outcomes of the common Type B certificate core
`[71]`--`[75]` / `[80]`--`[84]` (`Assembly.Internal.TypeBCertificateBoundary`):
certificate failure charged to the bridge fan mass `[75]`/`[84]`, successful B2
`[74]`/`[82]`, the surviving canonical post-ledger core, and the minimal B2
overlap obstruction `[73]`/`[83]`.  Direct cycles and the B2-paid negative
support close inside that core. -/
abbrev TypeBCertificateOutcome (selected : EGInput.{u}) : Prop :=
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateResidualMass selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateResidual selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBExcluded selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDisjointLedger selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBB2Choice selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBExclusionResidualMass selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBExclusionResidual selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDisjointLedger selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBOverlapObstructionMass selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBGlobalLocalBridge selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBOverlapObstruction selected.object)

/-- The actual same-token handoff at node `[144a]`, retaining its
strict-surplus source and the common Type B entry, after it has entered the
Type B fan ledger (`lem:same-token-bottleneck-routing`): the common
continuation `[68]`--`[75]` / `[78]`--`[84]` returns one of the four
certificate outcomes on the same ledger. -/
abbrev Node144aOutcome (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoff selected.object ∧
  StrictSurplusTypeBOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bottleneckRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .homogeneousBottleneckPattern selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePressureOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .capacityTokenLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  TypeBCertificateOutcome selected

/-- A Type B entry reached from one of the pair-system outcomes, with its
own source fact rather than the node-`[144]` handoff. -/
abbrev PairTypeBOutcome (selected : EGInput.{u}) :=
  ((Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemEarlyOutcome selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementEarlyOutcome selected.object) ∧
    StrictSurplusTypeBOutcome selected ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object)

abbrev StrictSurplusBoundaryResult (selected : EGInput.{u}) :=
  Sum (PLift (Node144aOutcome selected))
    (Sum (PLift (PairTypeBOutcome selected))
      ((K .pairConditionalFactorizationResidual).At selected))

end HypostructureErdos64EG
