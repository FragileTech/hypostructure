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

/-- The actual same-token handoff left at node `[144a]`, retaining its
strict-surplus source and the common Type B entry. -/
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
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object

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
