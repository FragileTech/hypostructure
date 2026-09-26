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

/-- **Node `[144a]`** (`thm:main` (ii)): the same-token handoff retained with
its token/role fibre (`K .typeBHandoff`, `K .bottleneckRouting`), the
active-demand and capacity presentations (`K .sparsePressureOverload`,
`K .capacityTokenLedger`), the homogeneous bottleneck pattern
(`K .homogeneousBottleneckPattern`) whose packing/core/decorated envelope is
carried by the handoff, its strict-surplus ancestry (`K .surplusAbove`,
`K .sparseSurplusSurvivor`), and the Type B fan entry `K .typeBFanEntry`; or,
when the routed pattern produces no handoff (`K .typeBHandoffFails`), the
residual of the paper error at `[144]` (`K .sameTokenPatternUnresolved`: the
same-label pattern pair whose readings are profile-separated without exit or
target-complete).  No cap or near-cubic estimate is part of this outcome. -/
abbrev Node144aOutcome (selected : EGInput.{u}) :=
  ((Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .typeBHandoff selected.object ∧
      StrictSurplusTypeBOutcome selected) ∨
    (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .typeBHandoffFails selected.object ∧
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .sameTokenPatternUnresolved
          selected.object)) ∧
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

/-- The strict-surplus branch returns exactly the three root outcomes it can
reach, as the literal disjunction the root boundary lists: the node-`[144a]`
handoff, a `[179]`/`[180]` Type B entry, or the open node-`[182]` residual. -/
abbrev StrictSurplusBoundaryResult (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∨ PairTypeBOutcome selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData
        .pairConditionalFactorizationResidual selected.object

end HypostructureErdos64EG
