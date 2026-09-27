import HypostructureErdos64EG.Assembly.NetCharge.Boundary

/-!
# Assembly: NearCubic / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The outcomes of the near-cubic survivor after node `[21]`: the net-charge
continuation's residuals, the failed private-carrier rate retained at the
entry of the route-8 continuation (`[187]`), the blocked-class overlap
residual `[172a]`, the local cold-terminal exclusion of the realized
package's silent cold configurations (`[157]`, retained at `[187]`), and the
three returned residuals of the structural exhaustion at `[153]` (G's first
equal-state pair), `[162]` (a long corridor of G through a heavy centre) and
`[54]` (the configuration at G where the joint realization fails). -/
abbrev SelectedNearCubicSurvivorBoundary (selected : EGInput.{u}) :=
  SelectedNetChargeBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8RateFails selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .coldRepeatedStateResidual
            selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .coldDenseHeavyEntryResidual
            selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .allColdEntropyResidual
            selected.object

/-- The literal target-defect exit left by the enclosing `[20]` sparse-exit
classification.  It is an outgoing residual, not a contradiction, not a
survivor fact, and not an output of routing-only node `[125]`. -/
abbrev SelectedSparseTargetDefectBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile spineData .sparseTargetDefectResidual
      selected.object

/-- The near-cubic branch either leaves through the paper's named
target-defect exit or, after all sparse exits have been excluded, follows the
surviving-cold/net-charge continuation. -/
abbrev SelectedNearCubicBoundary (selected : EGInput.{u}) :=
  (SelectedSparseTargetDefectBoundary selected ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure
        selected.object) ∨
    SelectedNearCubicSurvivorBoundary selected

end HypostructureErdos64EG
