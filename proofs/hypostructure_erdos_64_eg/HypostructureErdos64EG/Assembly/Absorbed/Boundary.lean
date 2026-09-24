import HypostructureErdos64EG.Assembly.RouteEight.Boundary

/-!
# Assembly: Absorbed / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

abbrev SelectedAbsorbedGermBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object

end HypostructureErdos64EG
