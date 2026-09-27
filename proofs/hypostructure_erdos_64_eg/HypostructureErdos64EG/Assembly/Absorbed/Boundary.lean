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

/-- The outcomes of the absorbed-configuration residual `[174]`--`[177]`: its
fan data continues through Type B to the route-8 residuals; when every selected
corridor is subcubic, its genuine configurations close at `[176]` by
`[154]`--`[157]`, `[165]`--`[168]`, with the local cold-terminal exclusion
retained at `[187]`. -/
abbrev SelectedAbsorbedGermBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object

end HypostructureErdos64EG
