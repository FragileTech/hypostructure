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
fan data continues through Type B to the route-8 residuals, and its genuine
configurations `[176]` run `[154]`--`[157]`, `[165]`--`[168]`: the G2 outcome
`[156]`, and the arm of `[175]` read at `[177]` on which every selected corridor
is subcubic, are the local cold exclusion `K .coldBranchClosed` retained at
`[187]`. -/
abbrev SelectedAbsorbedGermBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected ∨ ColdBranchClosedOutcome selected

end HypostructureErdos64EG
