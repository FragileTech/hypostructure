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
genuine configurations close at `[176]`, and its fan data continues through
Type B to the route-8 residuals. -/
abbrev SelectedAbsorbedGermBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected

end HypostructureErdos64EG
