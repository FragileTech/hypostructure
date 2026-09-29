import HypostructureErdos64EG.Assembly.RouteEight.Boundary
import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: NetCharge / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The only live conclusions of the net-charge continuation are the literal
Route-8 residuals.  The `[173]` no-arm (the absorbed-configuration residual
`[174]`, with its fan data, and its cold-closure exits)
is closed at the node against the private-carrier rate `K .route8Rate`. -/
abbrev SelectedNetChargeBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected

end HypostructureErdos64EG
