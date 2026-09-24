import HypostructureErdos64EG.Assembly.Absorbed.Boundary

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
Route-8 residuals or the literal absorbed-germ residuals published by their
own ledger owners. -/
abbrev SelectedNetChargeBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected ∨ SelectedAbsorbedGermBoundary selected

end HypostructureErdos64EG
