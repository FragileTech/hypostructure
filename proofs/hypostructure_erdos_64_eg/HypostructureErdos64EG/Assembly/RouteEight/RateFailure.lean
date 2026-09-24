import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: RouteEight / RateFailure

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The exact complement of the private-carrier rate is retained as its own
residual.  The manuscript does not route this fact to nodes `[174]`--`[177]`;
those nodes are entered only by `K .exactCollisionFails`. -/
noncomputable def selectedRouteEightRateFailure
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8RateFails) known] :
    ExactLedger EGInput.{u} selected known := by
  let _rateFailure := (history.get (K .route8RateFails)).down
  exact history

end HypostructureErdos64EG
