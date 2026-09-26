import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: RouteEight / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **The open outcomes of Part IX.**  The route-`8` residual of exit `(8)`
(`selectedRouteEightResidual`) closes nodes `[110]`--`[124]` and `[181]`; its
surviving outcomes are the Type B sublinear-bridge residual, the route-`8`
quotient residual of the unified census, and the node-`[186]` joint balance. -/
abbrev SelectedRouteEightBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearResidual
      selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8QuotientResidual
        selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8JointBalance
        selected.object

end HypostructureErdos64EG
