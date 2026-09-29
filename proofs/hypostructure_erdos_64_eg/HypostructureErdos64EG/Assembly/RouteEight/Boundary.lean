import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks
import HypostructureErdos64EG.Assembly.Residuals.TypeBSublinearOutcome
import HypostructureErdos64EG.Assembly.Residuals.Route8QuotientOutcome
import HypostructureErdos64EG.Assembly.Residuals.Route8JointBalanceOutcome

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
quotient residual `[348]` of the unified census (returned at `[187]` as the
failure of route-8 quotient freeness, per `thm:main`, tex 369-372, 388-390,
1215, 1255), and the node-`[186]` joint balance.  Each is the product of its
generic facts with the arm blocks of its path (prefix, entropy arm and
net-charge continuation, `Assembly/Residuals/Route8Blocks.lean`).  (The joint
balance is reached at G: with trace-basin realizations read on the pieces
constructed from G, node `[123]`'s failed-rate arm is not empty.) -/
abbrev SelectedRouteEightBoundary (selected : EGInput.{u}) :=
  TypeBSublinearOutcome_product selected ∨ Route8QuotientOutcome_product selected ∨
    Route8JointBalanceOutcome_product selected

end HypostructureErdos64EG
