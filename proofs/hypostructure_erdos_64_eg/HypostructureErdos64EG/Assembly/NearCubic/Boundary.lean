import HypostructureErdos64EG.Assembly.NetCharge.Boundary
import HypostructureErdos64EG.Assembly.Residuals.ColdBranchClosedOutcome
import HypostructureErdos64EG.Assembly.Residuals.Node54ResidualOutcome
import HypostructureErdos64EG.Assembly.Residuals.BlockedBarrierOverlapOutcome
import HypostructureErdos64EG.Assembly.Residuals.Route8RateFailsOutcome

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
package's cold configurations (`[157]`, retained at `[187]`: the silent
singleton, the silent germs of `[153]`'s repeat on the dense arms, and the five
subtypes of `[154]`'s G2 yes-arm, live with the constructed second
representative), and the
returned residual of the structural exhaustion at `[54]` (the configuration at
G where the joint realization fails).  `[153]`'s first equal-state pair is
the repeat subcase of (F5) and continues into the germ routing.  The pass needs
no terminality of a heavy-entry corridor.  Each
residual is stated as the disjunction of its subtypes, one per distinct fact
set of the ledger at its return. -/
abbrev SelectedNearCubicSurvivorBoundary (selected : EGInput.{u}) :=
  SelectedNetChargeBoundary selected ∨
    Route8RateFailsSubtypes selected ∨
      BlockedBarrierOverlapSubtypes selected ∨
        ColdBranchClosedLinearSubtypes selected ∨
        Node54ResidualSubtypes selected

/-- The near-cubic branch, on G's survivor fact (the named sparse exits are
the two cycle conclusions in G, refuted by `[4]`'s selection), follows the
surviving-cold/net-charge continuation. -/
abbrev SelectedNearCubicBoundary (selected : EGInput.{u}) :=
  SelectedNearCubicSurvivorBoundary selected

end HypostructureErdos64EG
