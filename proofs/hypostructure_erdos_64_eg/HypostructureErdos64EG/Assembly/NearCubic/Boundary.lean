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
package's silent cold configurations (`[157]`, retained at `[187]`), and the
two returned residuals of the structural exhaustion at `[153]` (G's first
equal-state pair) and `[54]` (the configuration at G where the joint
realization fails).  (`[162]`, a long corridor of G through a heavy centre, is
no longer returned: the pass needs no terminality of a heavy-entry corridor.)  Each
residual is stated as the disjunction of its subtypes, one per distinct fact
set of the ledger at its return. -/
abbrev SelectedNearCubicSurvivorBoundary (selected : EGInput.{u}) :=
  SelectedNetChargeBoundary selected ∨
    Route8RateFailsSubtypes selected ∨
      BlockedBarrierOverlapSubtypes selected ∨
        ColdBranchClosedLinearSubtypes selected ∨
        Node153ResidualSubtypes selected ∨
        Node54ResidualSubtypes selected

/-- The near-cubic branch, after all sparse exits have been excluded, follows
the surviving-cold/net-charge continuation.  (G-only restatement: the paper's
named target-defect exit `[187]` is closed at G -- exit (b), stated about G, is
empty -- so it returns no residual.) -/
abbrev SelectedNearCubicBoundary (selected : EGInput.{u}) :=
  SelectedNearCubicSurvivorBoundary selected

end HypostructureErdos64EG
