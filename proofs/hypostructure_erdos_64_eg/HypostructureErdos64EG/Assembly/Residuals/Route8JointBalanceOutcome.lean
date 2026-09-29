import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: Residuals / Route8JointBalanceOutcome

Node `[186]` as a PRODUCT OF ARM BLOCKS.

The 750 paths from `selectedLedgerBoundary` to the one return site
(`route8JointBalanceReturn` in `selectedRouteEightUnifiedResidual`,
`Assembly/RouteEight/Local.lean`) carry 750 distinct fact sets.  Each is
exactly the 80 common keys of `Route8JointBalanceOutcome` together with one
block per factor of

  `15 lane entries × 50 continuation`,  `50 = 2·22 + 6`,

where the lane entry (`Route8LaneEntry`) is `3 prefix × 4 entropy` or the
`[161]` prefix with one of the 3 low-entropy arms: the near-cubic route
"unrealized, `τ(θ) ≥ 1/4`, `θ < 1/78`" is closed at `[146]`, and the `[161]`
route with high entropy is closed at `[53]`,

and every combination occurs (checked against the elaborated ledger of every
path).  These are the same factors as `Route8QuotientOutcome`: both residuals
are returned from the same composition on the same incoming ledger, [186] on
the quotient-free arm after `[123]`, `[181]` and `[183]`--`[185]`.  The blocks
live in `Residuals/Route8Blocks.lean`.
The absorbed lane `[174]`--`[177]` contributes no path: `[173]`'s no-arm is
closed at the node against the private-carrier rate `K .route8Rate`
(`instIncompatibleExactCollisionFailsRoute8Rate`).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[186]` as a product of arm blocks**: the generic residual (102
common facts), one lane entry (a near-cubic prefix block with an entropy
block), and one net-charge continuation (Type A lane or Type B high-surplus
lane, each a nested product of its own blocks).  Totals run from 110 to 149
facts. -/
abbrev Route8JointBalanceOutcome_product (selected : EGInput.{u}) : Prop :=
  Route8JointBalanceOutcome selected ∧ Route8LaneEntry selected ∧
    NetChargeContinuation selected

theorem Route8JointBalanceOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : Route8JointBalanceOutcome_product selected) :
    Route8JointBalanceOutcome selected :=
  h.1

/- The return `route8JointBalanceProductReturn` is removed (G repair, R3): the
node-`[186]` residual is not reached at G.  Node `[123]`'s failed-rate arm is
empty at G (`selectedRouteEightDescent`, `K .route8UnifiedEmptyAtG`), so no
ledger reaches `[181]`, `[183]`--`[186]`.  The abbreviations above stay because
the protected root result type `SelectedLedgerBoundaryResult` still names this
disjunct; it is never produced. -/

end HypostructureErdos64EG
