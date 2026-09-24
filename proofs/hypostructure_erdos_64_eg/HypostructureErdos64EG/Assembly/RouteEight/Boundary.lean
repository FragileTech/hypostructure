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

/-- **Nodes `[110]`--`[116]`: the route-8 residual of Part IX**, on the shared
  `[109]` residual reached by the no-edge of exit `(7)` (index-polymorphic).
  This is exactly the edge drawn in Part VIII after the visible/silent
  residual routing and any finite exit-`(4)` peeling.  `[110]`
  `route8ResidualProfileRow`
(`def:typeA-silent-core-residual`: the saturated receiver survives only through
exit `(8)`, no decorated handoff fan); `[111]` `route8GlobalSqueezeRow` (the
  canonical route-8 Type A subcollection and its cleared `D_A` sum); `[112]`
  `route8BasinBurdenRow` (`lem:typeA-route8-burden`: for every member of that
  exact collection, `[111]` supplies the silent-first route-8 entry family and
  `[88]`, `K .typeAReceiverRouting`, supplies total routing; the row sums
  `S_sil^exc(X) ≥ s·D_A(X)` over the collection); `[113]`
`route8LargeBudgetDeficitRow` (`def:typeA-large-budget-deficit`), whose positive
arm is exactly the displayed route-8-only bound and whose negative arm enters
the unified target-defect/route-8 ledger required by `rem:why-unified`; `[114]`
`route8CarrierCoreRow` (canonical minimal target-complete carrier cores in the
declared `u`-supported response algebra), `route8TrueResidualRow` (the exact
true route-8 residual conditions `(R1)`--`(R4)` for every actual indexed entry),
and `route8CarrierCutParityRow` (`lem:typeA-carrier-cut-parity` for precisely
the surviving mixed events of those entries);
`[115]`--`[116]`
`route8SmallCoreCollapseRow` (`lem:typeA-one-terminal-collapse`: a zero/one
essential-core entry triggers exits `(4)`--`(7)`, absent here); then the
object-level census `K .route8Census` (`Graph.Route8Census`: the indexed entries
`(piece, receiver, silent-excess load)` of the Type A pieces `𝒳_A`, their selected
trace basins and canonical essential cores, the supply `∂R`; the deficit
`|R| ≤ N_basin + s·|∂R|` and the private-carrier rate — its row is the next
producer `route8CensusRow`), `[117]` `route8CarrierDichotomy` on it,
`[119]`--`[122]` closed inline by `Graph.Route8Census.false_of_noTwoCarrier`
(`rem:route8-carrier-margin`), and the two-carrier arm `[118]`--`[124]`. -/
-- EG-NODE [110] exit (8): route-8 residual profile
-- EG-NODE [111] global squeeze extracts a route-8 Type A collection $\mathcal X_A$ carrying $D_A(\mathcal X_A)$
-- EG-NODE [112] route-8 burden: $N_{\rm basin}(\mathcal X_A)\ge4D_A(\mathcal X_A)$
-- EG-NODE [113] large-budget deficit: $D_A(\mathcal X_A)\ge(1/4-\tau_{\rm win})|R|-o(|R|)$
-- EG-NODE [114] each entry passes to its canonical minimal target-complete response-support core inside the declared $u$-supported response algebra
-- EG-NODE [115] some entry has $\alpha_{\mathcal X}(\xi)\le1$?
-- EG-NODE [116] exits (4)--(7) occur
-- EG-NODE [117] some entry has $\pi_{\mathcal X}(\xi)\le2$?
-- EG-NODE [118] two-support route-8 entry
-- EG-NODE [119] no two-support entry: every indexed entry has at least three private essential boundary incidences
-- EG-NODE [120] private-support budget: $3N_{\rm basin}(\mathcal X_A)\le\defp(R)+o(|R|)\le\tau_{\rm win}|R|+o(|R|)$
-- EG-NODE [121] burden plus deficit: $N_{\rm basin}(\mathcal X_A)\ge4(1/4-\tau_{\rm win})|R|-o(|R|)$
-- EG-NODE [122] contradiction: $\tau_{\rm win}\ge12(1/4-\tau_{\rm win})$, but $\tau_{\rm win}<3/13$
-- EG-NODE [123] finite exact descent terminates in true route 8?
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
