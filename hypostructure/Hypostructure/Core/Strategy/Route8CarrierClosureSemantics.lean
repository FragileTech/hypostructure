import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Finite.Search
import Hypostructure.CT12.Spec

/-!
# Route-8 carrier closure semantics

Residual-indexed primitive data for the reusable CT5 → CT14 → CT12 Strategy.
The registration contains no query, ledger, execution result, terminal, route,
or selected outcome, exactly as
`Core.Strategy.FiniteScheduleCapacity.Registration` does for CT6 → CT5 → CT14.

The three blocks are the manuscript's three questions at a route-8 residual:

* the **CT5** block is the carrier supply -- which indexed entries are active,
  which essential carriers support them, and how the supply compares with the
  demand.  Its deficit scan is the entry with no supported carrier;
* the **CT14** block is the private-carrier census -- each entry's own private
  carriers weighed against the derived demand.  Its aggregate outcome is the
  low-private-carrier entry;
* the **CT12** block is the pressure descent -- one peel per target-defective
  entry, with the strict decrease that licenses another iteration.

No numeral appears in this file.  `required`, `capacity` and `memberLowerMass`
are residual observations, so a domain instantiates them at its own registered
discharge scale and carrier demand.
-/

namespace Hypostructure.Core.Strategy.Route8CarrierClosure

universe uResidual uData uResource

/-- Inert residual presentation consumed by CT5, CT14, and CT12.

`AmbientItem` is the **predecessor's own ledger carrier**, exactly as
`Strategy.FiniteStateCapacity.Registration` receives it: the indexed route-8
entries of `def:typeA-route8-carriers` are items of the inherited normalized
support, not a set this registration builds from the object.  That is what makes
the support, `def⁺` and the entry count ledger readings rather than recomputed
observations. -/
structure Registration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uData) where
  -- CT5: the carrier supply, manuscript nodes [114]-[116].
  -- The resource carries its own universe, exactly as `CT5.Spec` does: the
  -- boundary-incidence supply of `def:typeA-route8-carriers` is counted in the
  -- ordinary counting budget, which does not live where the indexed entries do.
  budget : Core.ResourceBudget.{uResource}
  Witness : (residual : Residual) → AmbientItem residual → Type uData
  family : (residual : Residual) →
    Core.Finite.DependentEnumeration (AmbientItem residual) (Witness residual)
  Active : (residual : Residual) → AmbientItem residual → Prop
  Supports : (residual : Residual) → (site : AmbientItem residual) →
    Witness residual site → Prop
  witnessContribution : (residual : Residual) → (site : AmbientItem residual) →
    Witness residual site → budget.Resource
  required : Residual → budget.Resource
  capacity : Residual → budget.Resource
  activeDecidable : (residual : Residual) → (site : AmbientItem residual) →
    Decidable (Active residual site)
  supportsDecidable : (residual : Residual) → (site : AmbientItem residual) →
    (witness : Witness residual site) →
      Decidable (Supports residual site witness)
  resourceLEDecidable : (left right : budget.Resource) →
    Decidable (left ≤ right)

  -- CT14: the private-carrier census, manuscript nodes [117]-[122].
  Label : Residual → Type uData
  members : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual)
  memberLowerMass : (residual : Residual) → AmbientItem residual → Nat
  memberCapacity : (residual : Residual) → AmbientItem residual → Option Nat
  memberLabel : (residual : Residual) →
    AmbientItem residual → Option (Label residual)
  labelDecidableEq : (residual : Residual) → DecidableEq (Label residual)
  -- CT12: the pressure descent, manuscript nodes [123]-[124].
  State : Residual → Nat → Type uData
  Peeled : {residual : Residual} → {load : Nat} →
    State residual (load + 1) → Type uData
  DemandResidual : Residual → Type uData
  TierResidual : Residual → Type uData
  peel : {residual : Residual} → {load : Nat} →
    (state : State residual (load + 1)) → Peeled state
  restorations : {residual : Residual} → {load : Nat} →
    {state : State residual (load + 1)} → (peeled : Peeled state) →
      CT12.RestorationOptions (State residual) (DemandResidual residual)
        (TierResidual residual) (load + 1)
  initialLoad : Residual → Nat
  initialState : (residual : Residual) → State residual (initialLoad residual)
  /-- **Manuscript node `[124]`.**  `thm:typeA-two-carrier-nogo`: there is no
  terminal two-carrier route-8 obstruction.  Supplying this field lets Core
  eliminate the tier output as vacuous instead of retaining it as an open branch
  endpoint, exactly as `FiniteStateCapacity.Registration.nonCapacityImpossible`
  does for its own non-capacity arm.  A registration whose tier alternative is
  genuinely inhabited leaves this `none` and that output stays live. -/
  tierImpossible :
    Option (PLift (∀ residual : Residual, TierResidual residual → False)) :=
    none
  /-- **Manuscript node `[122]`.**  `prop:typeA-route8-carrier-reduction`: the
  private-carrier budget, the route-8 burden and the large-budget deficit cannot
  hold together below the carrier rate.  Same discipline as `tierImpossible`:
  supplied, Core eliminates the descent's demand alternative; `none`, it stays
  live.  Both slots must be supplied for the closure arm to terminate, because
  that arm carries both of Figure 9's terminal ellipses. -/
  capacityImpossible :
    Option (PLift (∀ residual : Residual, DemandResidual residual → False)) :=
    none
  /-- **Manuscript node `[116]`.**  `lem:typeA-one-terminal-collapse`: there is
  no surviving indexed entry with `α_𝒳(ξ) ≤ 1`.

  The payload is CT5's `.deficit` residual itself -- the canonical first
  scheduled site satisfying `DeficitAt`, with its index, its soundness and its
  before-absence -- written in this registration's vocabulary.  Nothing is
  repackaged: `Core.Finite.Search.IndexedHit` over the registered site schedule
  *is* `CT5.LocalDeficitResidual`. -/
  deficitImpossible :
    Option (PLift (∀ residual : Residual,
      Core.Finite.Search.IndexedHit (family residual).indices
        (fun site => Active residual site ∧
          Core.Finite.Search.Avoids ((family residual).fibres site)
            (Supports residual site)) → False)) :=
    none
  /-- CT5's `.c4` output, `¬ (required ≤ capacity)`. -/
  requiredAffordable :
    Option (PLift (∀ residual : Residual,
      required residual ≤ capacity residual)) :=
    none
  /-- CT14's `.unboundedMember` output, a member with no published capacity. -/
  memberCapacityTotal :
    Option (PLift (∀ (residual : Residual) (member : AmbientItem residual),
      memberCapacity residual member ≠ none)) :=
    none
  /-- CT14's `.missingLabel` output, a member with no label. -/
  memberLabelTotal :
    Option (PLift (∀ (residual : Residual) (member : AmbientItem residual),
      memberLabel residual member ≠ none)) :=
    none

end Hypostructure.Core.Strategy.Route8CarrierClosure
