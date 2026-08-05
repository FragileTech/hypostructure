import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.Route8CarrierClosureSemantics

/-!
# Route-8 carrier closure

Manuscript nodes `[111]`--`[124]`, Figure 9: the reusable CT5 → CT14 → CT12
Strategy that terminates exit `(8)`.

This file is the registered Strategy that owns the canonical CT5 → CT14 → CT12
composition.  Domain specializations supply the carrier semantics and terminal
closures through `Registration`; no detached executor or parity adapter sits
beside the Strategy.

The build follows `Core.Strategy.FiniteScheduleCapacity` (CT6 → CT5 → CT14)
step for step; only the first stage is dropped and a peeling stage appended.

## What each stage decides

* **CT5** weighs the carrier supply against the demand.  `.deficit` is an active
  entry with no supported essential carrier -- `α(ξ) = 0`, so
  `lem:typeA-one-terminal-collapse` applies and one of exits `(4)`--`(7)` occurs.
  That is node `[116]`.
* **CT14** takes the private-carrier census.  `.aggregate` is
  `prop:typeA-route8-carrier-reduction`'s squeeze: the private carriers of
  distinct entries are disjoint, so a total below the demand exhibits an entry
  with fewer than `required` of them -- the two-carrier entry of node `[118]`.
  `.capacity` is the complementary arm, nodes `[119]`--`[121]`, whose collision
  with the route-8 burden is node `[122]`.
* **CT12** runs the pressure descent of node `[123]`.  Each target-defective
  entry peels by exit `(4)` and `lem:typeA-exit4-finite-descent` supplies the
  strict decrease, so the manuscript's loop is a well-founded recursion the
  framework owns rather than a cycle in the DAG.  `.tier` is node `[124]`, the
  terminal two-carrier obstruction, which `thm:typeA-two-carrier-nogo` refutes.
-/

namespace Hypostructure.Core.Strategy.Route8CarrierClosure

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe uPrevious uResidual uData uResource

variable {Previous : Type uPrevious} {Residual : Type uResidual}
variable {AmbientItem : Residual → Type uData}

/-- One registered route-8 carrier closure at a literal predecessor. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual]
    (AmbientItem : Residual → Type uData) where
  registration : Registration.{uResidual, uData, uResource} Residual AmbientItem

namespace Profile

variable [HasResidual Previous Residual]

def residualQuery (profile : Profile Previous Residual AmbientItem) :
    Query Previous fun _ => Residual :=
  Query.residual

/-! ## CT5: the carrier supply, nodes `[114]`--`[116]` -/

def carrierSpec (profile : Profile Previous Residual AmbientItem) :
    CT5.Spec Previous where
  budget := profile.registration.budget
  Site := fun previous => AmbientItem (profile.residualQuery previous)
  Witness := fun previous =>
    profile.registration.Witness (profile.residualQuery previous)
  Active := fun previous =>
    profile.registration.Active (profile.residualQuery previous)
  Supports := fun previous =>
    profile.registration.Supports (profile.residualQuery previous)
  contribution := fun previous =>
    profile.registration.witnessContribution (profile.residualQuery previous)
  required := fun previous =>
    profile.registration.required (profile.residualQuery previous)
  capacity := fun previous =>
    profile.registration.capacity (profile.residualQuery previous)

def carrierFamily (profile : Profile Previous Residual AmbientItem) :
    Query Previous fun previous =>
      Core.Finite.DependentEnumeration
        (profile.carrierSpec.Site previous)
        (profile.carrierSpec.Witness previous) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.family residual

def carrierCapability (profile : Profile Previous Residual AmbientItem) :
    CT5.Capability profile.carrierSpec where
  family := profile.carrierFamily
  activeDecidable := fun previous site =>
    profile.registration.activeDecidable
      (profile.residualQuery previous) site
  supportsDecidable := fun previous site witness =>
    profile.registration.supportsDecidable
      (profile.residualQuery previous) site witness
  resourceLEDecidable := profile.registration.resourceLEDecidable

noncomputable def carrierExecution (profile : Profile Previous Residual AmbientItem) :
    CTExecution Previous :=
  CTAdapters.ct5 profile.carrierCapability

abbrev AfterCarriers (profile : Profile Previous Residual AmbientItem) :=
  Ledger.Extension Previous profile.carrierExecution.Output

def ct5Result (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCarriers fun stage =>
      profile.carrierExecution.Output stage.previous :=
  Query.latest

def residualAfterCarriers (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCarriers fun _ => Residual :=
  profile.residualQuery.preserve

def ct5AndResidual (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCarriers fun stage =>
      PProd (profile.carrierExecution.Output stage.previous) Residual :=
  profile.ct5Result.and profile.residualAfterCarriers

/-! ## CT14: the private-carrier census, nodes `[117]`--`[122]` -/

def censusSpec (profile : Profile Previous Residual AmbientItem) :
    CT14.Spec profile.AfterCarriers where
  Member := fun stage => AmbientItem (profile.residualAfterCarriers stage)
  Label := fun stage =>
    profile.registration.Label (profile.residualAfterCarriers stage)
  memberLowerMass := fun stage member =>
    profile.registration.memberLowerMass
      (profile.residualAfterCarriers stage) member
  memberCapacity := fun stage member =>
    profile.registration.memberCapacity
      (profile.residualAfterCarriers stage) member
  memberLabel := fun stage member =>
    profile.registration.memberLabel
      (profile.residualAfterCarriers stage) member

def censusMembers (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCarriers fun stage =>
      Core.Finite.Enumeration (profile.censusSpec.Member stage) :=
  profile.ct5AndResidual.dependentMap fun _ inputs =>
    profile.registration.members inputs.snd

def censusCapability (profile : Profile Previous Residual AmbientItem) :
    CT14.Capability profile.censusSpec where
  members := profile.censusMembers
  labelDecidableEq := fun stage =>
    profile.registration.labelDecidableEq
      (profile.residualAfterCarriers stage)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.censusMembers stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def censusExecution (profile : Profile Previous Residual AmbientItem) :
    CTExecution profile.AfterCarriers :=
  CTAdapters.ct14 profile.censusCapability

abbrev AfterCensus (profile : Profile Previous Residual AmbientItem) :=
  Ledger.Extension profile.AfterCarriers profile.censusExecution.Output

def residualAfterCensus (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCensus fun _ => Residual :=
  profile.residualAfterCarriers.preserve

/-! ## CT12: the pressure descent, nodes `[123]`--`[124]` -/

def descentSpec (profile : Profile Previous Residual AmbientItem) :
    CT12.Spec profile.AfterCensus where
  State := fun stage =>
    profile.registration.State (profile.residualAfterCensus stage)
  Peeled := fun state => profile.registration.Peeled state
  DemandResidual := fun stage =>
    profile.registration.DemandResidual (profile.residualAfterCensus stage)
  TierResidual := fun stage =>
    profile.registration.TierResidual (profile.residualAfterCensus stage)
  peel := fun state => profile.registration.peel state
  restorations := fun peeled => profile.registration.restorations peeled

def descentInitial (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterCensus (CT12.InitialState profile.descentSpec) :=
   fun stage =>
    { load := profile.registration.initialLoad
        (profile.residualAfterCensus stage)
      state := profile.registration.initialState
        (profile.residualAfterCensus stage) }

def descentCapability (profile : Profile Previous Residual AmbientItem) :
    CT12.Capability profile.descentSpec where
  initial := profile.descentInitial
  inputSize := fun stage => (profile.descentInitial stage).load
  -- Both are read off CT12's own check schedule rather than written.  The
  -- coefficient is the cost CT12 charges a single peel, `maximumChecks 1`, and
  -- the degree is one because an exact erase removes one entry per step, so the
  -- descent is linear in the load -- the same `Fintype.card Unit` the census
  -- block above uses for its own unit degree.
  workCoefficient := CT12.maximumChecks 1
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [CT12.maximumChecks, Fintype.card_unit, Nat.pow_one]
    omega

noncomputable def descentExecution (profile : Profile Previous Residual AmbientItem) :
    CTExecution profile.AfterCensus :=
  CTAdapters.ct12 profile.descentCapability

/-! ## Manuscript nodes `[122]` and `[124]`: the two terminals close

The registered closures are consumed the way
`FiniteStateCapacity.state_not_incompatibility` consumes its own: a CT terminal
that the registration proves uninhabited is *never selected*, so Core eliminates
the branch endpoint instead of retaining it.  Nothing is routed by hand -- the
outcome is cased and its own payload is refuted. -/

/-- **Manuscript node `[124]`.**  Under the registered no-go the descent never
reaches its tier terminal.  `thm:typeA-two-carrier-nogo` says no terminal
two-carrier route-8 obstruction exists, and CT12's `.tier` outcome carries
exactly such an obstruction. -/
theorem descent_not_tier (profile : Profile Previous Residual AmbientItem)
    (closure : ∀ residual : Residual,
      profile.registration.TierResidual residual → False)
    (result : CT12.ExecutionResult profile.descentSpec
      profile.descentCapability) :
    result.terminal ≠ .tier := by
  intro selected
  have outcome : CT12.Outcome profile.descentSpec result.stage.previous .tier :=
    selected ▸ result.outcome
  cases outcome with
  | tier residual =>
      exact closure _ residual

/-! ### The non-closure outputs

Same discipline, read off the two earlier stages instead of the descent. -/

/-- **Manuscript node `[116]`.**  Under the registered collapse the carrier
stage never reaches its deficit terminal.  CT5's `.deficit` output is an active
scheduled site whose entire incoming witness fibre fails to support it, which is
`α(ξ) = 0`; `lem:typeA-one-terminal-collapse` puts one of exits `(4)`--`(7)`
there, and `def:typeA-true-route8-residual` denies all of them. -/
theorem carriers_not_deficit (profile : Profile Previous Residual AmbientItem)
    (closure : ∀ residual : Residual,
      Core.Finite.Search.IndexedHit
        (profile.registration.family residual).indices
        (fun site => profile.registration.Active residual site ∧
          Core.Finite.Search.Avoids
            ((profile.registration.family residual).fibres site)
            (profile.registration.Supports residual site)) → False)
    (result : CT5.ExecutionResult profile.carrierSpec profile.carrierCapability) :
    result.terminal ≠ .deficit := by
  intro selected
  have outcome : CT5.Outcome profile.carrierCapability result.stage.previous
      .deficit := selected ▸ result.outcome
  cases outcome with
  | deficit residual => exact closure _ residual

/-- The carrier stage never reaches its `.c4` terminal.  That output is
`¬ (required ≤ capacity)`, which the registered affordability denies. -/
theorem carriers_not_c4 (profile : Profile Previous Residual AmbientItem)
    (affordable : ∀ residual : Residual,
      profile.registration.required residual ≤
        profile.registration.capacity residual)
    (result : CT5.ExecutionResult profile.carrierSpec profile.carrierCapability) :
    result.terminal ≠ .c4 := by
  intro selected
  have outcome : CT5.Outcome profile.carrierCapability result.stage.previous
      .c4 := selected ▸ result.outcome
  cases outcome with
  | c4 certificate =>
      exact certificate.capacityFailure (affordable _)

/-- The census never reaches its `.unboundedMember` terminal.  That output is a
scheduled member whose capacity reads `none`, which the registered totality
denies. -/
theorem census_not_unboundedMember
    (profile : Profile Previous Residual AmbientItem)
    (total : ∀ (residual : Residual) (member : AmbientItem residual),
      profile.registration.memberCapacity residual member ≠ none)
    (result : CT14.ExecutionResult profile.censusSpec profile.censusCapability) :
    result.terminal ≠ .unboundedMember := by
  intro selected
  have outcome : CT14.Outcome profile.censusCapability result.stage.previous
      .unboundedMember := selected ▸ result.outcome
  cases outcome with
  | unboundedMember _ residual =>
      exact total _ residual.value residual.sound

/-- The census never reaches its `.missingLabel` terminal.  Same discipline: the
output is a scheduled member with no label. -/
theorem census_not_missingLabel
    (profile : Profile Previous Residual AmbientItem)
    (total : ∀ (residual : Residual) (member : AmbientItem residual),
      profile.registration.memberLabel residual member ≠ none)
    (result : CT14.ExecutionResult profile.censusSpec profile.censusCapability) :
    result.terminal ≠ .missingLabel := by
  intro selected
  have outcome : CT14.Outcome profile.censusCapability result.stage.previous
      .missingLabel := selected ▸ result.outcome
  cases outcome with
  | missingLabel _ _ residual =>
      exact total _ residual.value residual.sound

/-- **The four eliminations, as a statement about the selected terminals.**

Under the registered non-closure refutations the carrier stage can only select
`.chargeLedger` -- an empty `σ(X) = 0` part -- or `.aggregate`, and the census
only `.aggregate` (node `[118]`'s two-carrier entry) or `.capacity` (nodes
`[119]`--`[121]`).  In particular Figure 9's closure arm, which both
`ClosureResidual` constructors gate on `.aggregate` at *both* stages, is
reachable rather than vacuous. -/
theorem carriers_terminal (profile : Profile Previous Residual AmbientItem)
    (deficitClosure : ∀ residual : Residual,
      Core.Finite.Search.IndexedHit
        (profile.registration.family residual).indices
        (fun site => profile.registration.Active residual site ∧
          Core.Finite.Search.Avoids
            ((profile.registration.family residual).fibres site)
            (profile.registration.Supports residual site)) → False)
    (affordable : ∀ residual : Residual,
      profile.registration.required residual ≤
        profile.registration.capacity residual)
    (result : CT5.ExecutionResult profile.carrierSpec profile.carrierCapability) :
    result.terminal = .chargeLedger ∨ result.terminal = .aggregate := by
  match selected : result.terminal with
  | .deficit =>
      exact absurd selected (profile.carriers_not_deficit deficitClosure result)
  | .c4 => exact absurd selected (profile.carriers_not_c4 affordable result)
  | .chargeLedger => exact Or.inl rfl
  | .aggregate => exact Or.inr rfl

/-- The census counterpart of `carriers_terminal`. -/
theorem census_terminal (profile : Profile Previous Residual AmbientItem)
    (capacityTotal : ∀ (residual : Residual) (member : AmbientItem residual),
      profile.registration.memberCapacity residual member ≠ none)
    (labelTotal : ∀ (residual : Residual) (member : AmbientItem residual),
      profile.registration.memberLabel residual member ≠ none)
    (result : CT14.ExecutionResult profile.censusSpec profile.censusCapability) :
    result.terminal = .aggregate ∨ result.terminal = .capacity := by
  match selected : result.terminal with
  | .unboundedMember =>
      exact absurd selected
        (profile.census_not_unboundedMember capacityTotal result)
  | .missingLabel =>
      exact absurd selected (profile.census_not_missingLabel labelTotal result)
  | .aggregate => exact Or.inl rfl
  | .capacity => exact Or.inr rfl

/-- **Manuscript node `[122]`.**  Under the registered private-carrier budget
the descent never reaches its demand terminal.
`prop:typeA-route8-carrier-reduction` collides the budget with the route-8
burden and the large-budget deficit, and CT12's `.demand` outcome carries
exactly the residual that collision refutes. -/
theorem descent_not_demand (profile : Profile Previous Residual AmbientItem)
    (closure : ∀ residual : Residual,
      profile.registration.DemandResidual residual → False)
    (result : CT12.ExecutionResult profile.descentSpec
      profile.descentCapability) :
    result.terminal ≠ .demand := by
  intro selected
  have outcome : CT12.Outcome profile.descentSpec result.stage.previous .demand :=
    selected ▸ result.outcome
  cases outcome with
  | demand residual =>
      exact closure _ residual

/-! ## The composed execution -/

noncomputable def execution (profile : Profile Previous Residual AmbientItem) :
    CTExecution Previous :=
  (CTAdapters.ct5 profile.carrierCapability).compose
    ((CTAdapters.ct14 profile.censusCapability).compose
      (CTAdapters.ct12 profile.descentCapability))

abbrev AfterClosure (profile : Profile Previous Residual AmbientItem) :=
  Ledger.Extension Previous profile.execution.Output

def result (profile : Profile Previous Residual AmbientItem) :
    Query profile.AfterClosure fun stage =>
      profile.execution.Output stage.previous :=
  Query.latest

/-- The arms that do **not** reach the terminal two-carrier obstruction.

`deficit` is node `[116]`, `c4` and `chargeLedger` are the carrier-supply
comparisons, `aggregate` is node `[118]`'s two-carrier entry, `capacity` feeds
node `[122]`, and `exhausted`/`demand` are the descent's own exits. -/
inductive NonClosureResidual
    (profile : Profile Previous Residual AmbientItem) (previous : Previous) where
  | deficit
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .deficit)
  | c4
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .c4)
  | chargeLedger
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .chargeLedger)
  | unboundedMember
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (selected : output.snd.fst.terminal = .unboundedMember)
  | missingLabel
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (selected : output.snd.fst.terminal = .missingLabel)
  | aggregate
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (censusSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .exhausted)
  | capacity
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (selected : output.snd.fst.terminal = .capacity)

/-- The two terminal ellipses Figure 9 draws: node `[122]`, the large-budget
carrier obstruction the descent's demand alternative would have to exhibit, and
node `[124]`, the terminal two-carrier obstruction its tier alternative would.
`prop:typeA-route8-carrier-reduction` and `thm:typeA-two-carrier-nogo` refute
them, so a registration that supplies both refutations closes this whole arm. -/
inductive ClosureResidual
    (profile : Profile Previous Residual AmbientItem) (previous : Previous) where
  | budget
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (censusSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .demand)
  | nogo
      (output : profile.execution.Output previous)
      (carriersSelected : output.fst.terminal = .aggregate)
      (censusSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .tier)

/-- **Manuscript nodes `[122]` and `[124]` close.**  Under the two registered
refutations the closure payload is uninhabited, so Core eliminates that branch
endpoint as vacuous rather than retaining it as an open leaf.

This is the whole content of the two terminals: the large-budget carrier
obstruction and the terminal two-carrier obstruction the descent would have to
exhibit are the ones `prop:typeA-route8-carrier-reduction` and
`thm:typeA-two-carrier-nogo` refute. -/
theorem closureResidual_impossible
    (profile : Profile Previous Residual AmbientItem)
    (tier : ∀ residual : Residual,
      profile.registration.TierResidual residual → False)
    (demand : ∀ residual : Residual,
      profile.registration.DemandResidual residual → False)
    {previous : Previous} (payload : profile.ClosureResidual previous) :
    False := by
  cases payload with
  | budget _ _ _ selected => exact profile.descent_not_demand demand _ selected
  | nogo _ _ _ selected => exact profile.descent_not_tier tier _ selected

/-- **Manuscript node `[122]` closes.**  Under the registered private-carrier
budget the descent's demand arm is uninhabited, so the census-capacity endpoint
is vacuous too.

`prop:typeA-route8-carrier-reduction` is what supplies the hypothesis: the
budget, the route-8 burden and the large-budget deficit cannot hold together
below the carrier rate. -/
theorem demandResidual_impossible
    (profile : Profile Previous Residual AmbientItem)
    (closure : ∀ residual : Residual,
      profile.registration.DemandResidual residual → False)
    {previous : Previous}
    (output : profile.execution.Output previous)
    (selected : output.snd.snd.terminal = .demand) :
    False :=
  profile.descent_not_demand closure _ selected

noncomputable def dichotomy (profile : Profile Previous Residual AmbientItem) :
    Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.NonClosureResidual
  RightPayload := profile.ClosureResidual
  classify := fun previous =>
    let output := profile.execution.run previous
    match carriersSelected : output.fst.terminal with
    | .deficit => .inl (.deficit output carriersSelected)
    | .c4 => .inl (.c4 output carriersSelected)
    | .chargeLedger => .inl (.chargeLedger output carriersSelected)
    | .aggregate =>
        match censusSelected : output.snd.fst.terminal with
        | .unboundedMember =>
            .inl (.unboundedMember output carriersSelected censusSelected)
        | .missingLabel =>
            .inl (.missingLabel output carriersSelected censusSelected)
        | .capacity =>
            .inl (.capacity output carriersSelected censusSelected)
        | .aggregate =>
            match descentSelected : output.snd.snd.terminal with
            | .exhausted =>
                .inl (.aggregate output carriersSelected censusSelected
                  descentSelected)
            | .demand =>
                .inr (.budget output carriersSelected censusSelected
                  descentSelected)
            | .tier =>
                .inr (.nogo output carriersSelected censusSelected
                  descentSelected)

end Profile

end Hypostructure.Core.Strategy.Route8CarrierClosure
