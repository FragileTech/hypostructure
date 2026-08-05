import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.ScaleThresholdDichotomySemantics

/-!
# Scale-threshold dichotomy

The strategy realizes a residual-owned finite scale table through CT14.
There is one aggregate member: its lower mass is the observed load and its
capacity is the threshold computed from the registered table at the observed
size.  CT14 therefore owns the exhaustive strict-above / at-or-below
comparison and appends its exact routed result to the literal predecessor.
-/

namespace Hypostructure.Core.Strategy.ScaleThresholdDichotomy

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.Official.Features

universe uPrevious uResidual

/-- A scale-threshold execution reads its complete input from the literal
predecessor.  Registered residual semantics are one constructor of this
query-native profile; later Strategies may instead preserve an exact input
query from an accumulated ledger entry. -/
structure Profile (Previous : Type uPrevious) where
  input : Query Previous fun _ => ScaleDependentThreshold.Input

/-- **Registered semantics evaluated at an exact predecessor query.**

The `At` form of the registered constructor, matching
`LocalSupplyLowerBound.Profile.ofRegistrationAt`,
`BoundaryDemandAccounting.Profile.ofRegistrationAt` and
`TargetRelativeRankDichotomy.Profile.ofRegistrationAt`.  The comparison is run
on whatever residual the supplied query names, which after a
minimal-counterexample selection is the object the spine is actually arguing
about rather than the untouched problem input. -/
def Profile.ofRegistrationAt
    {Residual : Type uResidual}
    (registration : Registration Residual)
    (current : Query Previous fun _ => Residual) : Profile Previous where
  input := current.map fun _ residual =>
    { table := registration.table residual
      size := registration.size residual
      load := registration.load residual }

def Profile.ofRegistration
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (registration : Registration Residual) : Profile Previous :=
  Profile.ofRegistrationAt registration Query.residual

/-- Canonical embedding of an already queried numerical comparison into the
same CT14 strategy.  A singleton fixed row represents the queried threshold;
CT14 still owns the comparison, terminal, exact result, checks, and work. -/
def Profile.ofComparisonQuery
    (comparison : Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat) : Profile Previous where
  input := comparison.map fun _ values =>
    { table := { fixedRows := [values.threshold], scaleRows := [] }
      size := 0
      load := values.value }

namespace Profile

variable (profile : Profile Previous)

def thresholdInput (previous : Previous) : ScaleDependentThreshold.Input :=
  profile.input previous

@[simp] theorem ofComparisonQuery_thresholdInput
    (comparison : Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat)
    (previous : Previous) :
    ((Profile.ofComparisonQuery comparison).thresholdInput previous).threshold =
      (comparison previous).threshold := by
  simp [Profile.ofComparisonQuery, thresholdInput,
    ScaleDependentThreshold.Input.threshold,
    ScaleDependentThreshold.Table.threshold,
    ScaleDependentThreshold.Table.scaleContributions]

@[simp] theorem ofComparisonQuery_load
    (comparison : Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat)
    (previous : Previous) :
    ((Profile.ofComparisonQuery comparison).thresholdInput previous).load =
      (comparison previous).value := by
  rfl

def canonicalMembers : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def memberQuery
    (_profile : Profile Previous) :
    Query Previous fun _ => Core.Finite.Enumeration Unit :=
   fun _ => canonicalMembers

def spec : CT14.Spec Previous where
  Member := fun _ => Unit
  Label := fun _ => Unit
  memberLowerMass := fun previous _ => (profile.thresholdInput previous).load
  memberCapacity := fun previous _ =>
    some (profile.thresholdInput previous).threshold
  memberLabel := fun _ _ => some ()

inductive WorkNesting
  | member
  deriving DecidableEq, Fintype

def workNestingEquiv : WorkNesting ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => .member
  left_inv := by intro nesting; cases nesting; rfl
  right_inv := by intro value; cases value; rfl

def workCoefficient : Nat := CT14.localCheckBound canonicalMembers
def workDegree : Nat := Fintype.card WorkNesting

def capability : CT14.Capability profile.spec where
  members := memberQuery profile
  labelDecidableEq := fun _ => inferInstanceAs (DecidableEq Unit)
  inputSize := fun previous =>
    ((memberQuery profile) previous).card +
      (profile.thresholdInput previous).table.work
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := by
    intro previous
    simp only [memberQuery, workCoefficient,
      workDegree]
    rw [Fintype.card_congr workNestingEquiv]
    simp only [Fintype.card_unit, Nat.pow_one]
    change CT14.localCheckBound canonicalMembers ≤
      CT14.localCheckBound canonicalMembers *
        (canonicalMembers.card +
          (profile.thresholdInput previous).table.work + 1)
    exact Nat.le_mul_of_pos_right _
      (by omega : 0 <
        canonicalMembers.card +
          (profile.thresholdInput previous).table.work + 1)

/-- The only executable object exposed by this strategy.  Core's CT adapter
owns routing, checks, work, and the exact output ledger. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct14 profile.capability

/-- Strict-above residual retaining CT14's exact result. -/
structure AboveResidual (previous : Previous) where
  result : CT14.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  selected : result.terminal = .aggregate

/-- At-or-below residual retaining CT14's exact result. -/
structure AtOrBelowResidual (previous : Previous) where
  result : CT14.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  selected : result.terminal = .capacity

inductive RoutedResidual (previous : Previous) where
  | above (residual : profile.AboveResidual previous)
  | atOrBelow (residual : profile.AtOrBelowResidual previous)

private theorem noUnbounded (previous : Previous)
    (residual : CT14.UnboundedMemberResidual
      profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

private theorem noMissingLabel (previous : Previous)
    (residual : CT14.MissingLabelResidual
      profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

/-- Route only by eliminating CT14 terminals made impossible by the total
capacity and label semantics.  The comparison itself is not repeated. -/
noncomputable def route (previous : Previous) :
    profile.RoutedResidual previous :=
  let result := profile.execution.run previous
  by
    cases terminalEq : result.terminal with
    | unboundedMember =>
        have outcome : CT14.Outcome profile.capability result.stage.previous
            .unboundedMember := by
          simpa [terminalEq] using result.outcome
        cases outcome with
        | unboundedMember _ residual =>
            exact (profile.noUnbounded result.stage.previous residual).elim
    | missingLabel =>
        have outcome : CT14.Outcome profile.capability result.stage.previous
            .missingLabel := by
          simpa [terminalEq] using result.outcome
        cases outcome with
        | missingLabel _ _ residual =>
            exact
              (profile.noMissingLabel result.stage.previous residual).elim
    | aggregate =>
        exact .above ⟨result, rfl, terminalEq⟩
    | capacity =>
        exact .atOrBelow ⟨result, rfl, terminalEq⟩

/-- Standard Core dichotomy view of the exact CT14 route.  Compiler routing
consumes this view instead of reconstructing the terminal split. -/
noncomputable def dichotomy : Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.AboveResidual
  RightPayload := profile.AtOrBelowResidual
  classify := fun previous =>
    match profile.route previous with
    | .above residual => .inl residual
    | .atOrBelow residual => .inr residual

def AboveResidual.outcome
    {previous : Previous} (residual : profile.AboveResidual previous) :
    CT14.Outcome profile.capability previous .aggregate := by
  rw [← residual.previous_eq]
  simpa [residual.selected] using residual.result.outcome

def AtOrBelowResidual.outcome
    {previous : Previous} (residual : profile.AtOrBelowResidual previous) :
    CT14.Outcome profile.capability previous .capacity := by
  rw [← residual.previous_eq]
  simpa [residual.selected] using residual.result.outcome

/-- Public projection from the exact CT14 aggregate residual to the literal
predecessor-owned comparison this profile was executed on.  Consumers do not
unfold CT14's aggregate ledger.

This is the strict-above half of the branch fact recorded by the split: the
observed load genuinely exceeds the threshold the registered table computes at
the observed size. -/
theorem AboveResidual.threshold_lt_load
    {previous : Previous} (residual : profile.AboveResidual previous) :
    (profile.thresholdInput previous).threshold <
      (profile.thresholdInput previous).load := by
  cases residual.outcome with
  | aggregate ledger certificate =>
      change ledger.capacity.total < ledger.lower.total at certificate
      rw [ledger.lower.total_exact, ledger.capacity.total_exact] at certificate
      simpa [Profile.spec, Profile.canonicalMembers, Profile.memberQuery,
        Profile.capability,
        Core.Finite.Enumeration.singleton,
        Core.Finite.Enumeration.ofNodupList,
        CT14.lowerMass, CT14.upperCapacity, CT14.lowerMassEntries,
        CT14.capacityEntries, CT14.Capability.membersAt] using certificate

/-- Public projection from the exact CT14 capacity residual to the literal
predecessor-owned comparison this profile was executed on.

This is the at-or-below half of the branch fact recorded by the split: the
observed load is bounded by the threshold the registered table computes at the
observed size.  A continuation nested inside this branch may read the estimate
from here instead of assuming it. -/
theorem AtOrBelowResidual.load_le_threshold
    {previous : Previous} (residual : profile.AtOrBelowResidual previous) :
    (profile.thresholdInput previous).load ≤
      (profile.thresholdInput previous).threshold := by
  cases residual.outcome with
  | capacity ledger certificate =>
      change ledger.lower.total ≤ ledger.capacity.total at certificate
      rw [ledger.lower.total_exact, ledger.capacity.total_exact] at certificate
      simpa [Profile.spec, Profile.canonicalMembers, Profile.memberQuery,
        Profile.capability,
        Core.Finite.Enumeration.singleton,
        Core.Finite.Enumeration.ofNodupList,
        CT14.lowerMass, CT14.upperCapacity, CT14.lowerMassEntries,
        CT14.capacityEntries, CT14.Capability.membersAt] using certificate

/-- The registered-observation reading of `AboveResidual.threshold_lt_load`:
the strict-above branch of a `Registration`-backed split records that the
registered load exceeds the registered table's threshold at the registered
size. -/
theorem AboveResidual.registeredComparisonAt
    {Residual : Type uResidual}
    (registration : Registration Residual)
    (current : Query Previous fun _ => Residual) {previous : Previous}
    (residual :
      (Profile.ofRegistrationAt (Previous := Previous)
        registration current).AboveResidual previous) :
    (registration.table (current previous)).threshold
        (registration.size (current previous)) <
      registration.load (current previous) :=
  residual.threshold_lt_load

theorem AboveResidual.registeredComparison
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (registration : Registration Residual) {previous : Previous}
    (residual :
      (Profile.ofRegistration (Previous := Previous)
        registration).AboveResidual previous) :
    (registration.table (residualOf previous)).threshold
        (registration.size (residualOf previous)) <
      registration.load (residualOf previous) :=
  residual.registeredComparisonAt registration Query.residual

/-- The registered-observation reading of `AtOrBelowResidual.load_le_threshold`.

For the graph interpretation this is exactly `def:near-cubic-spine` at the
current object: `registration.load` is the object's degree surplus and
`registration.table` is the audited square-root table, so the branch records
`σ(G) ≤ (table coefficient) · ⌈√n⌉`. -/
theorem AtOrBelowResidual.registeredComparisonAt
    {Residual : Type uResidual}
    (registration : Registration Residual)
    (current : Query Previous fun _ => Residual) {previous : Previous}
    (residual :
      (Profile.ofRegistrationAt (Previous := Previous)
        registration current).AtOrBelowResidual previous) :
    registration.load (current previous) ≤
      (registration.table (current previous)).threshold
        (registration.size (current previous)) :=
  residual.load_le_threshold

theorem AtOrBelowResidual.registeredComparison
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (registration : Registration Residual) {previous : Previous}
    (residual :
      (Profile.ofRegistration (Previous := Previous)
        registration).AtOrBelowResidual previous) :
    registration.load (residualOf previous) ≤
      (registration.table (residualOf previous)).threshold
        (registration.size (residualOf previous)) :=
  residual.registeredComparisonAt registration Query.residual

/-- Public projection from the exact CT14 aggregate residual to the queried
strict comparison.  Consumers do not unfold CT14's aggregate ledger. -/
theorem AboveResidual.comparison
    (comparison : Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat)
    {previous : Previous}
    (residual :
      (Profile.ofComparisonQuery comparison).AboveResidual previous) :
    (comparison previous).threshold <
      (comparison previous).value := by
  have certificate := residual.threshold_lt_load
  rwa [ofComparisonQuery_thresholdInput, ofComparisonQuery_load] at certificate

/-- Public projection from the exact CT14 capacity residual to the queried
complementary comparison. -/
theorem AtOrBelowResidual.comparison
    (comparison : Query Previous fun _ =>
      Core.OrderThresholdSplit.Profile Nat)
    {previous : Previous}
    (residual :
      (Profile.ofComparisonQuery comparison).AtOrBelowResidual previous) :
    (comparison previous).value ≤
      (comparison previous).threshold := by
  have certificate := residual.load_le_threshold
  rwa [ofComparisonQuery_thresholdInput, ofComparisonQuery_load] at certificate

end Profile

end Hypostructure.Core.Strategy.ScaleThresholdDichotomy
