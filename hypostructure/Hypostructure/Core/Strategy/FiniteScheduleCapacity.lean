import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.FiniteScheduleCapacitySemantics

/-!
# Finite-schedule capacity

This reusable Strategy is exactly CT6 followed by CT5 followed by CT14.
All reads use public residual/ledger queries, all writes are owned by the CT
adapters, and `CTExecution.compose` retains the three exact outputs.
-/

namespace Hypostructure.Core.Strategy.FiniteScheduleCapacity

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uData

structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration : Registration.{uResidual, uData} Residual
  /-- The object this schedule audits.  It defaults to the incoming residual;
  a compiler that has already rebased onto a selected minimal counterexample
  passes that query instead, so the row schedule, the contribution family and
  the aggregate all speak about the same object as the strategies that
  produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]

def residualQuery (profile : Profile Previous Residual) :
    Query Previous fun _ => Residual :=
  profile.current

def failureOrder (profile : Profile Previous Residual) :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.registration.Index (profile.residualQuery previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.failureOrder residual

def rowSpec (profile : Profile Previous Residual) : CT6.Spec Previous where
  Index := fun previous =>
    profile.registration.Index (profile.residualQuery previous)
  FailureData := fun previous =>
    profile.registration.FailureData (profile.residualQuery previous)
  Failure := fun previous =>
    profile.registration.Failure (profile.residualQuery previous)
  failureData := fun previous index failure =>
    profile.registration.failureData
      (profile.residualQuery previous) index failure
  contribution := fun previous index =>
    profile.registration.rowContribution
      (profile.residualQuery previous) index

def rowCapability (profile : Profile Previous Residual) :
    CT6.Capability profile.rowSpec where
  failureOrder := profile.failureOrder
  failureDecidable := fun previous index =>
    profile.registration.failureDecidable
      (profile.residualQuery previous) index
  inputSize := fun previous => (profile.failureOrder previous).card
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [CT6.localCheckBound, Fintype.card_unit, Nat.pow_one,
      Nat.one_mul]
    exact Nat.le_succ _

noncomputable def rowExecution (profile : Profile Previous Residual) :
    CTExecution Previous :=
  CTAdapters.ct6 profile.rowCapability

abbrev AfterRows (profile : Profile Previous Residual) :=
  Ledger.Extension Previous profile.rowExecution.Output

def ct6Result (profile : Profile Previous Residual) :
    Query profile.AfterRows fun stage =>
      profile.rowExecution.Output stage.previous :=
  Query.latest

def residualAfterRows (profile : Profile Previous Residual) :
    Query profile.AfterRows fun _ => Residual :=
  profile.residualQuery.preserve

def ct6AndResidual (profile : Profile Previous Residual) :
    Query profile.AfterRows fun stage =>
      PProd (profile.rowExecution.Output stage.previous) Residual :=
  profile.ct6Result.and profile.residualAfterRows

def contributionSpec (profile : Profile Previous Residual) :
    CT5.Spec profile.AfterRows where
  budget := profile.registration.budget
  Site := fun stage =>
    profile.registration.Site (profile.residualAfterRows stage)
  Witness := fun stage =>
    profile.registration.Witness (profile.residualAfterRows stage)
  Active := fun stage =>
    profile.registration.Active (profile.residualAfterRows stage)
  Supports := fun stage =>
    profile.registration.Supports (profile.residualAfterRows stage)
  contribution := fun stage =>
    profile.registration.witnessContribution
      (profile.residualAfterRows stage)
  required := fun stage =>
    profile.registration.required (profile.residualAfterRows stage)
  capacity := fun stage =>
    profile.registration.capacity (profile.residualAfterRows stage)

def contributionFamily (profile : Profile Previous Residual) :
    Query profile.AfterRows fun stage =>
      Core.Finite.DependentEnumeration
        (profile.contributionSpec.Site stage)
        (profile.contributionSpec.Witness stage) :=
  profile.ct6AndResidual.dependentMap fun _ inputs =>
    profile.registration.family inputs.snd

def contributionCapability (profile : Profile Previous Residual) :
    CT5.Capability profile.contributionSpec where
  family := profile.contributionFamily
  activeDecidable := fun stage site =>
    profile.registration.activeDecidable
      (profile.residualAfterRows stage) site
  supportsDecidable := fun stage site witness =>
    profile.registration.supportsDecidable
      (profile.residualAfterRows stage) site witness
  resourceLEDecidable := profile.registration.resourceLEDecidable

noncomputable def contributionExecution
    (profile : Profile Previous Residual) :
    CTExecution profile.AfterRows :=
  CTAdapters.ct5 profile.contributionCapability

abbrev AfterContributions (profile : Profile Previous Residual) :=
  Ledger.Extension profile.AfterRows profile.contributionExecution.Output

def ct5Result (profile : Profile Previous Residual) :
    Query profile.AfterContributions fun stage =>
      profile.contributionExecution.Output stage.previous :=
  Query.latest

def residualAfterContributions (profile : Profile Previous Residual) :
    Query profile.AfterContributions fun _ => Residual :=
  profile.residualAfterRows.preserve

def ct5AndResidual (profile : Profile Previous Residual) :
    Query profile.AfterContributions fun stage =>
      PProd (profile.contributionExecution.Output stage.previous) Residual :=
  profile.ct5Result.and profile.residualAfterContributions

def aggregateSpec (profile : Profile Previous Residual) :
    CT14.Spec profile.AfterContributions where
  Member := fun stage =>
    profile.registration.Member
      (profile.residualAfterContributions stage)
  Label := fun stage =>
    profile.registration.Label
      (profile.residualAfterContributions stage)
  memberLowerMass := fun stage member =>
    profile.registration.memberLowerMass
      (profile.residualAfterContributions stage) member
  memberCapacity := fun stage member =>
    profile.registration.memberCapacity
      (profile.residualAfterContributions stage) member
  memberLabel := fun stage member =>
    profile.registration.memberLabel
      (profile.residualAfterContributions stage) member

def aggregateMembers (profile : Profile Previous Residual) :
    Query profile.AfterContributions fun stage =>
      Core.Finite.Enumeration (profile.aggregateSpec.Member stage) :=
  profile.ct5AndResidual.dependentMap fun _ inputs =>
    profile.registration.members inputs.snd

def aggregateCapability (profile : Profile Previous Residual) :
    CT14.Capability profile.aggregateSpec where
  members := profile.aggregateMembers
  labelDecidableEq := fun stage =>
    profile.registration.labelDecidableEq
      (profile.residualAfterContributions stage)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.aggregateMembers stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def aggregateExecution
    (profile : Profile Previous Residual) :
    CTExecution profile.AfterContributions :=
  CTAdapters.ct14 profile.aggregateCapability

noncomputable def execution (profile : Profile Previous Residual) :
    CTExecution Previous :=
  (CTAdapters.ct6 profile.rowCapability).compose
    ((CTAdapters.ct5 profile.contributionCapability).compose
      (CTAdapters.ct14 profile.aggregateCapability))

abbrev AfterCapacity (profile : Profile Previous Residual) :=
  Ledger.Extension Previous profile.execution.Output

def result (profile : Profile Previous Residual) :
    Query profile.AfterCapacity fun stage =>
      profile.execution.Output stage.previous :=
  Query.latest

inductive NonCapacityResidual
    (profile : Profile Previous Residual) (previous : Previous) where
  | firstFailure
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .firstFailure)
  | deficit
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (selected : output.snd.fst.terminal = .deficit)
  | c4
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (selected : output.snd.fst.terminal = .c4)
  | chargeLedger
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (selected : output.snd.fst.terminal = .chargeLedger)
  | unboundedMember
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (contributionsSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .unboundedMember)
  | missingLabel
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (contributionsSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .missingLabel)
  | aggregate
      (output : profile.execution.Output previous)
      (rowsSelected : output.fst.terminal = .activeLedger)
      (contributionsSelected : output.snd.fst.terminal = .aggregate)
      (selected : output.snd.snd.terminal = .aggregate)

structure CapacityResidual
    (profile : Profile Previous Residual) (previous : Previous) where
  output : profile.execution.Output previous
  rowsSelected : output.fst.terminal = .activeLedger
  contributionsSelected : output.snd.fst.terminal = .aggregate
  selected : output.snd.snd.terminal = .capacity

noncomputable def dichotomy (profile : Profile Previous Residual) :
    Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.NonCapacityResidual
  RightPayload := profile.CapacityResidual
  classify := fun previous =>
    let output := profile.execution.run previous
    match rowsSelected : output.fst.terminal with
    | .firstFailure =>
        .inl (.firstFailure output rowsSelected)
    | .activeLedger =>
        match contributionsSelected : output.snd.fst.terminal with
        | .deficit =>
            .inl (.deficit output rowsSelected contributionsSelected)
        | .c4 =>
            .inl (.c4 output rowsSelected contributionsSelected)
        | .chargeLedger =>
            .inl (.chargeLedger output rowsSelected contributionsSelected)
        | .aggregate =>
            match capacitySelected : output.snd.snd.terminal with
            | .unboundedMember =>
                .inl (.unboundedMember output rowsSelected
                  contributionsSelected capacitySelected)
            | .missingLabel =>
                .inl (.missingLabel output rowsSelected
                  contributionsSelected capacitySelected)
            | .aggregate =>
                .inl (.aggregate output rowsSelected
                  contributionsSelected capacitySelected)
            | .capacity =>
                .inr ⟨output, rowsSelected, contributionsSelected,
                  capacitySelected⟩

end Profile

end Hypostructure.Core.Strategy.FiniteScheduleCapacity
