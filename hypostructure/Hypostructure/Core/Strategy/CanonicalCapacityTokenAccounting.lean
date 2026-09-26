import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.CanonicalCapacityTokenAccountingSemantics

/-!
# Canonical capacity-token accounting

The Strategy is exactly CT4 followed by CT9 followed by CT14.  Later CTs read
the exact public output introduced by their literal predecessor through
`Query.latest`; CT14 uses CT9's retained CT4 stage only as the dependent type
index of its aggregate labels.  Core owns execution, ledger extension,
routing, terminals, and work accounting.
-/

namespace Hypostructure.Core.Strategy.CanonicalCapacityTokenAccounting

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uDemand uToken uRole uLabel uAggregateLabel

/-- Residual-indexed inert registration lifted to one literal predecessor. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{
      uResidual, uDemand, uToken, uRole, uLabel, uAggregateLabel} Residual
  /-- The object this token accounting audits.  It defaults to the incoming
  residual; a compiler that has already rebased onto a selected minimal
  counterexample passes that query instead, so the demand and token schedules,
  the fibre labels and the aggregate comparison all speak about the same
  object as the strategies that produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uDemand, uToken, uRole, uLabel, uAggregateLabel}
    Previous Residual)

/-- The one stable read of the audited object. -/
def residualQuery : Query Previous (fun _ => Residual) :=
  profile.current

/-- CT4 primitive assignment semantics. -/
def assignmentSpec : CT4.Spec Previous where
  Demand := fun previous =>
    profile.registration.Demand (profile.current previous)
  Payer := fun previous =>
    profile.registration.Token (profile.current previous)
  Eligible := fun previous demand token =>
    profile.registration.Eligible (profile.current previous) demand token
  demandWeight := fun previous demand =>
    profile.registration.demandWeight (profile.current previous) demand
  capacity := fun previous token =>
    profile.registration.tokenCapacity (profile.current previous) token
  required := fun previous =>
    profile.registration.required (profile.current previous)

/-- Exact residual-owned demand schedule consumed by CT4. -/
def demandQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.assignmentSpec.Demand previous) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.demands residual

/-- Exact residual-owned token schedule consumed by CT4. -/
def tokenQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.assignmentSpec.Payer previous) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.tokens residual

/-- CT4 capability derived entirely from residual-owned schedules. -/
def assignmentCapability : CT4.Capability profile.assignmentSpec where
  demands := profile.demandQuery
  payers := profile.tokenQuery
  eligibleDecidable := fun previous demand token =>
    profile.registration.eligibleDecidable
      (profile.current previous) demand token
  inputSize := fun previous =>
    CT4.localCheckBound
      (profile.demandQuery previous)
      (profile.tokenQuery previous)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The first Core-owned CT execution. -/
noncomputable def assignmentExecution :
    Core.Strategy.CTExecution Previous :=
  CTAdapters.ct4 profile.assignmentCapability

/-- Literal ledger shape after CT4. -/
abbrev AfterAssignment :=
  Ledger.Extension Previous profile.assignmentExecution.Output

/-- Exact CT4 result introduced at the newest ledger entry. -/
def assignmentResult :
    Query profile.AfterAssignment
      (fun stage => profile.assignmentExecution.Output stage.previous) :=
  Query.latest

/-- Public projection of CT4's generated first-eligible assignment table. -/
def assignedPayerQuery :
    Query profile.AfterAssignment fun stage =>
      let result := profile.assignmentResult stage
      (demand :
          profile.assignmentSpec.Demand result.stage.previous) →
        Option (profile.assignmentSpec.Payer result.stage.previous) :=
  profile.assignmentResult.dependentMap
    (Output := fun _stage result =>
      (demand :
          profile.assignmentSpec.Demand result.stage.previous) →
        Option (profile.assignmentSpec.Payer result.stage.previous))
    fun _stage result demand =>
      match result.terminal, result.outcome with
      | .missingPayer, .missingPayer assignment _ =>
          assignment.assignedPayer? demand
      | .overloadedFibre, .overloadedFibre total _ =>
          total.assignment.assignedPayer? demand
      | .c4, .c4 total _ _ =>
          total.assignment.assignedPayer? demand
      | .capacity, .capacity total _ _ =>
          total.assignment.assignedPayer? demand

/-- CT9 receives CT4's exact demand schedule through the retained result. -/
def ct9Items :
    Query profile.AfterAssignment fun stage =>
      let result := profile.assignmentResult stage
      Core.Finite.Enumeration
        (profile.assignmentSpec.Demand result.stage.previous) :=
  profile.assignmentResult.dependentMap fun _stage result =>
    profile.assignmentCapability.demandsAt result.stage.previous

/-- Complete label schedule indexed by CT4's exact predecessor. -/
def ct9Labels :
    Query profile.AfterAssignment fun stage =>
      let result := profile.assignmentResult stage
      Core.Finite.CompleteEnumeration
        (profile.registration.Label
          (profile.current result.stage.previous)) :=
  profile.assignmentResult.dependentMap fun _stage result =>
    profile.registration.completeLabels
      (profile.current result.stage.previous)

/-- CT9 labels each demand by CT4's generated payer and its residual role. -/
def fibreSpec : CT9.Spec profile.AfterAssignment where
  Item := fun stage =>
    profile.assignmentSpec.Demand
      (profile.assignmentResult stage).stage.previous
  Label := fun stage =>
    profile.registration.Label
      (profile.current
        (profile.assignmentResult stage).stage.previous)
  label := fun stage demand =>
    let result := profile.assignmentResult stage
    let residual := profile.current result.stage.previous
    profile.registration.labelOf residual
      ((profile.assignedPayerQuery stage) demand)
      (profile.registration.roleOf residual demand)
  capacity := fun stage label =>
    let result := profile.assignmentResult stage
    profile.registration.labelCapacity
      (profile.current result.stage.previous) label

/-- CT9 capability over the exact CT4 extension. -/
def fibreCapability : CT9.Capability profile.fibreSpec where
  items := profile.ct9Items
  labels := fun stage =>
    profile.ct9Labels stage
  inputSize := fun stage =>
    CT9.localCheckBound
      (profile.ct9Items stage)
      (profile.ct9Labels stage).toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The second Core-owned CT execution. -/
noncomputable def fibreExecution :
    Core.Strategy.CTExecution profile.AfterAssignment :=
  CTAdapters.ct9 profile.fibreCapability

/-- Literal ledger shape after CT9. -/
abbrev AfterFibres :=
  Ledger.Extension profile.AfterAssignment profile.fibreExecution.Output

/-- Exact CT9 result introduced at the newest ledger entry. -/
def fibreResult :
    Query profile.AfterFibres
      (fun stage => profile.fibreExecution.Output stage.previous) :=
  Query.latest

/-- Public projection of CT9's generated partition on either terminal. -/
def partitionQuery :
    Query profile.AfterFibres fun stage =>
      let result := profile.fibreResult stage
      CT9.Partition profile.fibreCapability result.stage.previous :=
  profile.fibreResult.dependentMap fun _stage result =>
    match result.terminal, result.outcome with
    | .overloaded, .overloaded partition _ => partition
    | .bounded, .bounded certificate => certificate.partition

/-- CT14 members are CT9's exact complete label schedule. -/
def aggregateMembers :
    Query profile.AfterFibres fun stage =>
      let result := profile.fibreResult stage
      Core.Finite.Enumeration
        (profile.fibreSpec.Label result.stage.previous) :=
  profile.fibreResult.dependentMap fun _stage result =>
    profile.fibreCapability.labelScheduleAt result.stage.previous

/-- CT14 primitive aggregate semantics over CT9's exact partition. -/
def aggregateSpec : CT14.Spec profile.AfterFibres where
  Member := fun stage =>
    profile.fibreSpec.Label
      (profile.fibreResult stage).stage.previous
  Label := fun stage =>
    let result := profile.fibreResult stage
    -- CT9's label family is indexed by this exact retained CT4 predecessor.
    let assignment :=
      profile.assignmentResult result.stage.previous
    profile.registration.aggregateLabel
      (profile.current assignment.stage.previous)
  memberLowerMass := fun stage label =>
    (profile.partitionQuery stage).count label
  memberCapacity := fun stage label =>
    some (profile.fibreSpec.capacity
      (profile.fibreResult stage).stage.previous label)
  memberLabel := fun stage label =>
    let result := profile.fibreResult stage
    -- This is a type index only; no CT4 outcome or assignment is inspected.
    let assignment :=
      profile.assignmentResult result.stage.previous
    some (profile.registration.memberAggregateLabel
      (profile.current assignment.stage.previous) label)

/-- CT14 capability derived from CT9's exact complete label schedule. -/
def aggregateCapability : CT14.Capability profile.aggregateSpec where
  members := profile.aggregateMembers
  labelDecidableEq := fun stage =>
    let result := profile.fibreResult stage
    -- Use the same dependent label-family index as `aggregateSpec.Label`.
    let assignment :=
      profile.assignmentResult result.stage.previous
    profile.registration.aggregateLabelDecidableEq
      (profile.current assignment.stage.previous)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.aggregateMembers stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The prescribed right-associated CT4 → CT9 → CT14 composition. -/
noncomputable def aggregateExecution :
    Core.Strategy.CTExecution profile.AfterFibres :=
  CTAdapters.ct14 profile.aggregateCapability

noncomputable def execution : Core.Strategy.CTExecution Previous :=
  profile.assignmentExecution.compose
    (profile.fibreExecution.compose profile.aggregateExecution)

/-- Literal ledger stage after the composed CT4 → CT9 → CT14 execution. -/
abbrev AfterExecution :=
  Ledger.Extension Previous profile.execution.Output

/-- Direct read of the exact composed output written by the Strategy. -/
noncomputable def executionResult :
    Query profile.AfterExecution
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- Exact CT4 payload projected from the composed ledger entry. -/
noncomputable def assignmentOutput :
    Query profile.AfterExecution
      (fun stage => profile.assignmentExecution.Output stage.previous) :=
  profile.executionResult.map fun _ output => output.fst

/-- Exact CT9 payload projected from the composed ledger entry. -/
noncomputable def fibreOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult stage
      profile.fibreExecution.Output
        (Ledger.extend stage.previous output.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.fst

/-- Exact CT14 payload projected from the composed ledger entry. -/
noncomputable def aggregateOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult stage
      let assignmentStage := Ledger.extend stage.previous output.fst
      profile.aggregateExecution.Output
        (Ledger.extend assignmentStage output.snd.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.snd

/-- The CT4 terminal read directly from the retained composed output. -/
noncomputable def assignmentTerminal :
    Query profile.AfterExecution (fun _ => CT4.Terminal) :=
  profile.assignmentOutput.map fun _ output => output.terminal

/-- The CT9 terminal read directly from the retained composed output. -/
noncomputable def fibreTerminal :
    Query profile.AfterExecution (fun _ => CT9.Terminal) :=
  profile.fibreOutput.map fun _ output => output.terminal

/-- The CT14 terminal read directly from the retained composed output. -/
noncomputable def aggregateTerminal :
    Query profile.AfterExecution (fun _ => CT14.Terminal) :=
  profile.aggregateOutput.map fun _ output => output.terminal

end Profile

end Hypostructure.Core.Strategy.CanonicalCapacityTokenAccounting
