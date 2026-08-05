import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressureSemantics

/-!
# Coupled homogeneous fibre pressure

This strategy is exactly the right-associated composition CT9 → CT13 → CT14.
CT9 reads the complete item and label schedules from the stable residual.
CT13 reads its residual-owned schedules through CT9's exact newest ledger
entry, and CT14 does the same through CT13's exact newest entry.  Core owns
all execution, routing, ledger extension, and work accounting.
-/

namespace Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uItem uToken uRole uLabel uPayer uObstruction
  uResource uMember uAggregateLabel uAmbient uBranch uLiveData uNew

structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{
      uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
      uResource, uMember, uAggregateLabel} Residual
  current : Query Previous fun _ => Residual := Query.residual

/-- The registration-level expression for one exact CT9 fibre. -/
private noncomputable def registrationFibre
    (registration : Registration.{
      uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
      uResource, uMember, uAggregateLabel} Residual)
    (residual : Residual) (label : registration.Label residual) :
    List (registration.Item residual) := by
  letI : DecidableEq (registration.Label residual) :=
    (registration.completeLabels residual).decEq
  exact (registration.items residual).values.filter fun item =>
    registration.labelOf residual item = label

/-- Exact CT9 overload retained as one dependent value: selected label,
literal computed fibre, schedule membership, fibre exactness, and strict
capacity excess. -/
private abbrev OverloadClaim
    (registration : Registration.{
      uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
      uResource, uMember, uAggregateLabel} Residual)
    (residual : Residual) :=
  Option (Sigma fun label : registration.Label residual =>
    Sigma fun fibre : List (registration.Item residual) =>
      PLift
        (label ∈ (registration.completeLabels residual).values ∧
          fibre = registrationFibre registration residual label ∧
          registration.fibreCapacity residual label < fibre.length))

/-- Public dependent view of one exact CT9 overload.  Its constructor is
private: consumers may inspect the selected label and literal fibre together
with their producer-owned laws, but cannot manufacture a collision payload. -/
structure SelectedOverload
    (registration : Registration.{
      uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
      uResource, uMember, uAggregateLabel} Residual)
    (residual : Residual) where
  private mk ::
  label : registration.Label residual
  fibre : List (registration.Item residual)
  label_member :
    label ∈ (registration.completeLabels residual).values
  item_member : ∀ item, item ∈ fibre →
    item ∈ (registration.items residual).values
  item_label : ∀ item, item ∈ fibre →
    registration.labelOf residual item = label
  fibre_nodup : fibre.Nodup
  overloaded : registration.fibreCapacity residual label < fibre.length

/-- Query-only ledger of CT9's exact selected homogeneous fibre. -/
structure OverloadLedger (Stage : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Stage Residual]
    (registration : Registration.{
      uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
      uResource, uMember, uAggregateLabel} Residual) where
  private mk ::
  current : Query Stage fun _ => Residual
  private claim : Query Stage fun stage =>
    OverloadClaim registration (current stage)

namespace OverloadLedger

variable {Stage : Type uPrevious} {Residual : Type uResidual}
variable [HasResidual Stage Residual]
variable {registration : Registration.{
  uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
  uResource, uMember, uAggregateLabel} Residual}

private def ofClaim
    (current : Query Stage fun _ => Residual)
    (claim : Query Stage fun stage =>
      OverloadClaim registration (current stage)) :
    OverloadLedger Stage Residual registration :=
  .mk current claim

/-- Read the selected label and literal fibre as one dependent value.  The
membership, same-label, and strict-overload fields are derived from CT9's
retained partition equality; the partition is not recomputed. -/
noncomputable def selected
    (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      Option (SelectedOverload registration (ledger.current stage)) :=
   fun stage => by
    cases claim_eq : ledger.claim stage with
    | none => exact none
    | some selected =>
        let label := selected.fst
        let fibre := selected.snd.fst
        have facts := selected.snd.snd.down
        have itemFacts : ∀ item, item ∈ fibre →
            item ∈ (registration.items (ledger.current stage)).values ∧
              registration.labelOf (ledger.current stage) item = label := by
          intro item member
          have filtered : item ∈
              registrationFibre registration (ledger.current stage) label := by
            rw [← facts.2.1]
            exact member
          letI : DecidableEq (registration.Label (ledger.current stage)) :=
            (registration.completeLabels (ledger.current stage)).decEq
          simpa [registrationFibre] using filtered
        exact some {
          label := label
          fibre := fibre
          label_member := facts.1
          item_member := fun item member => (itemFacts item member).1
          item_label := fun item member => (itemFacts item member).2
          fibre_nodup := by
            change selected.snd.fst.Nodup
            rw [facts.2.1]
            exact (registration.items (ledger.current stage)).nodup.filter _
          overloaded := facts.2.2 }

/-- The exact selected fibre as a duplicate-free finite schedule.  The
bounded terminal contributes the empty schedule; the overloaded terminal
uses the literal CT9 fibre and its inherited nodup proof. -/
noncomputable def selectedEnumeration
    (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      Core.Finite.Enumeration (registration.Item (ledger.current stage)) :=
   fun stage => by
    cases selected_eq : ledger.selected stage with
    | none =>
        letI : DecidableEq (registration.Item (ledger.current stage)) :=
          (registration.items (ledger.current stage)).decEq
        exact Core.Finite.Enumeration.empty _
    | some selected =>
        exact {
          values := selected.fibre
          nodup := selected.fibre_nodup
          decEq := (registration.items (ledger.current stage)).decEq }

/-- CT9's exact first overloaded label. -/
def selectedLabel (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      Option (registration.Label (ledger.current stage)) :=
  ledger.claim.map fun _ claim => claim.map Sigma.fst

/-- The literal fibre retained with the selected label. -/
def selectedFibre (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      Option (List (registration.Item (ledger.current stage))) :=
  ledger.claim.map fun _ claim => claim.map fun selected => selected.snd.fst

/-- Schedule membership of the exact selected label. -/
def labelMember (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      match ledger.selectedLabel stage with
      | none => PUnit
      | some label =>
          PLift (label ∈
            (registration.completeLabels (ledger.current stage)).values) :=
   fun stage => by
    change match (ledger.claim stage).map Sigma.fst with
      | none => PUnit
      | some label =>
          PLift (label ∈
            (registration.completeLabels (ledger.current stage)).values)
    cases claim_eq : ledger.claim stage with
    | none => exact PUnit.unit
    | some selected => exact PLift.up selected.snd.snd.down.1

/-- Exactness of the retained fibre against the registration's literal item
schedule and label map. -/
def fibreExact (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      match ledger.claim stage with
      | none => PUnit
      | some selected =>
          PLift (selected.snd.fst =
            registrationFibre registration (ledger.current stage)
              selected.fst) :=
  fun stage => by
    change match ledger.claim stage with
      | none => PUnit
      | some selected =>
          PLift (selected.snd.fst =
            registrationFibre registration (ledger.current stage)
              selected.fst)
    cases claim_eq : ledger.claim stage with
    | none => exact PUnit.unit
    | some selected => exact PLift.up selected.snd.snd.down.2.1

/-- Strict capacity excess of the literal retained fibre. -/
def overloaded (ledger : OverloadLedger Stage Residual registration) :
    Query Stage fun stage =>
      match ledger.claim stage with
      | none => PUnit
      | some selected =>
          PLift (registration.fibreCapacity (ledger.current stage) selected.fst <
            selected.snd.fst.length) :=
  fun stage => by
    change match ledger.claim stage with
      | none => PUnit
      | some selected =>
          PLift (registration.fibreCapacity (ledger.current stage)
            selected.fst < selected.snd.fst.length)
    cases claim_eq : ledger.claim stage with
    | none => exact PUnit.unit
    | some selected => exact PLift.up selected.snd.snd.down.2.2

/-- Preserve the exact overload through a residual-preserving stage
projection. -/
def comap {NewStage : Type uNew} [HasResidual NewStage Residual]
    (ledger : OverloadLedger Stage Residual registration)
    (project : NewStage → Stage)
    (current : Query NewStage fun _ => Residual)
    (current_eq : ∀ stage,
      ledger.current (project stage) = current stage) :
    OverloadLedger NewStage Residual registration :=
  ofClaim current ( fun stage =>
    Eq.mp (congrArg (OverloadClaim registration) (current_eq stage))
      (ledger.claim (project stage)))

end OverloadLedger

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uItem, uToken, uRole, uLabel, uPayer, uObstruction,
    uResource, uMember, uAggregateLabel} Previous Residual)

def residualQuery : Query Previous fun _ => Residual :=
  profile.current

def itemQuery : Query Previous fun previous =>
    Core.Finite.Enumeration
      (profile.registration.Item (profile.current previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.items residual

def completeLabelQuery : Query Previous fun previous =>
    Core.Finite.CompleteEnumeration
      (profile.registration.Label (profile.current previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeLabels residual

def overloadSpec : CT9.Spec Previous where
  Item := fun previous =>
    profile.registration.Item (profile.current previous)
  Label := fun previous =>
    profile.registration.Label (profile.current previous)
  label := fun previous item =>
    profile.registration.labelOf (profile.current previous) item
  capacity := fun previous label =>
    profile.registration.fibreCapacity (profile.current previous) label

def overloadCapability : CT9.Capability profile.overloadSpec where
  items := profile.itemQuery
  labels := fun previous => profile.completeLabelQuery previous
  inputSize := fun previous =>
    CT9.localCheckBound
      (profile.itemQuery previous)
      (profile.completeLabelQuery previous).toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def overloadExecution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct9 profile.overloadCapability

abbrev AfterOverload :=
  Ledger.Extension Previous profile.overloadExecution.Output

def overloadResult :
    Query profile.AfterOverload
      (fun stage => profile.overloadExecution.Output stage.previous) :=
  Query.latest

def payerQuery :
    Query profile.AfterOverload fun stage =>
      let result := profile.overloadResult stage
      Core.Finite.Enumeration
        (profile.registration.Payer
          (profile.current result.stage.previous)) :=
  profile.overloadResult.dependentMap fun _stage result =>
    profile.registration.payers (profile.current result.stage.previous)

def obstructionQuery :
    Query profile.AfterOverload fun stage =>
      let result := profile.overloadResult stage
      CT13.ObstructionSchedule
        (profile.registration.Obstruction
          (profile.current result.stage.previous)) :=
  profile.overloadResult.dependentMap fun _stage result =>
    profile.registration.obstructions (profile.current result.stage.previous)

def tierTwoQuery :
    Query profile.AfterOverload fun stage =>
      let result := profile.overloadResult stage
      (obstruction :
          profile.registration.Obstruction
            (profile.current result.stage.previous)) →
        Core.Finite.Enumeration
          (profile.registration.Payer
            (profile.current result.stage.previous)) :=
  profile.overloadResult.dependentMap fun _stage result =>
    profile.registration.tierTwo (profile.current result.stage.previous)

def reconciliationSpec : CT13.Spec profile.AfterOverload where
  Payer := fun stage =>
    let result := profile.overloadResult stage
    profile.registration.Payer (profile.current result.stage.previous)
  Obstruction := fun stage =>
    let result := profile.overloadResult stage
    profile.registration.Obstruction (profile.current result.stage.previous)
  Resource := fun stage =>
    let result := profile.overloadResult stage
    profile.registration.Resource (profile.current result.stage.previous)
  Eligible := fun stage payer =>
    let result := profile.overloadResult stage
    profile.registration.Eligible
      (profile.current result.stage.previous) payer
  obstructionCost := fun stage obstruction =>
    let result := profile.overloadResult stage
    profile.registration.obstructionCost
      (profile.current result.stage.previous) obstruction
  payerResource := fun stage payer =>
    let result := profile.overloadResult stage
    profile.registration.payerResource
      (profile.current result.stage.previous) payer
  charge := fun stage payer =>
    let result := profile.overloadResult stage
    profile.registration.charge
      (profile.current result.stage.previous) payer
  demand := fun stage =>
    let result := profile.overloadResult stage
    profile.registration.demand (profile.current result.stage.previous)

def reconciliationCapability :
    CT13.Capability profile.reconciliationSpec where
  payers := profile.payerQuery
  obstructions := profile.obstructionQuery
  tierTwo := profile.tierTwoQuery
  eligibleDecidable := fun stage payer =>
    let result := profile.overloadResult stage
    profile.registration.eligibleDecidable
      (profile.current result.stage.previous) payer
  resourceDecidableEq := fun stage =>
    let result := profile.overloadResult stage
    profile.registration.resourceDecidableEq
      (profile.current result.stage.previous)
  inputSize := fun stage =>
    CT13.localCheckBound
      (profile.payerQuery stage)
      (profile.obstructionQuery stage)
      (profile.tierTwoQuery stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def reconciliationExecution :
    Core.Strategy.CTExecution profile.AfterOverload :=
  CTAdapters.ct13 profile.reconciliationCapability

abbrev AfterReconciliation :=
  Ledger.Extension profile.AfterOverload
    profile.reconciliationExecution.Output

def reconciliationResult :
    Query profile.AfterReconciliation
      (fun stage =>
        profile.reconciliationExecution.Output stage.previous) :=
  Query.latest

def pressureMembers :
    Query profile.AfterReconciliation fun stage =>
      let result := profile.reconciliationResult stage
      Core.Finite.Enumeration
        (profile.registration.Member
          (profile.current result.stage.previous.previous)) :=
  profile.reconciliationResult.dependentMap fun _stage result =>
    profile.registration.members
      (profile.current result.stage.previous.previous)

def pressureSpec : CT14.Spec profile.AfterReconciliation where
  Member := fun stage =>
    let result := profile.reconciliationResult stage
    profile.registration.Member
      (profile.current result.stage.previous.previous)
  Label := fun stage =>
    let result := profile.reconciliationResult stage
    profile.registration.AggregateLabel
      (profile.current result.stage.previous.previous)
  memberLowerMass := fun stage member =>
    let result := profile.reconciliationResult stage
    profile.registration.memberLowerMass
      (profile.current result.stage.previous.previous) member
  memberCapacity := fun stage member =>
    let result := profile.reconciliationResult stage
    profile.registration.memberCapacity
      (profile.current result.stage.previous.previous) member
  memberLabel := fun stage member =>
    let result := profile.reconciliationResult stage
    profile.registration.memberLabel
      (profile.current result.stage.previous.previous) member

def pressureCapability : CT14.Capability profile.pressureSpec where
  members := profile.pressureMembers
  labelDecidableEq := fun stage =>
    profile.registration.aggregateLabelDecidableEq
      (profile.current
        (profile.reconciliationResult stage).stage.previous.previous)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.pressureMembers stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def pressureExecution :
    Core.Strategy.CTExecution profile.AfterReconciliation :=
  CTAdapters.ct14 profile.pressureCapability

noncomputable def execution : Core.Strategy.CTExecution Previous :=
  profile.overloadExecution.compose
    (profile.reconciliationExecution.compose profile.pressureExecution)

/-- Literal ledger stage after the composed CT9 → CT13 → CT14 execution. -/
abbrev AfterExecution :=
  Ledger.Extension Previous profile.execution.Output

/-- Direct read of the exact composed output written by the Strategy. -/
noncomputable def executionResult :
    Query profile.AfterExecution
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- Exact CT9 payload projected from the composed ledger entry. -/
noncomputable def overloadOutput :
    Query profile.AfterExecution
      (fun stage => profile.overloadExecution.Output stage.previous) :=
  profile.executionResult.map fun _ output => output.fst

/-- Exact CT13 payload projected from the composed ledger entry. -/
noncomputable def reconciliationOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult stage
      profile.reconciliationExecution.Output
        (Ledger.extend stage.previous output.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.fst

/-- Exact CT14 payload projected from the composed ledger entry. -/
noncomputable def pressureOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult stage
      let overloadStage := Ledger.extend stage.previous output.fst
      profile.pressureExecution.Output
        (Ledger.extend overloadStage output.snd.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.snd

/-- The CT9 terminal read directly from the retained composed output. -/
noncomputable def overloadTerminal :
    Query profile.AfterExecution (fun _ => CT9.Terminal) :=
  profile.overloadOutput.map fun _ output => output.terminal

/-- The CT13 terminal read directly from the retained composed output. -/
noncomputable def reconciliationTerminal :
    Query profile.AfterExecution (fun _ => CT13.Terminal) :=
  profile.reconciliationOutput.map fun _ output => output.terminal

/-- The CT14 terminal read directly from the retained composed output. -/
noncomputable def pressureTerminal :
    Query profile.AfterExecution (fun _ => CT14.Terminal) :=
  profile.pressureOutput.map fun _ output => output.terminal

/-! ## Exact live homogeneous-fibre ledger -/

/-- Read CT9's exact selected overload from the literal output of the full
CT9 → CT13 → CT14 composition.  The selected fibre is copied from the
retained partition; this function never recomputes CT9. -/
private noncomputable def overloadClaimLive
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {Previous : Type (max uAmbient uBranch uLiveData)}
    [HasResidual Previous (Core.Strategy.ProblemInput P)]
    (profile : Profile.{
      max uAmbient uBranch uLiveData, max uAmbient uBranch,
      uLiveData, uLiveData, uLiveData, uLiveData, uLiveData, uLiveData,
      uLiveData, uLiveData, uLiveData}
      Previous (Core.Strategy.ProblemInput P))
    (certify : (stage : Previous) →
      Sigma (profile.execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object))) :
    Query
      (Core.Strategy.HaltingProgram.LiveExtension T Previous
        profile.execution.toContract certify)
      (fun live => OverloadClaim profile.registration
        ((Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
          (T := T) profile.current) live)) :=
   fun live => by
    let composed := (profile.execution.liveOutputQuery certify) live
    let overloadOutput := composed.fst
    have composed_eq : composed = profile.execution.run live.previous :=
      Core.Strategy.CTExecution.read_liveOutputQuery
        profile.execution certify live
    have previous_eq : overloadOutput.stage.previous = live.previous := by
      change composed.fst.stage.previous = live.previous
      rw [composed_eq]
      exact CT9.run_previous profile.overloadSpec
        profile.overloadCapability _
    match terminal : overloadOutput.terminal,
        outcome : overloadOutput.outcome with
    | .overloaded, .overloaded partition overloaded =>
        let label := overloaded.label
        let fibre := partition.fibres label
        have member :
            label ∈
              (profile.registration.completeLabels
                (profile.current overloadOutput.stage.previous)).values := by
          exact overloaded.scheduled
        have items_read :
            profile.overloadCapability.itemsAt overloadOutput.stage.previous =
              profile.registration.items
                (profile.current overloadOutput.stage.previous) := by
          rfl
        have fibre_exact :
            fibre = registrationFibre profile.registration
              (profile.current overloadOutput.stage.previous) label := by
          letI : DecidableEq
              (profile.registration.Label
                (profile.current overloadOutput.stage.previous)) :=
            (profile.registration.completeLabels
              (profile.current overloadOutput.stage.previous)).decEq
          dsimp only [fibre]
          rw [partition.fibres_exact label]
          unfold CT9.fibre registrationFibre
          rw [items_read]
          change
            List.filter
                (fun item => decide
                  (profile.registration.labelOf
                    (profile.current overloadOutput.stage.previous) item = label))
                (profile.registration.items
                  (profile.current overloadOutput.stage.previous)).values =
              List.filter
                (fun item => decide
                  (profile.registration.labelOf
                    (profile.current overloadOutput.stage.previous) item = label))
                (profile.registration.items
                  (profile.current overloadOutput.stage.previous)).values
          rfl
        have strict :
            profile.registration.fibreCapacity
                (profile.current overloadOutput.stage.previous) label <
              fibre.length := by
          change
            profile.overloadSpec.capacity overloadOutput.stage.previous
                overloaded.label <
              partition.count overloaded.label
          exact overloaded.overloaded
        have current_eq :
            profile.current overloadOutput.stage.previous =
              (Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
                (T := T) profile.current) live := by
          rw [previous_eq]
          rfl
        exact Eq.mp
          (congrArg (OverloadClaim profile.registration) current_eq)
          (some ⟨label, fibre,
            PLift.up ⟨member, fibre_exact, strict⟩⟩)
    | .bounded, .bounded _ => exact none

/-- Public query-only ledger of the exact homogeneous fibre selected by CT9
inside the live coupled-pressure strategy. -/
noncomputable def overloadLedgerLive
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {Previous : Type (max uAmbient uBranch uLiveData)}
    [HasResidual Previous (Core.Strategy.ProblemInput P)]
    (profile : Profile.{
      max uAmbient uBranch uLiveData, max uAmbient uBranch,
      uLiveData, uLiveData, uLiveData, uLiveData, uLiveData, uLiveData,
      uLiveData, uLiveData, uLiveData}
      Previous (Core.Strategy.ProblemInput P))
    (certify : (stage : Previous) →
      Sigma (profile.execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object))) :
    OverloadLedger
      (Core.Strategy.HaltingProgram.LiveExtension T Previous
        profile.execution.toContract certify)
      (Core.Strategy.ProblemInput P) profile.registration :=
  OverloadLedger.ofClaim
    (Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
      (T := T) profile.current)
    (profile.overloadClaimLive certify)

end Profile

end Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure
