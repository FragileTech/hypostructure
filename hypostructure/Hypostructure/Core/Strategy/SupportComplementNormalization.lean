import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.SupportComplementNormalizationSemantics
import Hypostructure.Core.Strategy.ObstructionPackingClosure

/-!
# Support-complement normalization

This domain-neutral Strategy is exactly CT9 followed by CT14 followed by CT1
followed by CT6.  CT9 creates the exact selected/complement partition.  CT14
records the complement-mass comparison.  CT1 exhausts the exact obstruction
schedule restricted by that generated state.  CT6 performs the final ordered
local-core scan.

Every inherited value is an exact query on the literal predecessor.  Every
later phase is indexed by the exact output of the preceding composed
execution.  Core's `CTExecution.compose` owns all intermediate ledger
extensions; this module contains no registration, author-facing constructor,
router, executor callback, or direct ledger write.
-/

namespace Hypostructure.Core.Strategy.SupportComplementNormalization

open Hypostructure
open Hypostructure.Core.Residual

universe u uResidual uStage uAmbient uPiece

/-- Query-only structural view of one literal normalized-support output.

The carrier families and every fact remain indexed by the current ledger
stage.  Preservation through later strategies is therefore ordinary query
composition: no complement, local-piece schedule, or CT6 decision is
recomputed from the stable residual. -/
structure ExactLedger (Stage : Type uStage)
    (Residual : Type uResidual) [HasResidual Stage Residual]
    (AmbientItem : Stage → Type uAmbient) where
  LocalPiece : Stage → Type uPiece
  Failure : (stage : Stage) → LocalPiece stage → Prop
  complement : Query Stage fun stage =>
    Core.Finite.Enumeration (AmbientItem stage)
  localPieces : Query Stage fun stage =>
    Core.Finite.Enumeration (LocalPiece stage)
  active : Query Stage fun stage =>
    ∀ piece, piece ∈ (localPieces.read stage).values →
      ¬ Failure stage piece
  sourceResidual : Query Stage fun _ => Residual := Query.residual

namespace ExactLedger

universe uNew

variable {Stage : Type uStage} {Residual : Type uResidual}
variable [HasResidual Stage Residual]

/-- Transport the exact structural queries through a framework-owned stage
projection.  The residual law records that the projection is a genuine
predecessor projection rather than a change of mathematical input. -/
def comap {NewStage : Type uNew} [HasResidual NewStage Residual]
    (ledger : ExactLedger Stage Residual AmbientItem)
    (project : NewStage → Stage)
    (_residual_eq : ∀ stage,
      residualOf (project stage) = (residualOf stage : Residual)) :
    ExactLedger NewStage Residual (fun stage => AmbientItem (project stage)) where
  LocalPiece := fun stage => ledger.LocalPiece (project stage)
  Failure := fun stage => ledger.Failure (project stage)
  complement := ledger.complement.comap project
  localPieces := ledger.localPieces.comap project
  active := ledger.active.comap project
  sourceResidual := ledger.sourceResidual.comap project

/-- Reindex through a residual-preserving projection when the consumer names
the ambient carrier through its own (propositionally equal) residual view.
This is the standard dependent-query transport used by DAG composition. -/
def comapTo {NewStage : Type uNew} [HasResidual NewStage Residual]
    (ledger : ExactLedger Stage Residual AmbientItem)
    (project : NewStage → Stage)
    (_residual_eq : ∀ stage,
      residualOf (project stage) = (residualOf stage : Residual))
    (NewAmbient : NewStage → Type uAmbient)
    (ambient_eq : ∀ stage, AmbientItem (project stage) = NewAmbient stage) :
    ExactLedger NewStage Residual NewAmbient where
  LocalPiece := fun stage => ledger.LocalPiece (project stage)
  Failure := fun stage => ledger.Failure (project stage)
  complement := Query.ofFunction fun stage =>
    ambient_eq stage ▸ ledger.complement.read (project stage)
  localPieces := ledger.localPieces.comap project
  active := ledger.active.comap project
  sourceResidual := ledger.sourceResidual.comap project

def preserve {Added : Stage → Type uNew}
    (ledger : ExactLedger Stage Residual AmbientItem) :
    ExactLedger (Ledger.Extension Stage Added) Residual
      (fun stage => AmbientItem stage.previous) :=
  ledger.comap Ledger.Extension.previous (fun _ => rfl)

def preserveProp {Added : Stage → Prop}
    (ledger : ExactLedger Stage Residual AmbientItem) :
    ExactLedger (Ledger.Extension Stage Added) Residual
      (fun stage => AmbientItem stage.previous) :=
  ledger.comap Ledger.Extension.previous (fun _ => rfl)

end ExactLedger

/-! ## CT9: exact selected/complement partition -/

/-- Inert membership interpretation over two exact predecessor queries.

The profile contains no selected fibre, complement, CT9 result, terminal, or
route. -/
structure PartitionProfile (Previous : Type u) where
  AmbientItem : Previous → Type u
  ambientSupport : Query Previous fun previous =>
    Core.Finite.Enumeration (AmbientItem previous)
  SelectedPacking : Previous → Type u
  selectedPacking : Query Previous SelectedPacking
  Selected : (previous : Previous) →
    SelectedPacking previous → AmbientItem previous → Prop
  selectedDecidable : (previous : Previous) →
    (packing : SelectedPacking previous) →
    (item : AmbientItem previous) →
      Decidable (Selected previous packing item)

namespace PartitionProfile

variable (profile : PartitionProfile Previous)

/-- Exact packing and ambient-support values at the identical predecessor. -/
def inputs :=
  profile.selectedPacking.and profile.ambientSupport

/-- Completeness of the universal support-membership labels. -/
def completeMembershipLabels :
    Core.Finite.CompleteEnumeration Bool :=
  Core.Finite.CompleteEnumeration.ofFinEnum
    (FinEnum.ofList [false, true] (by
      intro label
      cases label <;> simp))

/-- CT9 primitive semantics on the literal predecessor. -/
def spec : CT9.Spec Previous where
  Item := profile.AmbientItem
  Label := fun _ => Bool
  label := fun previous item =>
    let values := profile.inputs.read previous
    letI : Decidable (profile.Selected previous values.fst item) :=
      profile.selectedDecidable previous values.fst item
    decide (profile.Selected previous values.fst item)
  capacity := fun previous _ =>
    (profile.inputs.read previous).snd.card

/-- CT9 capability derived only from the exact queried ambient schedule. -/
def capability : CT9.Capability profile.spec where
  items := profile.ambientSupport
  labels := fun _ => completeMembershipLabels
  inputSize := fun previous =>
    CT9.localCheckBound
      (profile.ambientSupport.read previous)
      completeMembershipLabels.toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- First canonical CT execution before retaining its literal predecessor
identity. -/
private noncomputable def rawExecution : CTExecution.{u, 0, u} Previous :=
  CTAdapters.ct9 profile.capability

/-- CT9's sealed result together with its literal predecessor identity. -/
structure ExactResult (previous : Previous)
    extends (rawExecution profile).Output previous where
  previous_eq : toExecutionResult.stage.previous = previous

/-- First canonical CT execution, with the result's literal predecessor
retained in its dependent output type. -/
noncomputable def execution : CTExecution.{u, 0, u} Previous where
  Terminal := (rawExecution profile).Terminal
  Output := ExactResult profile
  run := fun previous =>
    { toExecutionResult := (rawExecution profile).run previous
      previous_eq := rfl }
  terminal := fun previous result =>
    (rawExecution profile).terminal previous result.toExecutionResult
  checks := (rawExecution profile).checks
  work := (rawExecution profile).work

/-- Literal accumulated-ledger shape after CT9. -/
abbrev AfterPartition :=
  Ledger.Extension Previous profile.execution.Output

/-- Exact CT9 output at the newest ledger entry. -/
def result :
    Query profile.AfterPartition
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- The exact generated partition on either exhaustive CT9 terminal. -/
def generatedPartition :
    Query profile.AfterPartition fun stage =>
      let result := profile.result.read stage
      CT9.Partition profile.capability result.stage.previous :=
  profile.result.dependentMap fun _ result =>
    match result.terminal, result.outcome with
    | .overloaded, .overloaded partition _ => partition
    | .bounded, .bounded certificate => certificate.partition

/-- Project one literal CT9 fibre without rebuilding its members. -/
def fibre (label : Bool) :
    Query profile.AfterPartition fun stage =>
      let result := profile.result.read stage
      Core.Finite.Enumeration
        (profile.spec.Item result.stage.previous) :=
  profile.generatedPartition.dependentMap fun stage partition => by
    let result := profile.result.read stage
    letI : DecidableEq
        (profile.spec.Item result.stage.previous) :=
      (profile.capability.itemsAt result.stage.previous).decEq
    exact Core.Finite.Enumeration.ofNodupList
      (partition.fibres label)
      (partition.fibres_nodup label)

/-- The newest ledger entry is the literal CT9 result. -/
@[simp] theorem result_read (stage : profile.AfterPartition) :
    profile.result.read stage = stage.added := rfl

/-- Exact selected fibre generated by CT9. -/
def selectedFibre := profile.fibre true

/-- Exact complementary fibre generated by CT9. -/
def complementFibre := profile.fibre false

/-- Read CT9's literal complementary fibre at the predecessor retained by the
exact CT9 execution result.  The cast uses only the result's framework-owned
predecessor identity; no member is filtered or reconstructed. -/
def complementAtPrevious (previous : Previous)
    (result : profile.execution.Output previous) :
    Core.Finite.Enumeration (profile.AmbientItem previous) :=
  cast
    (congrArg
      (fun predecessor =>
        Core.Finite.Enumeration (profile.AmbientItem predecessor))
      result.previous_eq)
    (profile.complementFibre.read (Ledger.extend previous result))

private theorem mem_castEnumeration_iff
    (source target : Previous) (equal : source = target)
    (schedule : Core.Finite.Enumeration (profile.AmbientItem source))
    (Property : (previous : Previous) →
      profile.AmbientItem previous → Prop)
    (characterization :
      ∀ item, item ∈ schedule.values ↔ Property source item)
    (item : profile.AmbientItem target) :
    item ∈
        (cast
          (congrArg
            (fun predecessor =>
              Core.Finite.Enumeration (profile.AmbientItem predecessor))
            equal)
          schedule).values ↔
      Property target item := by
  subst target
  simpa using characterization item

/-- Membership in the transported exact complement is CT9's own false-label
fibre characterization at the retained predecessor. -/
theorem mem_complementAtPrevious_iff (previous : Previous)
    (result : profile.execution.Output previous)
    (item : profile.AmbientItem previous) :
    item ∈ (profile.complementAtPrevious previous result).values ↔
      item ∈ (profile.ambientSupport.read previous).values ∧
        ¬ profile.Selected previous
          (profile.selectedPacking.read previous) item := by
  let Property : (predecessor : Previous) →
      profile.AmbientItem predecessor → Prop :=
    fun predecessor candidate =>
      candidate ∈ (profile.ambientSupport.read predecessor).values ∧
        ¬ profile.Selected predecessor
          (profile.selectedPacking.read predecessor) candidate
  have fibreCharacterization (predecessor : Previous)
      (sourceItem : profile.AmbientItem predecessor) :
      sourceItem ∈
          (CT9.fibre profile.capability predecessor false) ↔
        Property predecessor sourceItem := by
    simp only [CT9.fibre, CT9.Capability.itemsAt,
      PartitionProfile.capability, PartitionProfile.spec,
      PartitionProfile.inputs, Property]
    constructor
    · intro member
      have filtered := List.mem_filter.mp member
      exact ⟨filtered.1, by simpa using filtered.2⟩
    · rintro ⟨ambient, notSelected⟩
      exact List.mem_filter.mpr ⟨ambient, by simp [notSelected]⟩
  have sourceCharacterization
      (sourceItem : profile.AmbientItem result.stage.previous) :
      sourceItem ∈
          (profile.complementFibre.read
            (Ledger.extend previous result)).values ↔
        Property result.stage.previous sourceItem := by
    change sourceItem ∈
        (profile.generatedPartition.read
          (Ledger.extend previous result)).fibres false ↔ _
    rw [(profile.generatedPartition.read
      (Ledger.extend previous result)).fibres_exact false]
    exact fibreCharacterization result.stage.previous sourceItem
  exact mem_castEnumeration_iff profile
    result.stage.previous previous result.previous_eq
    (profile.complementFibre.read (Ledger.extend previous result))
    Property sourceCharacterization item

/-- The retained complementary fibre is exactly CT9's own generated fibre for
the unselected label.  Nothing is re-enumerated: the identity is CT9's
`Partition.fibres_exact`. -/
theorem complementFibre_card (stage : profile.AfterPartition) :
    (profile.complementFibre.read stage).card =
      (CT9.fibre profile.capability
        (profile.result.read stage).stage.previous false).length := by
  have exactFibres :=
    (profile.generatedPartition.read stage).fibres_exact false
  simp [complementFibre, fibre, Core.Finite.Enumeration.card,
    Core.Finite.Enumeration.ofNodupList, exactFibres]

end PartitionProfile

/-! ## CT14: exact complement-mass comparison -/

/-- Inert mass interpretation indexed by CT9's exact output and inherited
density-cap payload. -/
structure MassProfile {Previous : Type u}
    (partition : PartitionProfile Previous) where
  DensityCap : Previous → Type u
  densityCap : Query Previous DensityCap
  lowerMass : (previous : Previous) →
    DensityCap previous →
    partition.execution.Output previous → Nat

namespace MassProfile

variable {partition : PartitionProfile Previous}
variable (profile : MassProfile partition)

/-- Exact inherited cap paired with CT9's newest output. -/
def inputs :=
  profile.densityCap.preserve.and partition.result

/-- Universal singleton schedule for the sole aggregate comparison. -/
def members (partition : PartitionProfile Previous) :
    Query partition.AfterPartition fun _ =>
      Core.Finite.Enumeration Unit :=
  Query.ofFunction fun _ => Core.Finite.Enumeration.singleton ()

/-- CT14 compares the inherited lower mass with CT9's literal complement
cardinality. -/
def spec : CT14.Spec partition.AfterPartition where
  Member := fun _ => Unit
  Label := fun _ => Unit
  memberLowerMass := fun stage _ =>
    let values := profile.inputs.read stage
    profile.lowerMass stage.previous values.fst values.snd
  memberCapacity := fun stage _ =>
    some (partition.complementFibre.read stage).card
  memberLabel := fun _ _ => some ()

/-- CT14 capability derived from the exact singleton schedule. -/
def capability : CT14.Capability profile.spec where
  members := members partition
  labelDecidableEq := fun _ => inferInstanceAs (DecidableEq Unit)
  inputSize := fun stage =>
    CT14.localCheckBound ((members partition).read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- Second canonical CT execution before retaining its literal predecessor
identity. -/
private noncomputable def rawExecution :
    CTExecution.{u, 0, u} partition.AfterPartition :=
  CTAdapters.ct14 profile.capability

/-- CT14's sealed result together with its literal predecessor identity. -/
structure ExactResult (previous : partition.AfterPartition)
    extends (rawExecution profile).Output previous where
  previous_eq : toExecutionResult.stage.previous = previous

/-- Second canonical CT execution on CT9's literal extension, retaining that
exact extension in its dependent output type. -/
noncomputable def execution :
    CTExecution.{u, 0, u} partition.AfterPartition where
  Terminal := (rawExecution profile).Terminal
  Output := ExactResult profile
  run := fun previous =>
    { toExecutionResult := (rawExecution profile).run previous
      previous_eq := rfl }
  terminal := fun previous result =>
    (rawExecution profile).terminal previous result.toExecutionResult
  checks := (rawExecution profile).checks
  work := (rawExecution profile).work

private theorem noUnbounded
    (result : profile.execution.Output previous)
    (selected : result.terminal = .unboundedMember) : False := by
  have outcome :
      CT14.Outcome profile.capability result.stage.previous
        .unboundedMember := by
    simpa [selected] using result.outcome
  cases outcome with
  | unboundedMember _ residual =>
      have impossible := residual.holds
      simp [spec] at impossible

private theorem noMissingLabel
    (result : profile.execution.Output previous)
    (selected : result.terminal = .missingLabel) : False := by
  have outcome :
      CT14.Outcome profile.capability result.stage.previous
        .missingLabel := by
    simpa [selected] using result.outcome
  cases outcome with
  | missingLabel _ _ residual =>
      have impossible := residual.holds
      simp [spec] at impossible

/-- CT14's own generated lower-mass total on the singleton comparison
schedule is exactly the inherited density-cap observation. -/
theorem lowerMass_eq (stage : partition.AfterPartition) :
    CT14.lowerMass profile.capability stage =
      profile.lowerMass stage.previous
        (profile.densityCap.read stage.previous)
        (partition.result.read stage) := by
  simp [CT14.lowerMass, CT14.lowerMassEntries, CT14.Capability.membersAt,
    capability, members, spec, inputs, Core.Finite.Enumeration.singleton,
    Core.Finite.Enumeration.ofNodupList]
  rfl

/-- CT14's own generated capacity total is exactly CT9's retained
complementary fibre cardinality. -/
theorem upperCapacity_eq (stage : partition.AfterPartition) :
    CT14.upperCapacity profile.capability stage =
      (partition.complementFibre.read stage).card := by
  simp [CT14.upperCapacity, CT14.capacityEntries, CT14.Capability.membersAt,
    capability, members, spec, Core.Finite.Enumeration.singleton,
    Core.Finite.Enumeration.ofNodupList]

end MassProfile

/-! ## CT1: exact complement obstruction scan -/

/-- Exact CT9 → CT14 execution used as the sole CT1 predecessor. -/
noncomputable def throughMassExecution
    {Previous : Type u}
    (partition : PartitionProfile Previous)
    (mass : MassProfile partition) :
    CTExecution.{u, 0, u} Previous :=
  partition.execution.compose mass.execution

/-- Inert obstruction interpretation indexed by the exact CT9 → CT14 output.

`SupportedByComplement` is the domain predicate used by the canonical finite
`Enumeration.subtype` operation.  No filtered schedule, hit, avoidance
certificate, or terminal is accepted here. -/
structure ObstructionProfile {Previous : Type u}
    (partition : PartitionProfile Previous)
    (mass : MassProfile partition) where
  Obstruction : Previous → Type u
  obstructionSchedule : Query Previous fun previous =>
    Core.Finite.Enumeration (Obstruction previous)
  SupportedByComplement : (previous : Previous) →
    (output : (throughMassExecution partition mass).Output previous) →
    Obstruction previous → Prop
  supportedDecidable : (previous : Previous) →
    (output : (throughMassExecution partition mass).Output previous) →
    (obstruction : Obstruction previous) →
      Decidable (SupportedByComplement previous output obstruction)
  Realizes : (previous : Previous) →
    (output : (throughMassExecution partition mass).Output previous) →
    Obstruction previous → Prop
  realizesDecidable : (previous : Previous) →
    (output : (throughMassExecution partition mass).Output previous) →
    (obstruction : Obstruction previous) →
      Decidable (Realizes previous output obstruction)

namespace ObstructionProfile

variable {partition : PartitionProfile Previous}
variable {mass : MassProfile partition}
variable (profile : ObstructionProfile partition mass)

/-- Literal ledger shape after the exact CT9 → CT14 execution. -/
abbrev AfterMass
    (partition : PartitionProfile Previous)
    (mass : MassProfile partition) :=
  Ledger.Extension Previous (throughMassExecution partition mass).Output

/-- Exact composed CT9 → CT14 result. -/
def massResult
    (partition : PartitionProfile Previous)
    (mass : MassProfile partition) :
    Query (AfterMass partition mass)
      (fun stage =>
        (throughMassExecution partition mass).Output stage.previous) :=
  Query.latest

/-- Exact inherited obstruction schedule paired with the newest composed
output. -/
def inputs :=
  profile.obstructionSchedule.preserve.and (massResult partition mass)

/-- Exact complement-supported obstruction schedule. -/
def candidates :
    Query (AfterMass partition mass) fun stage =>
      Core.Finite.Enumeration
        {obstruction : profile.Obstruction stage.previous //
          profile.SupportedByComplement stage.previous
            ((massResult partition mass).read stage) obstruction} :=
  profile.inputs.dependentMap fun stage inputs =>
    inputs.fst.subtype
      (profile.SupportedByComplement stage.previous inputs.snd)
      (profile.supportedDecidable stage.previous inputs.snd)

/-- CT1 primitive semantics on the exact filtered schedule. -/
def spec : CT1.Spec (AfterMass partition mass) where
  Candidate := fun stage =>
    {obstruction : profile.Obstruction stage.previous //
      profile.SupportedByComplement stage.previous
        ((massResult partition mass).read stage) obstruction}
  Realizes := fun stage obstruction =>
    profile.Realizes stage.previous
      ((massResult partition mass).read stage) obstruction.1

/-- CT1 capability derived from the exact filtered query. -/
def capability : CT1.Capability profile.spec where
  schedule := profile.candidates
  realizesDecidable := fun stage obstruction =>
    profile.realizesDecidable stage.previous
      ((massResult partition mass).read stage) obstruction.1
  inputSize := fun stage =>
    CT1.searchCheckBound profile.spec profile.candidates stage
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- Third canonical CT execution before retaining its literal predecessor
identity. -/
private noncomputable def rawExecution :
    CTExecution.{u, 0, u} (AfterMass partition mass) :=
  CTAdapters.ct1 profile.capability

/-- CT1's sealed result together with its literal predecessor identity. -/
structure ExactResult (previous : AfterMass partition mass)
    extends (rawExecution profile).Output previous where
  previous_eq : toExecutionResult.stage.previous = previous

/-- Third canonical CT execution on the exact two-CT extension, retaining that
exact extension in its dependent output type. -/
noncomputable def execution :
    CTExecution.{u, 0, u} (AfterMass partition mass) where
  Terminal := (rawExecution profile).Terminal
  Output := ExactResult profile
  run := fun previous =>
    { toExecutionResult := (rawExecution profile).run previous
      previous_eq := rfl }
  terminal := fun previous result =>
    (rawExecution profile).terminal previous result.toExecutionResult
  checks := (rawExecution profile).checks
  work := (rawExecution profile).work

/-- Exact CT9 → CT14 → CT1 execution. -/
noncomputable def throughAvoidance : CTExecution.{u, 0, u} Previous :=
  (throughMassExecution partition mass).compose profile.execution

end ObstructionProfile

/-! ## CT6: exact ordered local-core scan -/

/-- Inert local-piece interpretation indexed by the exact CT9 → CT14 → CT1
output.

The profile contains primitive local schedules, failure semantics, and
decisions only.  It cannot supply a selected piece, first failure,
no-failure ledger, terminal, or route. -/
structure CoreProfile {Previous : Type u}
    (partition : PartitionProfile Previous)
    (mass : MassProfile partition)
    (obstruction : ObstructionProfile partition mass) where
  LocalPiece : (previous : Previous) →
    (ObstructionProfile.throughAvoidance obstruction).Output previous → Type u
  localPieces : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
      Core.Finite.Enumeration (LocalPiece previous output)
  FailureData : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
    LocalPiece previous output → Type u
  Failure : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
    LocalPiece previous output → Prop
  failureData : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
    (piece : LocalPiece previous output) →
    Failure previous output piece →
      FailureData previous output piece
  failureDecidable : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
    (piece : LocalPiece previous output) →
      Decidable (Failure previous output piece)
  contribution : (previous : Previous) →
    (output :
      (ObstructionProfile.throughAvoidance obstruction).Output previous) →
    LocalPiece previous output → Nat

namespace CoreProfile

variable {partition : PartitionProfile Previous}
variable {mass : MassProfile partition}
variable {obstruction : ObstructionProfile partition mass}
variable (profile : CoreProfile partition mass obstruction)

abbrev AfterAvoidance :=
  Ledger.Extension Previous
    (ObstructionProfile.throughAvoidance obstruction).Output

/-- Exact CT9 → CT14 → CT1 output at the newest ledger entry. -/
def avoidanceResult
    (obstruction : ObstructionProfile partition mass) :
    Query (AfterAvoidance (obstruction := obstruction))
      (fun stage =>
        (ObstructionProfile.throughAvoidance obstruction).Output
          stage.previous) :=
  Query.latest

/-- Canonical local-piece order derived from the literal composed output. -/
def localPieceSchedule :
    Query (AfterAvoidance (obstruction := obstruction)) fun stage =>
      Core.Finite.Enumeration
        (profile.LocalPiece stage.previous
          ((avoidanceResult obstruction).read stage)) :=
  (avoidanceResult obstruction).dependentMap fun stage output =>
    profile.localPieces stage.previous output

/-- CT6 primitive failure semantics over the exact three-CT output. -/
def spec : CT6.Spec (AfterAvoidance (obstruction := obstruction)) where
  Index := fun stage =>
    profile.LocalPiece stage.previous
      ((avoidanceResult obstruction).read stage)
  FailureData := fun stage piece =>
    profile.FailureData stage.previous
      ((avoidanceResult obstruction).read stage) piece
  Failure := fun stage piece =>
    profile.Failure stage.previous
      ((avoidanceResult obstruction).read stage) piece
  failureData := fun stage piece failure =>
    profile.failureData stage.previous
      ((avoidanceResult obstruction).read stage) piece failure
  contribution := fun stage piece =>
    profile.contribution stage.previous
      ((avoidanceResult obstruction).read stage) piece

/-- CT6 capability derived from the exact local-piece schedule. -/
def capability : CT6.Capability profile.spec where
  failureOrder := profile.localPieceSchedule
  failureDecidable := fun stage piece =>
    profile.failureDecidable stage.previous
      ((avoidanceResult obstruction).read stage) piece
  inputSize := fun stage =>
    CT6.localCheckBound (profile.localPieceSchedule.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- Fourth canonical CT execution before retaining its literal predecessor
identity. -/
private noncomputable def rawExecution :
    CTExecution.{u, 0, u} (AfterAvoidance (obstruction := obstruction)) :=
  CTAdapters.ct6 profile.capability

/-- CT6's sealed result together with its literal predecessor identity. -/
structure ExactResult
    (previous : AfterAvoidance (obstruction := obstruction))
    extends (rawExecution profile).Output previous where
  previous_eq : toExecutionResult.stage.previous = previous

/-- Fourth canonical CT execution on the exact three-CT extension, retaining
that exact extension in its dependent output type. -/
noncomputable def execution :
    CTExecution.{u, 0, u} (AfterAvoidance (obstruction := obstruction)) where
  Terminal := (rawExecution profile).Terminal
  Output := ExactResult profile
  run := fun previous =>
    { toExecutionResult := (rawExecution profile).run previous
      previous_eq := rfl }
  terminal := fun previous result =>
    (rawExecution profile).terminal previous result.toExecutionResult
  checks := (rawExecution profile).checks
  work := (rawExecution profile).work

end CoreProfile

/-! ## Complete reusable Strategy -/

/-- Complete inert profile for the four canonical CT phases. -/
structure Profile (Previous : Type u) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  partition : PartitionProfile Previous
  mass : MassProfile partition
  obstruction : ObstructionProfile partition mass
  core : CoreProfile partition mass obstruction

namespace Profile

variable [HasResidual Previous Residual]
variable (profile : Profile Previous Residual)

/-- The prescribed CT9 → CT14 → CT1 → CT6 execution.

No phase is rerun or paired manually: the last composition consumes the
literal output family of the already composed first three phases. -/
noncomputable def execution : CTExecution Previous :=
  profile.obstruction.throughAvoidance.compose profile.core.execution

/-- Literal accumulated-ledger shape after the complete Strategy. -/
abbrev AfterNormalization :=
  Ledger.Extension Previous profile.execution.Output

/-- Exact complete output at the newest ledger entry. -/
def result :
    Query profile.AfterNormalization
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- The literal CT9 result retained inside the composed normalization output.
This is a projection of the newest ledger entry; CT9 is not rerun and no
partition is reconstructed. -/
def partitionResultAfterNormalization :
    Query profile.AfterNormalization
      (fun stage => profile.partition.execution.Output stage.previous) :=
  profile.result.map fun _ output => output.fst.fst.fst

/-- The exact complementary fibre computed by CT9, transported to the
normalization predecessor using the predecessor equality stored by CT9.
Downstream strategies preserve this query instead of rebuilding the
complement from the ambient object and packing. -/
def complementAfterNormalization :
    Query profile.AfterNormalization fun stage =>
      Core.Finite.Enumeration
        (profile.partition.AmbientItem stage.previous) :=
  profile.partitionResultAfterNormalization.dependentMap
    fun stage partitionResult =>
      profile.partition.complementAtPrevious stage.previous partitionResult

/-- Exact first-three-phase output retained by the complete composition. -/
def avoidanceResultAfterNormalization :
    Query profile.AfterNormalization
      (fun stage =>
        profile.obstruction.throughAvoidance.Output stage.previous) :=
  profile.result.map fun _ output => output.fst

/-- The exact component/local-piece schedule consumed by CT6.  The schedule
is projected from the same composed output that CT6 received, so its pieces
remain indexed by the literal CT9--CT14--CT1 predecessor. -/
def localPiecesAfterNormalization :
    Query profile.AfterNormalization fun stage =>
      Core.Finite.Enumeration
        (profile.core.LocalPiece stage.previous
          (profile.avoidanceResultAfterNormalization.read stage)) :=
  profile.result.dependentMap fun stage output =>
    profile.core.localPieces stage.previous output.fst

/-- Exact CT6 output retained by the complete composition. -/
def coreResultAfterNormalization :=
  profile.result.dependentMap fun _ output => output.snd

/-- Any literal CT9 result in the composed output is bounded: each generated
fibre is bounded by that result's exact predecessor-owned ambient schedule,
which is also CT9's capacity for either Boolean label.  No CT is rerun. -/
private theorem partitionBounded
    (result : profile.partition.execution.Output previous) :
    result.terminal = .bounded := by
  exact
    result.terminal_bounded_of_bounded
      (fun label => by
        simpa [PartitionProfile.spec, PartitionProfile.capability,
          PartitionProfile.inputs, CT9.Capability.itemsAt] using
          (CT9.fibreCount_le_itemCount
            (capability := profile.partition.capability)
            (previous := result.stage.previous) label))

/-- The complete literal CT output together with the predecessor equalities
proved by the canonical adapters and `CTExecution.compose`.  These fields are
provenance, not a second result representation. -/
structure ExactOutput (previous : Previous) where
  output : profile.execution.Output previous
  partitionPrevious :
    output.fst.fst.fst.stage.previous = previous
  massPrevious :
    output.fst.fst.snd.stage.previous =
      Ledger.extend previous output.fst.fst.fst
  obstructionPrevious :
    output.fst.snd.stage.previous =
      Ledger.extend previous output.fst.fst
  corePrevious :
    output.snd.stage.previous =
      Ledger.extend previous output.fst

/-- Extract CT6's exact active ledger from a normalized output.  The only
transport is along the predecessor equality already stored by the composed
execution; the active scan is not evaluated again. -/
def ExactOutput.activeLedger
    {previous : Previous} (exact : profile.ExactOutput previous)
    (selected : exact.output.snd.terminal = .activeLedger) :
    CT6.ActiveLedgerResidual profile.core.capability
      (Ledger.extend previous exact.output.fst) := by
  have outcome : CT6.Outcome profile.core.capability
      exact.output.snd.stage.previous .activeLedger := by
    simpa [selected] using exact.output.snd.outcome
  cases outcome with
  | activeLedger ledger =>
      exact exact.corePrevious ▸ ledger

/-- Every component/local piece in a normalized successor is certified
active by the literal CT6 ledger.  This is the preserved structural fact
needed by later component selection; no component schedule is regenerated. -/
theorem ExactOutput.noFailureAt
    {previous : Previous} (exact : profile.ExactOutput previous)
    (selected : exact.output.snd.terminal = .activeLedger)
    (piece : profile.core.LocalPiece previous exact.output.fst)
    (member : piece ∈ (profile.core.localPieces previous exact.output.fst).values) :
    ¬ profile.core.Failure previous exact.output.fst piece := by
  let ledger := ExactOutput.activeLedger (profile := profile) exact selected
  exact ledger.activeAt piece member

/-- CT1's avoidance terminal excludes every complement-supported obstruction
from its exact predecessor-owned schedule. -/
theorem ExactOutput.noObstructionAt
    {previous : Previous} (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .avoiding)
    (obstruction : profile.obstruction.Obstruction previous)
    (scheduled : obstruction ∈
      (profile.obstruction.obstructionSchedule.read previous).values)
    (supported : profile.obstruction.SupportedByComplement previous
      exact.output.fst.fst obstruction)
    (realizes : profile.obstruction.Realizes previous
      exact.output.fst.fst obstruction) : False := by
  let predecessor := Ledger.extend previous exact.output.fst.fst
  have avoidedAtResult :
      ¬ CT1.Target profile.obstruction.spec
        exact.output.fst.snd.stage.previous
        (profile.obstruction.capability.scheduleAt
          exact.output.fst.snd.stage.previous) := by
    simpa [CT1.OutcomeClaim, selected] using
      exact.output.fst.snd.verified
  have avoided :
      ¬ CT1.Target profile.obstruction.spec predecessor
        (profile.obstruction.capability.scheduleAt predecessor) := by
    rw [exact.obstructionPrevious] at avoidedAtResult
    exact avoidedAtResult
  let candidate : profile.obstruction.spec.Candidate predecessor :=
    ⟨obstruction, supported⟩
  apply avoided
  refine ⟨candidate, ?_, realizes⟩
  exact (Core.Finite.Enumeration.mem_subtype_values
    (profile.obstruction.obstructionSchedule.read previous)
    (profile.obstruction.SupportedByComplement previous exact.output.fst.fst)
    (profile.obstruction.supportedDecidable previous exact.output.fst.fst)
    candidate).mpr scheduled

/-- Inert semantic laws consuming only literal terminals of the exact
four-CT output.  They cannot select a terminal, construct an output, or
alter execution.  A domain adapter proves these implications from its
registered target, packing-maximality, density, and core semantics. -/
structure Semantics where
  Target : Previous → Prop
  massAggregateImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      exact.output.fst.fst.fst.terminal = .bounded →
      exact.output.fst.fst.snd.terminal = .aggregate → False
  obstructionHitImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      exact.output.fst.fst.fst.terminal = .bounded →
      exact.output.fst.fst.snd.terminal = .capacity →
      exact.output.fst.snd.terminal = .c1 → False
  coreFailureTarget :
    ∀ previous (exact : profile.ExactOutput previous),
      exact.output.fst.fst.fst.terminal = .bounded →
      exact.output.fst.fst.snd.terminal = .capacity →
      exact.output.fst.snd.terminal = .avoiding →
      exact.output.snd.terminal = .firstFailure →
        Target previous

/-- Exhaustive target-or-normalized successor of the exact composition.
Every surviving constructor retains the complete literal output and the
terminal equalities derived from it. -/
inductive RoutedResidual (semantics : profile.Semantics)
    (previous : Previous) where
  | target
      (exact : profile.ExactOutput previous)
      (proof : semantics.Target previous)
  | normalized
      (exact : profile.ExactOutput previous)
      (partitionSelected : exact.output.fst.fst.fst.terminal = .bounded)
      (massSelected : exact.output.fst.fst.snd.terminal = .capacity)
      (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
      (selected : exact.output.snd.terminal = .activeLedger)

/-- Interpret the complete literal output once and retain every possible CT
terminal as one typed successor. -/
noncomputable def route (semantics : profile.Semantics)
    (previous : Previous) :
    profile.RoutedResidual semantics previous :=
  let output := profile.execution.run previous
  let exact : profile.ExactOutput previous :=
    ⟨output, rfl, rfl, rfl, rfl⟩
  have partitionTerminal :
      output.fst.fst.fst.terminal = .bounded :=
    profile.partitionBounded output.fst.fst.fst
  match massTerminal : output.fst.fst.snd.terminal with
  | .unboundedMember =>
      (profile.mass.noUnbounded output.fst.fst.snd massTerminal).elim
  | .missingLabel =>
      (profile.mass.noMissingLabel output.fst.fst.snd massTerminal).elim
  | .aggregate =>
      (semantics.massAggregateImpossible previous exact
        partitionTerminal massTerminal).elim
  | .capacity =>
      match obstructionTerminal : output.fst.snd.terminal with
      | .c1 =>
          (semantics.obstructionHitImpossible previous exact
            partitionTerminal massTerminal obstructionTerminal).elim
      | .avoiding =>
          match coreTerminal : output.snd.terminal with
          | .firstFailure =>
              .target exact
                (semantics.coreFailureTarget previous exact
                  partitionTerminal massTerminal obstructionTerminal
                  coreTerminal)
          | .activeLedger =>
              .normalized exact partitionTerminal massTerminal
                obstructionTerminal coreTerminal

/-- Standard completed Strategy boundary over the exhaustive typed result.
Core appends this one payload; the proof application supplies no terminal
interpreter. -/
noncomputable def contract (semantics : profile.Semantics) :
    Core.Strategy.Contract Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Payload := fun previous _ => profile.RoutedResidual semantics previous
  produce := fun previous =>
    ⟨.completed, profile.route semantics previous⟩
  exhaustive := fun previous =>
    ⟨⟨.completed, profile.route semantics previous⟩⟩


/-- Exact numeric ledger published by one completed normalization.  Every
field is a CT-generated total read off the literal retained output through the
provenance record; nothing is recomputed or copied. -/
def summaryOfExact {previous : Previous}
    (exact : profile.ExactOutput previous) : Summary :=
  { ambientCount :=
      (profile.partition.capability.itemsAt
        exact.output.fst.fst.fst.stage.previous).card
    selectedCount :=
      CT9.fibreCount profile.partition.capability
        exact.output.fst.fst.fst.stage.previous true
    complementCount :=
      CT9.fibreCount profile.partition.capability
        exact.output.fst.fst.fst.stage.previous false
    lowerMass :=
      CT14.lowerMass profile.mass.capability
        exact.output.fst.fst.snd.stage.previous
    activeTotal :=
      CT6.activeTotal profile.core.capability
        exact.output.snd.stage.previous }

/-- The residual-to-ambient link, read off the two totals this entry already
publishes: the normalized complement never has more members than the ambient
item schedule it was cut out of.

This is the fact `def:remainder-entropy` needs in order to compare `|R|` with
`n` -- the entropy account divides `log2|G(R)|` by `|R|` and measures the
skeleton budget in powers of `n`, so a consumer that reads both numbers from
this one entry gets them already ordered instead of having to equate two
independently reconstructed carriers.  Both sides are CT9's own counts; the
proof is that a fibre is a filtered sub-schedule of the item schedule. -/
theorem summaryOfExact_complementCount_le_ambientCount {previous : Previous}
    (exact : profile.ExactOutput previous) :
    (profile.summaryOfExact exact).complementCount <=
      (profile.summaryOfExact exact).ambientCount :=
  CT9.fibreCount_le_itemsAt_card _ _ _

/-- **CT9's partition, on the two counts this entry publishes.**

The selected and complementary fibres exhaust the ambient item schedule with no
loss and no duplication, so `|W| + |R| = n`.  This is `CT9`'s own
no-overcounting identity (`CT9.cardinality_eq_sum_fibreCount`) at the two-label
membership schedule this profile searches, read on the published totals.

It is the manuscript's `|R| = n - |W|`; combined with a presentation whose
selected part is `p` vertex-disjoint windows of order `windowOrder` it is
`|R| = n - windowOrder · p`, the Erdős–Gyárfás `|R| = n - 13 p₁₃`.  Nothing is
recomputed: both fibre counts and the item count are CT9's own totals. -/
theorem summaryOfExact_selectedCount_add_complementCount_eq_ambientCount
    {previous : Previous} (exact : profile.ExactOutput previous) :
    (profile.summaryOfExact exact).selectedCount +
        (profile.summaryOfExact exact).complementCount =
      (profile.summaryOfExact exact).ambientCount := by
  have partition := CT9.cardinality_eq_sum_fibreCount
    (capability := profile.partition.capability)
    (previous := exact.output.fst.fst.fst.stage.previous)
  have labels :
      (profile.partition.capability.labelScheduleAt
        exact.output.fst.fst.fst.stage.previous).values = [false, true] := rfl
  rw [labels] at partition
  have split :
      (profile.partition.capability.itemsAt
        exact.output.fst.fst.fst.stage.previous).card =
        CT9.fibreCount profile.partition.capability
            exact.output.fst.fst.fst.stage.previous false +
          CT9.fibreCount profile.partition.capability
            exact.output.fst.fst.fst.stage.previous true := by
    rw [partition]; rfl
  show CT9.fibreCount profile.partition.capability
        exact.output.fst.fst.fst.stage.previous true +
      CT9.fibreCount profile.partition.capability
        exact.output.fst.fst.fst.stage.previous false =
    (profile.partition.capability.itemsAt
      exact.output.fst.fst.fst.stage.previous).card
  omega

/-- The exact numeric ledger of whichever exhaustive successor Core routed to.
Both constructors retain the same complete literal output. -/
def summaryOfRouted {semantics : profile.Semantics} {previous : Previous} :
    profile.RoutedResidual semantics previous → Summary
  | .target exact _ => profile.summaryOfExact exact
  | .normalized exact _ _ _ _ => profile.summaryOfExact exact

/-- The same link on the routed successor's published ledger, so a consumer
that only ever sees `summaryOfRouted` reads it without unfolding the route. -/
theorem summaryOfRouted_complementCount_le_ambientCount
    {semantics : profile.Semantics} {previous : Previous} :
    ∀ routed : profile.RoutedResidual semantics previous,
      (profile.summaryOfRouted routed).complementCount <=
        (profile.summaryOfRouted routed).ambientCount
  | .target exact _ => profile.summaryOfExact_complementCount_le_ambientCount exact
  | .normalized exact _ _ _ _ =>
      profile.summaryOfExact_complementCount_le_ambientCount exact

/-- CT9's partition on the routed successor's published ledger, so a consumer
that only ever sees `summaryOfRouted` reads `|W| + |R| = n` without unfolding
the route. -/
theorem summaryOfRouted_selectedCount_add_complementCount_eq_ambientCount
    {semantics : profile.Semantics} {previous : Previous} :
    ∀ routed : profile.RoutedResidual semantics previous,
      (profile.summaryOfRouted routed).selectedCount +
          (profile.summaryOfRouted routed).complementCount =
        (profile.summaryOfRouted routed).ambientCount
  | .target exact _ =>
      profile.summaryOfExact_selectedCount_add_complementCount_eq_ambientCount
        exact
  | .normalized exact _ _ _ _ =>
      profile.summaryOfExact_selectedCount_add_complementCount_eq_ambientCount
        exact

end Profile

/-! ## Registration-driven construction

The compiler builds the complete dependent profile from one inert
residual-indexed registration.  Every inherited value is a `Query` on the
literal predecessor; the registration supplies no stage, ledger, or CT
value. -/

/-- Build the dependent CT9 → CT14 → CT1 → CT6 profile from one inert
registration.  All four phase profiles read the stable residual through
`Query.residual`. -/
noncomputable def Profile.ofRegistrationAt
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    {packingSemantics :
      ObstructionPackingClosure.Semantics.{uResidual, u} Residual Target}
    (registration :
      Registration.{uResidual, u, u, u, u}
        Residual Target packingSemantics)
    (current : Query Previous fun _ => Residual)
    (packingQuery : Query Previous fun previous =>
      ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current.read previous))
        (packingSemantics.conflict (current.read previous))) :
    Profile.{u, uResidual} Previous Residual :=
  let residual := current
  let selected : (previous : Previous) →
      List (packingSemantics.Occurrence (current.read previous)) :=
    fun previous => (packingQuery.read previous).selected
  let covers : (residual : Residual) →
      List (packingSemantics.Occurrence residual) →
        registration.AmbientItem residual → Prop :=
    fun residual selected item =>
      ∃ occurrence ∈ selected, item ∈ registration.cover residual occurrence
  let coveredItems : (previous : Previous) →
      List (registration.AmbientItem (current.read previous)) :=
    fun previous =>
      (selected previous).flatMap
        (registration.cover (current.read previous))
  let partition : PartitionProfile Previous :=
    { AmbientItem := fun previous =>
        registration.AmbientItem (current.read previous)
      ambientSupport := residual.dependentMap fun _ residual =>
        registration.ambientSupport residual
      SelectedPacking := fun previous =>
        List (packingSemantics.Occurrence (current.read previous))
      selectedPacking := Query.ofFunction selected
      Selected := fun previous => covers (current.read previous)
      selectedDecidable := fun _ _ _ => Classical.dec _ }
  let mass : MassProfile partition :=
    { DensityCap := fun _ => PUnit
      densityCap := residual.dependentMap fun _ _ => PUnit.unit
      -- The unselected fibre misses at most the covered items.
      lowerMass := fun previous _ _ =>
        (registration.ambientSupport (current.read previous)).card -
          (coveredItems previous).length }
  let obstruction : ObstructionProfile partition mass :=
    { Obstruction := fun previous =>
        packingSemantics.Occurrence (current.read previous)
      obstructionSchedule := residual.dependentMap fun _ residual =>
        packingSemantics.occurrences residual
      SupportedByComplement := fun previous output obstruction =>
        ∀ item ∈ registration.cover (current.read previous) obstruction,
          item ∈
            (partition.complementAtPrevious previous output.fst).values
      supportedDecidable := fun _ _ _ => Classical.dec _
      Realizes := fun previous _ obstruction =>
        obstruction ∈
          (packingSemantics.occurrences (current.read previous)).values
      realizesDecidable := fun _ _ _ => Classical.dec _ }
  { partition
    mass
    obstruction
    core :=
      { LocalPiece := fun previous output =>
          registration.LocalPiece (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst)
        localPieces := fun previous output =>
          registration.localPieces (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst)
        FailureData := fun previous output piece =>
          registration.FailureData (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst) piece
        Failure := fun previous output piece =>
          registration.Failure (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst) piece
        failureData := fun previous output piece failure =>
          registration.failureData (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst)
            piece failure
        failureDecidable := fun previous output piece =>
          registration.failureDecidable (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst) piece
        contribution := fun previous output piece =>
          registration.contribution (current.read previous)
            (partition.complementAtPrevious previous output.fst.fst) piece } }

/-- Stable-residual specialization of the query-native constructor. -/
noncomputable def Profile.ofRegistration
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    {packingSemantics :
      ObstructionPackingClosure.Semantics.{uResidual, u} Residual Target}
    (registration :
      Registration.{uResidual, u, u, u, u}
        Residual Target packingSemantics)
    (packingQuery : Query Previous fun previous =>
      ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (residualOf previous))
        (packingSemantics.conflict (residualOf previous))) :
    Profile.{u, uResidual} Previous Residual :=
  Profile.ofRegistrationAt registration Query.residual packingQuery

namespace Profile

variable [HasResidual Previous Residual]

/-- Framework-derived mass law.  The unselected fibre of the ambient support
misses at most the items the selected family covers, so the derived density
cap never exceeds it.  Domain data contributes nothing here. -/
private theorem coveredComplement_length
    {Item : Type uItem} {Occ : Type uPacking}
    (ambient : Core.Finite.Enumeration Item)
    (selected : List Occ) (cover : Occ → List Item)
    (complement : List Item)
    (characterization : ∀ item, item ∈ complement ↔
      item ∈ ambient.values ∧
        ¬ ∃ occurrence ∈ selected, item ∈ cover occurrence) :
    ambient.card - (selected.flatMap cover).length ≤ complement.length := by
  have subset :
      ambient.values ⊆ complement ++ selected.flatMap cover := by
    intro item mem
    by_cases covered : ∃ occurrence ∈ selected, item ∈ cover occurrence
    · obtain ⟨occurrence, occurrenceMem, itemMem⟩ := covered
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨occurrence, occurrenceMem, itemMem⟩)
    · exact List.mem_append_left _
        ((characterization item).mpr ⟨mem, covered⟩)
  have le := (List.subperm_of_subset ambient.nodup subset).length_le
  simp only [List.length_append] at le
  simp only [Core.Finite.Enumeration.card_eq_length]
  omega

/-- Framework-derived maximality law.  An occurrence whose covered items are
all unselected conflicts with nothing in Core's canonical maximal packing, so
maximality forces it to be selected -- and then it covers one of its own
items, which is a contradiction.  Domain data contributes only `cover_ne`. -/
private theorem packing_no_free_occurrence
    {Occ : Type uPacking} {Item : Type uItem}
    (schedule : Core.Finite.Enumeration Occ)
    (conflict : Occ → Occ → Prop)
    (packing : ObstructionPackingClosure.Packing schedule conflict)
    (cover : Occ → List Item)
    (conflict_iff : ∀ left right, conflict left right ↔
      ∃ item, item ∈ cover left ∧ item ∈ cover right)
    (cover_ne : ∀ occurrence, cover occurrence ≠ [])
    (occurrence : Occ)
    (supported : ∀ item ∈ cover occurrence,
      ¬ ∃ selected ∈ packing.selected, item ∈ cover selected)
    (realized : occurrence ∈ schedule.values) : False := by
  obtain ⟨selected, selectedMem, conflictOrEq⟩ :=
    packing.maximal occurrence realized
  rcases conflictOrEq with related | rfl
  · obtain ⟨item, inOccurrence, inSelected⟩ :=
      (conflict_iff occurrence selected).mp related
    exact supported item inOccurrence ⟨selected, selectedMem, inSelected⟩
  · obtain ⟨item, inOccurrence⟩ :=
      List.exists_mem_of_ne_nil _ (cover_ne occurrence)
    exact supported item inOccurrence
      ⟨occurrence, selectedMem, inOccurrence⟩

/-- The registered laws discharge every non-normalized terminal of the exact
four-CT composition, and the registered target implication supplies the sole
target-producing branch.  The stage identities used here are the provenance
equalities Core already retains in `ExactOutput`. -/
noncomputable def semanticsOfRegistrationAt
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    {packingSemantics :
      ObstructionPackingClosure.Semantics.{uResidual, u} Residual Target}
    (registration :
      Registration.{uResidual, u, u, u, u}
        Residual Target packingSemantics)
    (current : Query Previous fun _ => Residual)
    (packingQuery : Query Previous fun previous =>
      ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current.read previous))
        (packingSemantics.conflict (current.read previous))) :
    (Profile.ofRegistrationAt (Previous := Previous)
      registration current packingQuery).Semantics where
  Target := fun previous => Target (current.read previous)
  massAggregateImpossible := by
    intro previous exact _partitionTerminal massTerminal
    have outcome := exact.output.fst.fst.snd.outcome
    rw [massTerminal] at outcome
    cases outcome with
    | aggregate ledger certificate =>
        have strict : ledger.capacity.total < ledger.lower.total := certificate
        rw [ledger.capacity.total_exact, ledger.lower.total_exact] at strict
        refine absurd strict (Nat.not_lt.mpr ?_)
        rw [MassProfile.lowerMass_eq, MassProfile.upperCapacity_eq,
          PartitionProfile.complementFibre_card,
          PartitionProfile.result_read, exact.massPrevious]
        simp only [Ledger.extend]
        rw [exact.partitionPrevious]
        refine coveredComplement_length
          (registration.ambientSupport (current.read previous)) _
          (registration.cover (current.read previous))
          (CT9.fibre
            (ofRegistrationAt registration current packingQuery).partition.capability
            previous false) ?_
        intro item
        simp only [CT9.fibre, CT9.Capability.itemsAt,
          PartitionProfile.capability, PartitionProfile.spec,
          PartitionProfile.inputs, Profile.ofRegistrationAt, List.mem_filter,
          Query.read_residual, Query.read_dependentMap, Query.read_and,
          Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          not_exists, not_and]
        tauto
  obstructionHitImpossible := by
    intro previous exact _partitionTerminal _massTerminal obstructionTerminal
    cases branch : exact.output.fst.snd.stage.added.added with
    | noBranch _ =>
        have avoiding : exact.output.fst.snd.terminal = .avoiding := by
          simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
        rw [avoiding] at obstructionTerminal
        exact CT1.Terminal.noConfusion obstructionTerminal
    | yesBranch hasHit =>
        let hit :=
          Core.Finite.Search.Execution.hitOfHasHit
            exact.output.fst.snd.stage.added.previous hasHit
        have supported :
            ∀ item ∈
                registration.cover
                  (current.read exact.output.fst.snd.stage.previous.previous)
                  hit.value.1,
              ¬ ∃ selected ∈
                  (packingQuery.read
                    exact.output.fst.snd.stage.previous.previous).selected,
                item ∈ registration.cover
                  (current.read exact.output.fst.snd.stage.previous.previous)
                  selected := by
          intro item itemMem
          exact
            ((PartitionProfile.mem_complementAtPrevious_iff
              (Profile.ofRegistrationAt registration current packingQuery).partition
              exact.output.fst.snd.stage.previous.previous
              exact.output.fst.snd.stage.previous.added.fst item).mp
                (hit.value.2 item itemMem)).2
        exact packing_no_free_occurrence
          (packingSemantics.occurrences
            (current.read exact.output.fst.snd.stage.previous.previous))
          (packingSemantics.conflict
            (current.read exact.output.fst.snd.stage.previous.previous))
          (packingQuery.read exact.output.fst.snd.stage.previous.previous)
          (registration.cover
            (current.read exact.output.fst.snd.stage.previous.previous))
          (registration.conflict_iff_shared_item
            (current.read exact.output.fst.snd.stage.previous.previous))
          (registration.cover_ne
            (current.read exact.output.fst.snd.stage.previous.previous))
          hit.value.1 supported hit.sound
  coreFailureTarget := by
    intro previous exact _partitionTerminal _massTerminal obstructionTerminal
      coreTerminal
    cases branch : exact.output.fst.snd.stage.added.added with
    | yesBranch _ =>
        have selected : exact.output.fst.snd.terminal = .c1 := by
          simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
        rw [selected] at obstructionTerminal
        exact CT1.Terminal.noConfusion obstructionTerminal
    | noBranch avoiding =>
        have outcome := exact.output.snd.outcome
        rw [coreTerminal] at outcome
        cases outcome with
        | firstFailure failure =>
            rw [exact.corePrevious] at failure
            refine registration.failureForcesTarget
              (current.read previous)
              (PartitionProfile.complementAtPrevious
                (Profile.ofRegistrationAt registration current packingQuery).partition
                previous exact.output.fst.fst.fst)
              failure.hit.value failure.hit.holds ?_
            intro occurrence supported realized
            let candidate :
                {obstruction :
                    packingSemantics.Occurrence (current.read previous) //
                  ∀ item ∈ registration.cover (current.read previous) obstruction,
                    item ∈
                      (PartitionProfile.complementAtPrevious
                        (Profile.ofRegistrationAt registration current packingQuery).partition
                        previous exact.output.fst.fst.fst).values} :=
              ⟨occurrence, supported⟩
            have candidateMem :
                candidate ∈
                  (ObstructionProfile.candidates
                    (Profile.ofRegistrationAt registration current packingQuery).obstruction
                    |>.read
                      (Ledger.extend previous exact.output.fst.fst)).values := by
              change candidate ∈
                ((packingSemantics.occurrences (current.read previous)).subtype
                  _ _).values
              exact
                (Core.Finite.Enumeration.mem_subtype_values
                  (packingSemantics.occurrences (current.read previous))
                  _ _ candidate).mpr realized
            obtain ⟨index, indexValue⟩ :=
              (Core.Finite.Enumeration.mem_iff_exists_index
                (ObstructionProfile.candidates
                  (Profile.ofRegistrationAt registration current packingQuery).obstruction
                  |>.read (Ledger.extend previous exact.output.fst.fst))
                candidate).mp candidateMem
            rw [exact.obstructionPrevious] at avoiding
            exact (avoiding index) (by
              change
                ((ObstructionProfile.candidates
                    (Profile.ofRegistrationAt registration current packingQuery).obstruction
                    |>.read (Ledger.extend previous exact.output.fst.fst)).get
                    index).1 ∈
                  (packingSemantics.occurrences
                    (current.read previous)).values
              rw [indexValue]
              exact realized)

/-- Stable-residual specialization of `semanticsOfRegistrationAt`. -/
noncomputable def semanticsOfRegistration
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    {packingSemantics :
      ObstructionPackingClosure.Semantics.{uResidual, u} Residual Target}
    (registration :
      Registration.{uResidual, u, u, u, u}
        Residual Target packingSemantics)
    (packingQuery : Query Previous fun previous =>
      ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (residualOf previous))
        (packingSemantics.conflict (residualOf previous))) :
    (Profile.ofRegistration (Previous := Previous)
      registration packingQuery).Semantics :=
  semanticsOfRegistrationAt registration Query.residual packingQuery

end Profile

end Hypostructure.Core.Strategy.SupportComplementNormalization
