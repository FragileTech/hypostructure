import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.BoundaryDemandAccountingSemantics

/-!
# Boundary-demand accounting

This domain-neutral Strategy is exactly CT4 followed by CT14.  CT4 assigns
the demand schedule derived from an exact predecessor-ledger query to the
first eligible payer.  CT14 then aggregates members derived from CT4's
literal output together with that same preserved predecessor query.

Core's `CTExecution.compose` owns both execution and the intermediate ledger
extension.  This module neither reconstructs an inherited fact nor writes to
the ledger directly.
-/

namespace Hypostructure.Core.Strategy.BoundaryDemandAccounting

open Hypostructure
open Hypostructure.Core.Residual

universe u uResidual uSupport uDemand uPayer uMember uLabel

/-- Inert domain semantics for CT4 over one exact normalized-support query.

The profile contains primitive schedules, eligibility, weights, and
capacities only.  In particular, it contains no assignment, terminal,
execution result, route, or required-total certificate. -/
structure AssignmentProfile (Previous : Type u) where
  NormalizedSupport : Previous → Type uSupport
  normalizedSupport : Query Previous NormalizedSupport
  Demand :
    (previous : Previous) → NormalizedSupport previous → Type uDemand
  Payer :
    (previous : Previous) → NormalizedSupport previous → Type uPayer
  demands :
    (previous : Previous) → (support : NormalizedSupport previous) →
      Core.Finite.Enumeration (Demand previous support)
  payers :
    (previous : Previous) → (support : NormalizedSupport previous) →
      Core.Finite.Enumeration (Payer previous support)
  Eligible :
    (previous : Previous) → (support : NormalizedSupport previous) →
      Demand previous support → Payer previous support → Prop
  eligibleDecidable :
    (previous : Previous) → (support : NormalizedSupport previous) →
      (demand : Demand previous support) →
      (payer : Payer previous support) →
        Decidable (Eligible previous support demand payer)
  demandWeight :
    (previous : Previous) → (support : NormalizedSupport previous) →
      Demand previous support → Nat
  payerCapacity :
    (previous : Previous) → (support : NormalizedSupport previous) →
      Payer previous support → Nat
  /-- The exact normalization ledger carried by the dependent support value
  this node reads.  It is a projection, not a second observation: the very
  value `memberCapacity` already multiplies its registered rate by.  Node
  `[29]`'s window/remainder coordinates `n`, `|W|`, `|R|` are its three
  counts. -/
  normalizationSummary :
    (previous : Previous) → NormalizedSupport previous →
      SupportComplementNormalization.Summary

namespace AssignmentProfile

variable (profile :
  AssignmentProfile.{u, uSupport, uDemand, uPayer} Previous)

/-- Exact demand schedule projected from the predecessor-owned support. -/
def demandQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Demand previous
          (profile.normalizedSupport.read previous)) :=
  profile.normalizedSupport.dependentMap fun previous support =>
    profile.demands previous support

/-- Exact payer schedule projected from the same predecessor-owned support. -/
def payerQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Payer previous
          (profile.normalizedSupport.read previous)) :=
  profile.normalizedSupport.dependentMap fun previous support =>
    profile.payers previous support

/-- One typed read retaining both CT4 schedules at the identical stage. -/
def assignmentInputs :=
  profile.demandQuery.and profile.payerQuery

/-- CT4's demand schedule, projected from the exact combined query. -/
def assignmentDemands :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Demand previous
          (profile.normalizedSupport.read previous)) :=
  profile.assignmentInputs.map fun _ inputs => inputs.fst

/-- CT4's payer schedule, projected dependently from the exact combined
query. -/
def assignmentPayers :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Payer previous
          (profile.normalizedSupport.read previous)) :=
  profile.assignmentInputs.dependentMap fun _ inputs => inputs.snd

/-- CT4 semantics on the literal predecessor.

The required total is definitionally the sum of the exact demand weights; it
is not accepted as registration data. -/
def assignmentSpec : CT4.Spec Previous where
  Demand := fun previous =>
    profile.Demand previous
      (profile.normalizedSupport.read previous)
  Payer := fun previous =>
    profile.Payer previous
      (profile.normalizedSupport.read previous)
  Eligible := fun previous =>
    profile.Eligible previous
      (profile.normalizedSupport.read previous)
  demandWeight := fun previous =>
    profile.demandWeight previous
      (profile.normalizedSupport.read previous)
  capacity := fun previous =>
    profile.payerCapacity previous
      (profile.normalizedSupport.read previous)
  required := fun previous =>
    ((profile.assignmentDemands.read previous).values.map
      (profile.demandWeight previous
        (profile.normalizedSupport.read previous))).sum

/-- CT4 capability derived from the two exact queried schedules. -/
def assignmentCapability : CT4.Capability profile.assignmentSpec where
  demands := profile.assignmentDemands
  payers := profile.assignmentPayers
  eligibleDecidable := fun previous =>
    profile.eligibleDecidable previous
      (profile.normalizedSupport.read previous)
  inputSize := fun previous =>
    CT4.localCheckBound
      (profile.assignmentDemands.read previous)
      (profile.assignmentPayers.read previous)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The first canonical CT execution. -/
noncomputable def assignmentExecution : CTExecution Previous :=
  CTAdapters.ct4 profile.assignmentCapability

/-- Literal accumulated-ledger shape after CT4. -/
abbrev AfterAssignment :=
  Ledger.Extension Previous profile.assignmentExecution.Output

/-- Exact CT4 result at the newest ledger entry. -/
def assignmentResult :
    Query profile.AfterAssignment
      (fun stage => profile.assignmentExecution.Output stage.previous) :=
  Query.latest

/-- Preserve the inherited normalized-support query through CT4. -/
def normalizedSupportAfterAssignment :
    Query profile.AfterAssignment
      (fun stage => profile.NormalizedSupport stage.previous) :=
  profile.normalizedSupport.preserve

/-- The sole input to CT14's domain projection: CT4's exact result paired
with the exact inherited normalized support. -/
def assignmentAndSupport :=
  profile.assignmentResult.and profile.normalizedSupportAfterAssignment

/-- Exact assignment table retained by CT4 on every one of its four
terminals.  The table is read out of the literal execution result; the
first-eligible scan is not repeated. -/
def assignmentStateOf
    (result : CT4.ExecutionResult profile.assignmentSpec
      profile.assignmentCapability) :
    CT4.AssignmentState profile.assignmentCapability result.stage.previous :=
  match result.terminal, result.outcome with
  | .missingPayer, .missingPayer assignment _ => assignment
  | .overloadedFibre, .overloadedFibre total _ => total.assignment
  | .c4, .c4 total _ _ => total.assignment
  | .capacity, .capacity total _ _ => total.assignment

/-- Exact numeric ledger published by one completed boundary accounting.
Every field is CT4's own generated quantity at the literal result stage. -/
def summaryOfResult
    (result : CT4.ExecutionResult profile.assignmentSpec
      profile.assignmentCapability) : Summary :=
  { demandCount :=
      (profile.assignmentCapability.demandsAt result.stage.previous).card
    payerCount :=
      (profile.assignmentCapability.payersAt result.stage.previous).card
    requiredTotal := profile.assignmentSpec.required result.stage.previous
    assignedTotal :=
      ((profile.assignmentCapability.payersAt
          result.stage.previous).values.map fun payer =>
        CT4.fibreWeight (profile.assignmentStateOf result) payer).sum
    capacityTotal :=
      CT4.totalCapacity profile.assignmentCapability result.stage.previous
    ambientCount :=
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport.read result.stage.previous)).ambientCount
    selectedCount :=
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport.read result.stage.previous)).selectedCount
    complementCount :=
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport.read result.stage.previous)).complementCount }

/-- **CT9's partition, transported across the accounting boundary.**

The three node-`[29]` counts are the normalization ledger's own, copied
verbatim, so `|W| + |R| = n` moves onto the accounting entry by definitional
transport alone.  The premise is exactly
`SupportComplementNormalization.Profile.summaryOfRouted_selectedCount_add_complementCount_eq_ambientCount`
read at the same predecessor; nothing is recomputed and no count is
re-derived. -/
theorem summaryOfResult_selectedCount_add_complementCount_eq_ambientCount
    (result : CT4.ExecutionResult profile.assignmentSpec
      profile.assignmentCapability)
    (partition :
      (profile.normalizationSummary result.stage.previous
          (profile.normalizedSupport.read
            result.stage.previous)).selectedCount +
        (profile.normalizationSummary result.stage.previous
          (profile.normalizedSupport.read
            result.stage.previous)).complementCount =
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport.read result.stage.previous)).ambientCount) :
    (profile.summaryOfResult result).selectedCount +
        (profile.summaryOfResult result).complementCount =
      (profile.summaryOfResult result).ambientCount := partition

end AssignmentProfile

/-- Inert aggregate interpretation of CT4's literal result.

Every member, mass, capacity, and label is indexed by both the exact CT4
output and the exact normalized-support value.  Capacities and labels are
total primitive observations, so this profile cannot inject CT14's selected
comparison terminal. -/
structure AggregateProfile {Previous : Type u}
    (assignment :
      AssignmentProfile.{u, uSupport, uDemand, uPayer} Previous) where
  Member :
    (previous : Previous) →
      assignment.assignmentExecution.Output previous →
      assignment.NormalizedSupport previous → Type uMember
  Label :
    (previous : Previous) →
      assignment.assignmentExecution.Output previous →
      assignment.NormalizedSupport previous → Type uLabel
  members :
    (previous : Previous) →
      (result : assignment.assignmentExecution.Output previous) →
      (support : assignment.NormalizedSupport previous) →
        Core.Finite.Enumeration (Member previous result support)
  memberLowerMass :
    (previous : Previous) →
      (result : assignment.assignmentExecution.Output previous) →
      (support : assignment.NormalizedSupport previous) →
        Member previous result support → Nat
  memberCapacity :
    (previous : Previous) →
      (result : assignment.assignmentExecution.Output previous) →
      (support : assignment.NormalizedSupport previous) →
        Member previous result support → Nat
  memberLabel :
    (previous : Previous) →
      (result : assignment.assignmentExecution.Output previous) →
      (support : assignment.NormalizedSupport previous) →
        Member previous result support → Label previous result support
  labelDecidableEq :
    (previous : Previous) →
      (result : assignment.assignmentExecution.Output previous) →
      (support : assignment.NormalizedSupport previous) →
        DecidableEq (Label previous result support)

/-- Complete inert semantics for the reusable CT4 → CT14 Strategy. -/
structure Profile (Previous : Type u) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  assignment : AssignmentProfile.{u, uSupport, uDemand, uPayer} Previous
  aggregate :
    AggregateProfile.{u, uSupport, uDemand, uPayer, uMember, uLabel}
      assignment

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{u, uResidual, uSupport, uDemand, uPayer, uMember, uLabel}
    Previous Residual)

abbrev AfterAssignment := profile.assignment.AfterAssignment

/-- CT14's exact member schedule, projected only from CT4's newest result and
the preserved normalized-support query. -/
def aggregateMembers :
    Query profile.AfterAssignment fun stage =>
      let inputs := profile.assignment.assignmentAndSupport.read stage
      Core.Finite.Enumeration
        (profile.aggregate.Member stage.previous inputs.fst inputs.snd) :=
  profile.assignment.assignmentAndSupport.dependentMap
    fun stage inputs =>
      profile.aggregate.members stage.previous inputs.fst inputs.snd

/-- CT14 semantics over the exact paired predecessor views. -/
def aggregateSpec : CT14.Spec profile.AfterAssignment where
  Member := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    profile.aggregate.Member stage.previous inputs.fst inputs.snd
  Label := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    profile.aggregate.Label stage.previous inputs.fst inputs.snd
  memberLowerMass := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    profile.aggregate.memberLowerMass
      stage.previous inputs.fst inputs.snd member
  memberCapacity := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    some (profile.aggregate.memberCapacity
      stage.previous inputs.fst inputs.snd member)
  memberLabel := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    some (profile.aggregate.memberLabel
      stage.previous inputs.fst inputs.snd member)

/-- CT14 capability derived from the exact generated accounting schedule. -/
def aggregateCapability : CT14.Capability profile.aggregateSpec where
  members := profile.aggregateMembers
  labelDecidableEq := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport.read stage
    profile.aggregate.labelDecidableEq
      stage.previous inputs.fst inputs.snd
  inputSize := fun stage =>
    CT14.localCheckBound (profile.aggregateMembers.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The second canonical CT execution on CT4's literal extension. -/
noncomputable def aggregateExecution :
    CTExecution profile.AfterAssignment :=
  CTAdapters.ct14 profile.aggregateCapability

/-- The prescribed CT4 → CT14 execution.  `compose` owns the intermediate
extension and retains both literal CT results in its output. -/
noncomputable def execution : CTExecution Previous :=
  profile.assignment.assignmentExecution.compose
    profile.aggregateExecution

/-- Literal ledger shape after the complete Strategy. -/
abbrev AfterAccounting :=
  Ledger.Extension Previous profile.execution.Output

/-- Exact complete CT4 → CT14 result at the newest ledger entry. -/
def result :
    Query profile.AfterAccounting
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- Exact CT4 component retained by the composed output. -/
def assignmentResultAfterAccounting :
    Query profile.AfterAccounting
      (fun stage =>
        profile.assignment.assignmentExecution.Output stage.previous) :=
  profile.result.map fun _ output => output.fst

/-- Exact CT14 component retained by the composed output. -/
def aggregateResultAfterAccounting :=
  profile.result.dependentMap fun _ output => output.snd

private theorem noUnbounded
    (result : profile.aggregateExecution.Output previous)
    (selected : result.terminal = .unboundedMember) : False := by
  have outcome :
      CT14.Outcome profile.aggregateCapability result.stage.previous
        .unboundedMember := by
    simpa [selected] using result.outcome
  cases outcome with
  | unboundedMember _ residual =>
      have impossible := residual.holds
      simp [aggregateSpec] at impossible

private theorem noMissingLabel
    (result : profile.aggregateExecution.Output previous)
    (selected : result.terminal = .missingLabel) : False := by
  have outcome :
      CT14.Outcome profile.aggregateCapability result.stage.previous
        .missingLabel := by
    simpa [selected] using result.outcome
  cases outcome with
  | missingLabel _ _ residual =>
      have impossible := residual.holds
      simp [aggregateSpec] at impossible

/-- Literal CT4 → CT14 output with the predecessor identities supplied by
the two canonical adapters and dependent composition. -/
structure ExactOutput (previous : Previous) where
  output : profile.execution.Output previous
  assignmentPrevious : output.fst.stage.previous = previous
  aggregatePrevious :
    output.snd.stage.previous.previous = previous
  aggregateAdded :
    output.snd.stage.previous.added = output.fst

/-- The literal CT4 assignment table transported back to the accounting
predecessor.  This projects the table retained by CT4; it does not repeat the
first-eligible search. -/
def ExactOutput.assignmentState
    {previous : Previous} (exact : profile.ExactOutput previous) :
    CT4.AssignmentState profile.assignment.assignmentCapability previous :=
  exact.assignmentPrevious ▸
    profile.assignment.assignmentStateOf exact.output.fst

/-- Exhaustive terminal-indexed successor of the exact CT4 → CT14
composition.  The complete literal output is retained in every constructor;
no exceptional terminal is erased or treated as a target in generic Core. -/
inductive RoutedResidual (previous : Previous) where
  | missingPayer
      (exact : profile.ExactOutput previous)
      (selected : exact.output.fst.terminal = .missingPayer)
  | overloadedFibre
      (exact : profile.ExactOutput previous)
      (selected : exact.output.fst.terminal = .overloadedFibre)
  | assignmentCertificate
      (exact : profile.ExactOutput previous)
      (selected : exact.output.fst.terminal = .c4)
  | aggregateCertificate
      (exact : profile.ExactOutput previous)
      (assignmentSelected : exact.output.fst.terminal = .capacity)
      (selected : exact.output.snd.terminal = .aggregate)
  | capacityResidual
      (exact : profile.ExactOutput previous)
      (assignmentSelected : exact.output.fst.terminal = .capacity)
      (selected : exact.output.snd.terminal = .capacity)

/-- Every exhaustive accounting route retains the identical composed CT
output.  This projection lets later Strategies read that output without
matching separately on the five terminals. -/
def RoutedResidual.exactOutput {previous : Previous} :
    profile.RoutedResidual previous → profile.ExactOutput previous
  | .missingPayer exact _ => exact
  | .overloadedFibre exact _ => exact
  | .assignmentCertificate exact _ => exact
  | .aggregateCertificate exact _ _ => exact
  | .capacityResidual exact _ _ => exact

/-- Exact CT4 assignment state preserved by every accounting route. -/
def RoutedResidual.assignmentState {previous : Previous}
    (routed : profile.RoutedResidual previous) :
    CT4.AssignmentState profile.assignment.assignmentCapability previous :=
  routed.exactOutput.assignmentState

/-- Interpret the complete composed output once.  CT14 is semantically
consumed only on CT4's capacity terminal; all other CT4 terminals remain
explicit typed successors. -/
noncomputable def route (previous : Previous) :
    profile.RoutedResidual previous :=
  let output := profile.execution.run previous
  let exact : profile.ExactOutput previous :=
    ⟨output, rfl, rfl, rfl⟩
  match assignmentTerminal : output.fst.terminal with
  | .missingPayer =>
      .missingPayer exact assignmentTerminal
  | .overloadedFibre =>
      .overloadedFibre exact assignmentTerminal
  | .c4 =>
      .assignmentCertificate exact assignmentTerminal
  | .capacity =>
      match aggregateTerminal : output.snd.terminal with
      | .unboundedMember =>
          (profile.noUnbounded output.snd aggregateTerminal).elim
      | .missingLabel =>
          (profile.noMissingLabel output.snd aggregateTerminal).elim
      | .aggregate =>
          .aggregateCertificate exact assignmentTerminal aggregateTerminal
      | .capacity =>
          .capacityResidual exact assignmentTerminal aggregateTerminal

/-- Standard completed Strategy boundary over the exhaustive typed result.
Core appends this one payload; applications cannot supply an interpreter for
either CT terminal. -/
noncomputable def contract : Core.Strategy.Contract Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Payload := fun previous _ => profile.RoutedResidual previous
  produce := fun previous => ⟨.completed, profile.route previous⟩
  exhaustive := fun previous => ⟨⟨.completed, profile.route previous⟩⟩

/-- Exact numeric ledger of whichever exhaustive successor Core routed to.
Every constructor retains the same literal CT4 output. -/
def summaryOfRouted {previous : Previous} :
    profile.RoutedResidual previous → Summary
  | .missingPayer exact _ =>
      profile.assignment.summaryOfResult exact.output.fst
  | .overloadedFibre exact _ =>
      profile.assignment.summaryOfResult exact.output.fst
  | .assignmentCertificate exact _ =>
      profile.assignment.summaryOfResult exact.output.fst
  | .aggregateCertificate exact _ _ =>
      profile.assignment.summaryOfResult exact.output.fst
  | .capacityResidual exact _ _ =>
      profile.assignment.summaryOfResult exact.output.fst

/-- The inherited CT9 partition equation for the summary on every route. -/
theorem summaryOfRouted_partition {previous : Previous}
    (routed : profile.RoutedResidual previous)
    (partition :
      let summary := profile.assignment.normalizationSummary previous
        (profile.assignment.normalizedSupport.read previous)
      summary.selectedCount + summary.complementCount = summary.ambientCount) :
    (profile.summaryOfRouted routed).selectedCount +
        (profile.summaryOfRouted routed).complementCount =
      (profile.summaryOfRouted routed).ambientCount := by
  cases routed with
  | missingPayer exact selected
  | overloadedFibre exact selected
  | assignmentCertificate exact selected
  | aggregateCertificate exact assignmentSelected selected
  | capacityResidual exact assignmentSelected selected =>
      exact profile.assignment.summaryOfResult_selectedCount_add_complementCount_eq_ambientCount
        exact.output.fst (exact.assignmentPrevious.symm ▸ partition)

/-- CT4's capacity terminal publishes its exact aggregate inequality on every
outer route; no schedule is rerun to obtain it. -/
theorem summaryOfRouted_required_le_capacity {previous : Previous}
    (routed : profile.RoutedResidual previous)
    (selected : routed.exactOutput.output.fst.terminal = .capacity) :
    (profile.summaryOfRouted routed).requiredTotal ≤
      (profile.summaryOfRouted routed).capacityTotal := by
  cases routed with
  | missingPayer exact routeSelected
  | overloadedFibre exact routeSelected
  | assignmentCertificate exact routeSelected
  | aggregateCertificate exact routeSelected aggregateSelected
  | capacityResidual exact routeSelected aggregateSelected =>
      have outcome : CT4.Outcome profile.assignment.assignmentCapability
          exact.output.fst.stage.previous .capacity := by
        rw [← selected]
        exact exact.output.fst.outcome
      cases outcome with
      | capacity total bounded residual =>
          exact residual

end Profile

/-- Query-only facts published by a completed CT4 → CT14 operation.

The record contains no executable function and no presentation data.  Its
terminal fields and inequalities are projections of the literal CT outputs
which Core appended at the producer stage.  Consequently a later Strategy can
inspect the accounting result without rerunning either CT or reconstructing a
schedule from the stable residual. -/
def Profile.ofRegistrationAt
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    (registration :
      Registration.{uResidual, uDemand, uPayer, uMember, uLabel} Residual)
    (current : Query Previous fun _ => Residual)
    (support : Query Previous fun _ =>
      ULift.{uSupport} SupportComplementNormalization.Summary) :
    Profile.{u, uResidual, uSupport, uDemand, uPayer, uMember, uLabel}
      Previous Residual :=
  let assignment :
      AssignmentProfile.{u, uSupport, uDemand, uPayer} Previous :=
    { NormalizedSupport := fun _ =>
        ULift.{uSupport} SupportComplementNormalization.Summary
      normalizedSupport := support
      Demand := fun previous _ =>
        registration.Demand (current.read previous)
      Payer := fun previous _ =>
        registration.Payer (current.read previous)
      demands := fun previous _ =>
        registration.demands (current.read previous)
      payers := fun previous _ =>
        registration.payers (current.read previous)
      Eligible := fun previous _ =>
        registration.Eligible (current.read previous)
      eligibleDecidable := fun previous _ =>
        registration.eligibleDecidable (current.read previous)
      demandWeight := fun previous _ =>
        registration.demandWeight (current.read previous)
      payerCapacity := fun previous _ =>
        registration.payerCapacity (current.read previous)
      normalizationSummary := fun _ support => support.down }
  { assignment
    aggregate :=
      { Member := fun previous _ _ =>
          registration.Member (current.read previous)
        Label := fun previous _ _ =>
          registration.Label (current.read previous)
        members := fun previous _ _ =>
          registration.members (current.read previous)
        memberLowerMass := fun previous _ _ =>
          registration.memberLowerMass (current.read previous)
        -- Manuscript node [29]: the external-incidence supply available to a
        -- member is its registered rate times the exact selected count
        -- published by the preceding support-complement normalization.
        memberCapacity := fun previous _ support member =>
          registration.memberCapacityRate (current.read previous) member *
            support.down.selectedCount
        memberLabel := fun previous _ _ =>
          registration.memberLabel (current.read previous)
        labelDecidableEq := fun previous _ _ =>
          registration.labelDecidableEq (current.read previous) } }

/-- Stable-residual specialization of the query-native constructor. -/
def Profile.ofRegistration
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    (registration :
      Registration.{uResidual, uDemand, uPayer, uMember, uLabel} Residual)
    (support : Query Previous fun _ =>
      ULift.{uSupport} SupportComplementNormalization.Summary) :
    Profile.{u, uResidual, uSupport, uDemand, uPayer, uMember, uLabel}
      Previous Residual :=
  Profile.ofRegistrationAt registration Query.residual support

end Hypostructure.Core.Strategy.BoundaryDemandAccounting
