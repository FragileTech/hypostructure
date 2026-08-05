import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.BoundaryDemandAccountingSemantics
import Hypostructure.Core.Strategy.SupportComplementNormalization

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
          (profile.normalizedSupport previous)) :=
  profile.normalizedSupport.dependentMap fun previous support =>
    profile.demands previous support

/-- Exact payer schedule projected from the same predecessor-owned support. -/
def payerQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Payer previous
          (profile.normalizedSupport previous)) :=
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
          (profile.normalizedSupport previous)) :=
  profile.assignmentInputs.map fun _ inputs => inputs.fst

/-- CT4's payer schedule, projected dependently from the exact combined
query. -/
def assignmentPayers :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.Payer previous
          (profile.normalizedSupport previous)) :=
  profile.assignmentInputs.dependentMap fun _ inputs => inputs.snd

/-- CT4 semantics on the literal predecessor.

The required total is definitionally the sum of the exact demand weights; it
is not accepted as registration data. -/
def assignmentSpec : CT4.Spec Previous where
  Demand := fun previous =>
    profile.Demand previous
      (profile.normalizedSupport previous)
  Payer := fun previous =>
    profile.Payer previous
      (profile.normalizedSupport previous)
  Eligible := fun previous =>
    profile.Eligible previous
      (profile.normalizedSupport previous)
  demandWeight := fun previous =>
    profile.demandWeight previous
      (profile.normalizedSupport previous)
  capacity := fun previous =>
    profile.payerCapacity previous
      (profile.normalizedSupport previous)
  required := fun previous =>
    ((profile.assignmentDemands previous).values.map
      (profile.demandWeight previous
        (profile.normalizedSupport previous))).sum

/-- CT4 capability derived from the two exact queried schedules. -/
def assignmentCapability : CT4.Capability profile.assignmentSpec where
  demands := profile.assignmentDemands
  payers := profile.assignmentPayers
  eligibleDecidable := fun previous =>
    profile.eligibleDecidable previous
      (profile.normalizedSupport previous)
  inputSize := fun previous =>
    CT4.localCheckBound
      (profile.assignmentDemands previous)
      (profile.assignmentPayers previous)
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
        (profile.normalizedSupport result.stage.previous)).ambientCount
    selectedCount :=
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport result.stage.previous)).selectedCount
    complementCount :=
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport result.stage.previous)).complementCount }

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
          (profile.normalizedSupport
            result.stage.previous)).selectedCount +
        (profile.normalizationSummary result.stage.previous
          (profile.normalizedSupport
            result.stage.previous)).complementCount =
      (profile.normalizationSummary result.stage.previous
        (profile.normalizedSupport result.stage.previous)).ambientCount) :
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
      let inputs := profile.assignment.assignmentAndSupport stage
      Core.Finite.Enumeration
        (profile.aggregate.Member stage.previous inputs.fst inputs.snd) :=
  profile.assignment.assignmentAndSupport.dependentMap
    fun stage inputs =>
      profile.aggregate.members stage.previous inputs.fst inputs.snd

/-- CT14 semantics over the exact paired predecessor views. -/
def aggregateSpec : CT14.Spec profile.AfterAssignment where
  Member := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport stage
    profile.aggregate.Member stage.previous inputs.fst inputs.snd
  Label := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport stage
    profile.aggregate.Label stage.previous inputs.fst inputs.snd
  memberLowerMass := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport stage
    profile.aggregate.memberLowerMass
      stage.previous inputs.fst inputs.snd member
  memberCapacity := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport stage
    some (profile.aggregate.memberCapacity
      stage.previous inputs.fst inputs.snd member)
  memberLabel := fun stage member =>
    let inputs := profile.assignment.assignmentAndSupport stage
    some (profile.aggregate.memberLabel
      stage.previous inputs.fst inputs.snd member)

/-- CT14 capability derived from the exact generated accounting schedule. -/
def aggregateCapability : CT14.Capability profile.aggregateSpec where
  members := profile.aggregateMembers
  labelDecidableEq := fun stage =>
    let inputs := profile.assignment.assignmentAndSupport stage
    profile.aggregate.labelDecidableEq
      stage.previous inputs.fst inputs.snd
  inputSize := fun stage =>
    CT14.localCheckBound (profile.aggregateMembers stage)
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

/-- The sealed strategy exposes the canonical composed execution directly.
There is no strategy-local router, replacement residual, or callback surface:
Core's `toContract` appends the literal CT4–CT14 output to the one dependent
ledger chain. -/
noncomputable def contract : Core.Strategy.Contract Previous :=
  profile.execution.toContract

/-- Numeric projection of the literal CT4 component retained by Core's
composed output. -/
def summaryOfOutput {previous : Previous}
    (output : profile.execution.Output previous) : Summary :=
  profile.assignment.summaryOfResult output.fst

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
    {AmbientItem : Residual → Type uDemand}
    {ambient : (residual : Residual) →
      Core.Finite.Enumeration (AmbientItem residual)}
    {Block : Residual → Type uPayer}
    {cover : (residual : Residual) → Block residual →
      List (AmbientItem residual)}
    (registration :
      Registration Residual AmbientItem ambient Block cover)
    (current : Query Previous fun _ => Residual)
    (exact : SupportComplementNormalization.ExactLedger Previous Residual
      (fun previous => AmbientItem (current previous))) :
    Profile
      Previous Residual :=
  let assignment :
      AssignmentProfile Previous :=
    { NormalizedSupport := fun _ => PUnit
      normalizedSupport :=  fun _ => PUnit.unit
      Demand := fun previous _ =>
        { pair : AmbientItem (current previous) ×
            AmbientItem (current previous) //
          registration.Interaction (current previous) pair.1 pair.2 }
      Payer := fun previous _ =>
        { pair : exact.Block previous × AmbientItem (current previous) //
          pair.2 ∈ exact.cover previous pair.1 }
      demands := fun previous _ =>
        (exact.complement previous).product
          (exact.selected previous) |>.subtype
            (fun pair => registration.Interaction
              (current previous) pair.1 pair.2)
            (fun pair => registration.interactionDecidable
              (current previous) pair.1 pair.2)
      payers := fun previous _ =>
        (exact.blocks previous).product
          (exact.ambient previous) |>.subtype
            (fun pair => pair.2 ∈ exact.cover previous pair.1)
            (fun pair => by
              letI := (exact.ambient previous).decEq
              exact inferInstance)
      Eligible := fun _ _ demand payer => demand.1.2 = payer.1.2
      eligibleDecidable := fun previous _ _ _ => by
        letI := (exact.ambient previous).decEq
        exact inferInstance
      demandWeight := fun _ _ _ => 1
      payerCapacity := fun previous _ payer => by
        letI := (exact.ambient previous).decEq
        exact (exact.ambient previous).values.countP fun other =>
          @decide (registration.Interaction
            (current previous) payer.1.2 other)
            (registration.interactionDecidable
              (current previous) payer.1.2 other) &&
          !decide (other ∈ exact.cover previous payer.1.1)
      normalizationSummary := fun previous _ => exact.summary previous }
  { assignment
    aggregate :=
      { Member := fun previous _ _ => AmbientItem (current previous)
        Label := fun previous _ _ => AmbientItem (current previous)
        members := fun previous _ _ => exact.complement previous
        memberLowerMass := fun previous _ _ member =>
          registration.baseline (current previous) -
            (exact.complement previous).values.countP fun other =>
              @decide (registration.Interaction
                (current previous) member other)
                (registration.interactionDecidable
                  (current previous) member other)
        memberCapacity := fun previous _ _ member =>
          (exact.selected previous).values.countP fun other =>
            @decide (registration.Interaction
              (current previous) member other)
              (registration.interactionDecidable
                (current previous) member other)
        memberLabel := fun _ _ _ member => member
        labelDecidableEq := fun previous _ _ =>
          (exact.ambient previous).decEq } }

/-- Stable-residual specialization of the query-native constructor. -/
def Profile.ofRegistration
    {Previous : Type u} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uDemand}
    {ambient : (residual : Residual) →
      Core.Finite.Enumeration (AmbientItem residual)}
    {Block : Residual → Type uPayer}
    {cover : (residual : Residual) → Block residual →
      List (AmbientItem residual)}
    (registration :
      Registration Residual AmbientItem ambient Block cover)
    (exact : SupportComplementNormalization.ExactLedger Previous Residual
      (fun previous => AmbientItem (residualOf previous))) :
    Profile Previous Residual :=
  Profile.ofRegistrationAt registration Query.residual exact

end Hypostructure.Core.Strategy.BoundaryDemandAccounting
