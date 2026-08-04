import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics
import Hypostructure.Core.Strategy.SupportComplementNormalization

/-!
# Local supply lower bound

This domain-neutral Strategy is exactly one CT14 execution.  Its finite
member schedule and all primitive observations are dependent views of one
exact predecessor-ledger query.  CT14 performs the only aggregation and
comparison, and its literal execution result is the sole output retained for
later Strategies.

The interpretation below contains only pointwise mathematical semantics.  It
contains no executor, route, terminal, aggregate result, work parameter, or
ledger operation.
-/

namespace Hypostructure.Core.Strategy.LocalSupplyLowerBound

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uBoundary uAmbient uMember uLabel uPiece

/-- Domain-neutral pointwise interpretation of an exact boundary-accounting
ledger value.

The local member schedule is projected from that value.  Required mass,
observed supply, and defect correction are primitive observations on each
projected member.  The pointwise law is the only mathematical provision:
CT14 still computes both aggregate ledgers and performs their sole
comparison. -/
structure Interpretation (Previous : Type uPrevious)
    (BoundaryAccounting : Previous → Type uBoundary) where
  Member :
    (previous : Previous) →
      BoundaryAccounting previous → Type uMember
  Label :
    (previous : Previous) →
      BoundaryAccounting previous → Type uLabel
  members :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Core.Finite.Enumeration (Member previous accounting)
  requiredMass :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Member previous accounting → Nat
  observedSupply :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Member previous accounting → Nat
  defectCorrection :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Member previous accounting → Nat
  surplus :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Member previous accounting → Nat
  label :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        Member previous accounting → Label previous accounting
  labelDecidableEq :
    (previous : Previous) →
      (accounting : BoundaryAccounting previous) →
        DecidableEq (Label previous accounting)
  pointwise :
    ∀ previous accounting member,
      requiredMass previous accounting member ≤
        observedSupply previous accounting member +
          defectCorrection previous accounting member

/-- Exact predecessor input for the reusable Strategy.  The accounting value
is a typed read from the accumulated Core ledger; no producer is named or
recomputed. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  BoundaryAccounting : Previous → Type uBoundary
  boundaryAccounting :
    Query Previous BoundaryAccounting
  /-- The exact boundary-accounting ledger carried by the dependent value this
  Strategy reads.  It is a projection of that value, not a second observation:
  the node-`[29]` window/remainder counts `n`, `|W|`, `|R|` travel here on the
  same entry `boundaryAccounting` already reads. -/
  accountingSummary :
    (previous : Previous) → BoundaryAccounting previous →
      BoundaryDemandAccounting.Summary
  interpretation :
    Interpretation.{
      uPrevious, uBoundary, uMember, uLabel}
      Previous BoundaryAccounting

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uBoundary, uMember, uLabel}
    Previous Residual)

/-- Exact local-cell schedule projected from the predecessor's accounting
entry. -/
def localCells :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.interpretation.Member previous
          (profile.boundaryAccounting.read previous)) :=
  profile.boundaryAccounting.dependentMap
    fun previous accounting =>
      profile.interpretation.members previous accounting

/-- The producer value and its projected member schedule, read at the same
literal predecessor. -/
def accountingAndCells :
    Query Previous fun previous =>
      PProd
        (profile.BoundaryAccounting previous)
        (Core.Finite.Enumeration
          (profile.interpretation.Member previous
            (profile.boundaryAccounting.read previous))) :=
  profile.boundaryAccounting.and profile.localCells

/-- CT14 primitive semantics over the exact predecessor-owned accounting
value.  Capacities and labels are total by construction; their values remain
the registered pointwise observations. -/
def spec : CT14.Spec Previous where
  Member := fun previous =>
    profile.interpretation.Member previous
      (profile.boundaryAccounting.read previous)
  Label := fun previous =>
    profile.interpretation.Label previous
      (profile.boundaryAccounting.read previous)
  memberLowerMass := fun previous member =>
    let accounting := (profile.accountingAndCells.read previous).fst
    profile.interpretation.requiredMass previous accounting member
  memberCapacity := fun previous member =>
    let accounting := (profile.accountingAndCells.read previous).fst
    some
      (profile.interpretation.observedSupply previous accounting member +
        profile.interpretation.defectCorrection previous accounting member)
  memberLabel := fun previous member =>
    let accounting := (profile.accountingAndCells.read previous).fst
    some (profile.interpretation.label previous accounting member)

/-- CT14 capability on the exact dependent member schedule.  Its polynomial
envelope is derived internally from `CT14.localCheckBound`; no work
coefficient or degree is accepted by the profile. -/
def capability : CT14.Capability profile.spec where
  members := profile.localCells
  labelDecidableEq := fun previous =>
    profile.interpretation.labelDecidableEq previous
      (profile.boundaryAccounting.read previous)
  inputSize := fun previous =>
    CT14.localCheckBound (profile.localCells.read previous)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The sole executable object: Core's canonical CT14 adapter. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct14 profile.capability

private theorem noUnbounded (previous : Previous)
    (residual :
      CT14.UnboundedMemberResidual profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

private theorem noMissingLabel (previous : Previous)
    (residual :
      CT14.MissingLabelResidual profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

/-- Summing the registered pointwise inequality over CT14's exact member
schedule bounds its generated lower-mass ledger by its generated capacity
ledger. -/
theorem lowerMass_le_upperCapacity (previous : Previous) :
    CT14.lowerMass profile.capability previous ≤
      CT14.upperCapacity profile.capability previous := by
  unfold CT14.lowerMass CT14.lowerMassEntries
    CT14.upperCapacity CT14.capacityEntries
  simp only [List.map_map]
  apply List.sum_le_sum
  intro member _member
  exact profile.interpretation.pointwise
    previous (profile.boundaryAccounting.read previous) member

private theorem noAggregate (previous : Previous)
    (ledger : CT14.AggregateLedger profile.capability previous)
    (certificate :
      CT14.AggregateCertificate profile.capability previous ledger) :
    False := by
  apply Nat.not_lt_of_ge (profile.lowerMass_le_upperCapacity previous)
  simpa [ledger.capacity.total_exact, ledger.lower.total_exact] using
    certificate

/-- CT14's three non-capacity terminals are impossible for any literal
result produced by this capability.  The retained result is inspected
directly; neither execution nor the aggregate comparison is repeated. -/
theorem execution_terminal
    (result : profile.execution.Output previous) :
    result.terminal = .capacity := by
  cases terminalEq : result.terminal with
  | unboundedMember =>
      have outcome :
          CT14.Outcome profile.capability result.stage.previous
            .unboundedMember := by
        simpa [terminalEq] using result.outcome
      cases outcome with
      | unboundedMember _ residual =>
          exact
            (profile.noUnbounded result.stage.previous residual).elim
  | missingLabel =>
      have outcome :
          CT14.Outcome profile.capability result.stage.previous
            .missingLabel := by
        simpa [terminalEq] using result.outcome
      cases outcome with
      | missingLabel _ _ residual =>
          exact
            (profile.noMissingLabel result.stage.previous residual).elim
  | aggregate =>
      have outcome :
          CT14.Outcome profile.capability result.stage.previous
            .aggregate := by
        simpa [terminalEq] using result.outcome
      cases outcome with
      | aggregate ledger certificate =>
          exact
            (profile.noAggregate result.stage.previous ledger certificate).elim
  | capacity =>
      rfl

/-- Exact capacity-terminal successor.  It retains CT14's literal result and
the terminal equality derived from that same result; no supply total or
comparison is copied into a feature-local summary. -/
structure CapacityResidual (previous : Previous) where
  result : profile.execution.Output previous
  previous_eq : result.stage.previous = previous
  selected : result.terminal = .capacity

/-- Produce the typed successor from CT14's one canonical execution. -/
noncomputable def capacityResidual (previous : Previous) :
    profile.CapacityResidual previous :=
  let result := profile.execution.run previous
  ⟨result, rfl, profile.execution_terminal result⟩

/-- The public Strategy contract exposes only the exact capacity successor
proved above.  Core appends this payload at the ordinary contract boundary. -/
noncomputable def contract : Core.Strategy.Contract Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Payload := fun previous _ => profile.CapacityResidual previous
  produce := fun previous => ⟨.completed, profile.capacityResidual previous⟩
  exhaustive := fun previous =>
    ⟨⟨.completed, profile.capacityResidual previous⟩⟩

/-- Literal accumulated-ledger shape after the narrowed Strategy boundary. -/
abbrev AfterLocalSupply :=
  Ledger.Extension Previous profile.CapacityResidual

end Profile

/-- Exact dependent carrier retained by the local-supply execution.

This is a query-only view of CT14's literal member schedule.  In particular,
it is not a second registration, a copied summary, or a reconstructed finite
family: `members` is the same `Profile.localCells` query consumed by CT14,
transported through the ordinary ledger extension. -/
structure ExactLedger (Stage : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Stage Residual] (Member : Stage → Type uMember) where
  members : Query Stage fun stage =>
    Core.Finite.Enumeration (Member stage)
  sourceResidual : Query Stage fun _ => Residual

namespace ExactLedger

variable {Stage : Type uPrevious} {Residual : Type uResidual}
variable [HasResidual Stage Residual]

/-- Reindex an exact CT14 carrier along a residual-preserving stage map. -/
def comap {Stage' : Type uBoundary} [HasResidual Stage' Residual]
    (ledger : ExactLedger.{uPrevious, uResidual, uMember}
      Stage Residual Member)
    (f : Stage' → Stage)
    (_residual_eq : ∀ stage, residualOf (f stage) = residualOf stage) :
    ExactLedger.{uBoundary, uResidual, uMember} Stage' Residual
      (fun stage => Member (f stage)) where
  members := ledger.members.comap f
  sourceResidual := ledger.sourceResidual.comap f

/-- Reindex through a residual-preserving projection when the consumer names
the member carrier through its own propositionally equal residual view. -/
def comapTo {Stage' : Type uBoundary} [HasResidual Stage' Residual]
    (ledger : ExactLedger.{uPrevious, uResidual, uMember}
      Stage Residual Member)
    (f : Stage' → Stage)
    (_residual_eq : ∀ stage, residualOf (f stage) = residualOf stage)
    (NewMember : Stage' → Type uMember)
    (member_eq : ∀ stage, Member (f stage) = NewMember stage) :
    ExactLedger.{uBoundary, uResidual, uMember} Stage' Residual NewMember where
  members := Query.ofFunction fun stage =>
    member_eq stage ▸ ledger.members.read (f stage)
  sourceResidual := ledger.sourceResidual.comap f

/-- Preserve the exact CT14 carrier through an ordinary ledger extension. -/
def preserve {Added : Stage → Type uBoundary}
    (ledger : ExactLedger.{uPrevious, uResidual, uMember}
      Stage Residual Member) :
    ExactLedger.{max uPrevious uBoundary, uResidual, uMember}
      (Ledger.Extension Stage Added) Residual
      (fun stage => Member stage.previous) :=
  ledger.comap
    (fun stage : Ledger.Extension Stage Added => stage.previous)
    (fun _ => rfl)

end ExactLedger

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uBoundary, uMember, uLabel}
    Previous Residual)

/-- Exact capacity successor introduced by the newest ledger entry. -/
def localSupplyResult :
    Query profile.AfterLocalSupply
      (fun stage => profile.CapacityResidual stage.previous) :=
  Query.latest

/-- The exact dependent member family consumed by CT14, retained on its
literal successor without rebuilding it from the stable residual. -/
def exactLedger :
    ExactLedger profile.AfterLocalSupply Residual (fun stage =>
      profile.interpretation.Member stage.previous
        (profile.boundaryAccounting.read stage.previous)) where
  members := profile.localCells.preserve
  sourceResidual := Query.residual

/-- Preserve the exact boundary-accounting value through the CT14 extension.
The newest entry is the supply result; the inherited accounting value remains
available through the ordinary ledger query. -/
def boundaryAccountingAfterLocalSupply :
    Query profile.AfterLocalSupply
      (fun stage => profile.BoundaryAccounting stage.previous) :=
  profile.boundaryAccounting.preserve

/-- The exact aggregate ledger computed by CT14 on its capacity terminal,
transported to the local-supply predecessor. -/
def CapacityResidual.aggregateLedger
    {previous : Previous} (capacity : profile.CapacityResidual previous) :
    CT14.AggregateLedger profile.capability previous := by
  have outcome : CT14.Outcome profile.capability
      capacity.result.stage.previous .capacity := by
    simpa [capacity.selected] using capacity.result.outcome
  cases outcome with
  | capacity ledger _ =>
      exact capacity.previous_eq ▸ ledger

/-- Aggregate of the registered per-member surplus observation over CT14's
own exact member schedule.  It is the same list CT14 sums for its lower-mass
and capacity ledgers, so no member family is rebuilt. -/
def assignedSurplusTotal (previous : Previous) : Nat :=
  ((profile.localCells.read previous).values.map
    (profile.interpretation.surplus previous
      (profile.boundaryAccounting.read previous))).sum

/-- Aggregate of the registered per-member observed supply over the same exact
member schedule.  On the graph adapter the members are the normalized support
and the observation is the count of incidences leaving it, so this is literally
`e(R, W)`. -/
def observedSupplyTotal (previous : Previous) : Nat :=
  ((profile.localCells.read previous).values.map
    (profile.interpretation.observedSupply previous
      (profile.boundaryAccounting.read previous))).sum

/-- Aggregate of the registered per-member defect correction over the same
exact member schedule.  On the graph adapter the observation is the *ambient*
deficiency `baseline - d_G(v)` of a member, so this is the total ambient
deficiency carried by the members; it is not the manuscript's `def⁺(R)`, which
is the *internal* deficiency `∑_v max(0, baseline - d_R(v))` and is aggregated
by CT14 itself as `lowerMass`. -/
def assignedDefectTotal (previous : Previous) : Nat :=
  ((profile.localCells.read previous).values.map
    (profile.interpretation.defectCorrection previous
      (profile.boundaryAccounting.read previous))).sum

private theorem sum_map_add {Item : Type uMember} (items : List Item)
    (left right : Item → Nat) :
    (items.map fun item => left item + right item).sum =
      (items.map left).sum + (items.map right).sum := by
  induction items with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- CT14's generated capacity ledger splits exactly into the two registered
per-member observations it was built from.  Nothing is recomputed: both sides
sum the same literal member schedule. -/
theorem upperCapacity_eq_observedSupplyTotal_add_assignedDefectTotal
    (previous : Previous) :
    CT14.upperCapacity profile.capability previous =
      profile.observedSupplyTotal previous +
        profile.assignedDefectTotal previous := by
  unfold CT14.upperCapacity CT14.capacityEntries CT14.Capability.membersAt
    observedSupplyTotal assignedDefectTotal
  simp only [List.map_map]
  exact sum_map_add (profile.localCells.read previous).values
    (profile.interpretation.observedSupply previous
      (profile.boundaryAccounting.read previous))
    (profile.interpretation.defectCorrection previous
      (profile.boundaryAccounting.read previous))

/-- The aggregated pointwise law in the manuscript's own variables: the
internal deficiency of the member schedule is covered by its external supply
plus its ambient deficiency correction.  On the graph adapter this is
`def⁺(R) ≤ e(R, W) + ∑_{v ∈ R} max(0, baseline - d_G(v))`, i.e.
`lem:stub-positive` without its minimum-degree hypothesis: when the ambient
minimum degree meets the baseline the correction vanishes and the statement
degenerates to `def⁺(R) ≤ e(R, W)`. -/
theorem lowerMass_le_observedSupplyTotal_add_assignedDefectTotal
    (previous : Previous) :
    CT14.lowerMass profile.capability previous ≤
      profile.observedSupplyTotal previous +
        profile.assignedDefectTotal previous := by
  rw [← profile.upperCapacity_eq_observedSupplyTotal_add_assignedDefectTotal]
  exact profile.lowerMass_le_upperCapacity previous

/-- Cardinality of CT14's exact member schedule.  On the graph adapter the
members are the normalized support, so this is literally `|R|`. -/
def remainderCard (previous : Previous) : Nat :=
  (profile.localCells.read previous).card

/-- An empty member schedule carries no required mass.

`CT14.lowerMass` folds the very list `remainderCard` counts, so when that count
is zero the list is `[]` and the fold is `0`.  Nothing is assumed about the
residual: this is a fact about one and the same `localCells` read. -/
theorem lowerMass_eq_zero_of_remainderCard_eq_zero (previous : Previous)
    (empty : profile.remainderCard previous = 0) :
    CT14.lowerMass profile.capability previous = 0 := by
  have lengthZero : (profile.localCells.read previous).values.length = 0 := by
    have card := empty
    unfold remainderCard at card
    rwa [Core.Finite.Enumeration.card_eq_length] at card
  have nil : (profile.localCells.read previous).values = [] :=
    List.eq_nil_of_length_eq_zero lengthZero
  unfold CT14.lowerMass CT14.lowerMassEntries CT14.Capability.membersAt
  simp only [capability]
  rw [nil]
  rfl

/-! ### `Finset` coordinates of the three published aggregates

The three theorems below are the producer-side half of the tie between the
numbers this Strategy publishes and the finite *set* a consumer names.  CT14
aggregates by folding its own `List` schedule; a consumer states its
certificate as a `Finset` sum over the support that schedule enumerates.  The
two agree because the schedule is an `Enumeration`, hence duplicate-free
(`Core.Finite.Enumeration.nodup`), so `List.sum_toFinset` applies verbatim.

Nothing is recomputed and no member family is rebuilt: both sides range over
the same literal `localCells` read.  A domain adapter finishes the tie by
identifying `(profile.localCells.read previous).toFinset` with its own support
(on the graph adapter that is
`Graph.Strategy.NormalizationRank.localSupply_members_toFinset`). -/

/-- CT14's own lower-mass aggregate, in `Finset` coordinates over the exact
member schedule's underlying finite set. -/
theorem lowerMass_eq_sum_toFinset (previous : Previous) :
    CT14.lowerMass profile.capability previous =
      ∑ member ∈ (profile.localCells.read previous).toFinset,
        profile.interpretation.requiredMass previous
          (profile.boundaryAccounting.read previous) member := by
  letI : DecidableEq
      (profile.interpretation.Member previous
        (profile.boundaryAccounting.read previous)) :=
    (profile.localCells.read previous).decEq
  have bridge :
      ∑ member ∈ (profile.localCells.read previous).toFinset,
          profile.interpretation.requiredMass previous
            (profile.boundaryAccounting.read previous) member =
        ((profile.localCells.read previous).values.map
          (profile.interpretation.requiredMass previous
            (profile.boundaryAccounting.read previous))).sum :=
    List.sum_toFinset _ (profile.localCells.read previous).nodup
  rw [bridge]
  unfold CT14.lowerMass CT14.lowerMassEntries CT14.Capability.membersAt
  simp only [List.map_map]
  rfl

/-- The published assigned-surplus aggregate, in the same `Finset`
coordinates. -/
theorem assignedSurplusTotal_eq_sum_toFinset (previous : Previous) :
    profile.assignedSurplusTotal previous =
      ∑ member ∈ (profile.localCells.read previous).toFinset,
        profile.interpretation.surplus previous
          (profile.boundaryAccounting.read previous) member := by
  letI : DecidableEq
      (profile.interpretation.Member previous
        (profile.boundaryAccounting.read previous)) :=
    (profile.localCells.read previous).decEq
  unfold assignedSurplusTotal
  exact (List.sum_toFinset _ (profile.localCells.read previous).nodup).symm

/-- The published observed-supply aggregate, in the same `Finset`
coordinates. -/
theorem observedSupplyTotal_eq_sum_toFinset (previous : Previous) :
    profile.observedSupplyTotal previous =
      ∑ member ∈ (profile.localCells.read previous).toFinset,
        profile.interpretation.observedSupply previous
          (profile.boundaryAccounting.read previous) member := by
  letI : DecidableEq
      (profile.interpretation.Member previous
        (profile.boundaryAccounting.read previous)) :=
    (profile.localCells.read previous).decEq
  unfold observedSupplyTotal
  exact (List.sum_toFinset _ (profile.localCells.read previous).nodup).symm

/-- The published member count is the cardinality of that same finite set.
`Core.Finite.Enumeration.card_toFinset` is exactly the duplicate-freedom of
the schedule. -/
theorem remainderCard_eq_card_toFinset (previous : Previous) :
    profile.remainderCard previous =
      (profile.localCells.read previous).toFinset.card :=
  (Core.Finite.Enumeration.card_toFinset _).symm

/-- Size of the *atom part* of CT14's own exact member schedule: the members
whose registered `surplus` observation vanishes.  It counts the same literal
member list `assignedSurplusTotal` sums, so no member family is rebuilt and no
new carrier is introduced.

On the graph adapter (`Graph.Strategy.NormalizationRank.localSupply`) the
registered surplus is `d_G(v) - baselineDegree`, so this counts exactly the
members of the normalized support `R` whose ambient degree does not exceed the
presentation's baseline degree.  That is the subcubicity coordinate of
`def:remainder-entropy`; the manuscript's `3` is the registered baseline. -/
def subcubicAtomCard (previous : Previous) : Nat :=
  (profile.localCells.read previous).values.countP fun member =>
    decide (profile.interpretation.surplus previous
      (profile.boundaryAccounting.read previous) member = 0)

private theorem length_le_countP_zero_add_sum {Item : Type uMember}
    (items : List Item) (value : Item → Nat) :
    items.length ≤
      (items.countP fun item => decide (value item = 0)) +
        (items.map value).sum := by
  induction items with
  | nil => simp
  | cons item tail ih =>
      have sumEq :
          ((item :: tail).map value).sum =
            value item + (tail.map value).sum := by
        simp
      by_cases zero : value item = 0
      · have countEq :
            ((item :: tail).countP fun x => decide (value x = 0)) =
              (tail.countP fun x => decide (value x = 0)) + 1 := by
          simp [List.countP_cons, zero]
        rw [List.length_cons, countEq, sumEq]
        omega
      · have countEq :
            ((item :: tail).countP fun x => decide (value x = 0)) =
              (tail.countP fun x => decide (value x = 0)) := by
          simp [List.countP_cons, zero]
        have positive : 1 ≤ value item := Nat.one_le_iff_ne_zero.mpr zero
        rw [List.length_cons, countEq, sumEq]
        omega

/-- **Subcubicity of the remainder, aggregated.**  Every member of CT14's exact
schedule either lies in the atom part or contributes at least one unit of
surplus, so all but `assignedSurplusTotal` members are subcubic against the
presentation's own baseline.  Nothing outside the registered `surplus`
observation is used, and no numeral appears: the baseline enters only through
the registration that defines `surplus`. -/
theorem remainderCard_le_subcubicAtomCard_add_assignedSurplusTotal
    (previous : Previous) :
    profile.remainderCard previous ≤
      profile.subcubicAtomCard previous +
        profile.assignedSurplusTotal previous := by
  unfold remainderCard subcubicAtomCard assignedSurplusTotal
  rw [Core.Finite.Enumeration.card_eq_length]
  exact
    length_le_countP_zero_add_sum
      (profile.localCells.read previous).values
      (profile.interpretation.surplus previous
        (profile.boundaryAccounting.read previous))

private theorem countP_le_length {Item : Type uMember} (items : List Item)
    (predicate : Item → Bool) :
    items.countP predicate ≤ items.length := by
  induction items with
  | nil => simp
  | cons item tail ih =>
      by_cases hit : predicate item = true
      · have countEq :
            (item :: tail).countP predicate = tail.countP predicate + 1 := by
          simp [List.countP_cons, hit]
        rw [List.length_cons, countEq]
        omega
      · have countEq :
            (item :: tail).countP predicate = tail.countP predicate := by
          simp [List.countP_cons, hit]
        rw [List.length_cons, countEq]
        omega

private theorem exists_pos_of_sum_pos {Item : Type uMember}
    (items : List Item) (value : Item → Nat) :
    0 < (items.map value).sum → ∃ item ∈ items, 0 < value item := by
  induction items with
  | nil => intro positive; simp at positive
  | cons item tail ih =>
      intro positive
      by_cases zero : value item = 0
      · have tailPositive : 0 < (tail.map value).sum := by
          simp only [List.map_cons, List.sum_cons, zero] at positive
          omega
        obtain ⟨witness, witnessMem, witnessPos⟩ := ih tailPositive
        exact ⟨witness, List.mem_cons_of_mem _ witnessMem, witnessPos⟩
      · exact ⟨item, by simp, Nat.pos_of_ne_zero zero⟩

private theorem countP_zero_lt_length_of_sum_pos {Item : Type uMember}
    (items : List Item) (value : Item → Nat) :
    0 < (items.map value).sum →
      (items.countP fun item => decide (value item = 0)) < items.length := by
  induction items with
  | nil => intro positive; simp at positive
  | cons item tail ih =>
      intro positive
      by_cases zero : value item = 0
      · have tailPositive : 0 < (tail.map value).sum := by
          simp only [List.map_cons, List.sum_cons, zero] at positive
          omega
        have countEq :
            ((item :: tail).countP fun x => decide (value x = 0)) =
              (tail.countP fun x => decide (value x = 0)) + 1 := by
          simp [List.countP_cons, zero]
        have inner := ih tailPositive
        rw [List.length_cons, countEq]
        omega
      · have countEq :
            ((item :: tail).countP fun x => decide (value x = 0)) =
              (tail.countP fun x => decide (value x = 0)) := by
          simp [List.countP_cons, zero]
        have bound := countP_le_length tail fun x => decide (value x = 0)
        rw [List.length_cons, countEq]
        omega

/-- **Extraction of an individual assigned member.**

`assignedSurplusTotal` is the sum of the registered per-member `surplus`
observation over CT14's *own* exact member schedule, so a positive total is
carried by a single member of that same schedule.  Nothing is constructed,
chosen or substituted: the witness is an element of the literal list CT14
already summed, and the statement adds no hypothesis.

On the graph adapter this is the individual high-degree fan centre of
`def:canonical-decomp`'s assigned support: the registered surplus is
`d_G(v) - baselineDegree`, so a member with positive surplus is a member `h` of
the normalized support with `baselineDegree < d_G(h)`
(`Graph.Strategy.NormalizationRank.localSupply_baselineDegree_le_degree_of_surplus_ne_zero`
converts the two).  No numeral appears here; the baseline enters only through
the registration that defines `surplus`. -/
theorem exists_surplus_member_of_assignedSurplusTotal_pos (previous : Previous)
    (positive : 0 < profile.assignedSurplusTotal previous) :
    ∃ member ∈ (profile.localCells.read previous).values,
      0 < profile.interpretation.surplus previous
        (profile.boundaryAccounting.read previous) member := by
  have expanded :
      0 <
        ((profile.localCells.read previous).values.map
          (profile.interpretation.surplus previous
            (profile.boundaryAccounting.read previous))).sum := positive
  exact exists_pos_of_sum_pos _ _ expanded

/-- The same extraction in the two published aggregates: a positive assigned
surplus makes the atom part a *proper* part of CT14's exact member schedule.
This is the ledger-coordinate form of
`exists_surplus_member_of_assignedSurplusTotal_pos`, and it is the form that
survives the ordinary ledger boundary, where only the numbers travel. -/
theorem subcubicAtomCard_lt_remainderCard_of_assignedSurplusTotal_pos
    (previous : Previous)
    (positive : 0 < profile.assignedSurplusTotal previous) :
    profile.subcubicAtomCard previous < profile.remainderCard previous := by
  have expanded :
      0 <
        ((profile.localCells.read previous).values.map
          (profile.interpretation.surplus previous
            (profile.boundaryAccounting.read previous))).sum := positive
  unfold subcubicAtomCard remainderCard
  rw [Core.Finite.Enumeration.card_eq_length]
  exact countP_zero_lt_length_of_sum_pos _ _ expanded

/-- **The net-deficiency cap, aggregated.**  CT14's own lower-mass ledger is
bounded by its own capacity ledger, and the published surplus aggregate is
nonnegative, so the *net* deficiency of the exact member schedule is bounded by
its external supply.

This is the fourth coordinate of `def:remainder-entropy`'s constrained
remainder family: "positive net-deficiency density at most the current cap".
The cap is not written here — it is the ratio of the two aggregates this same
Strategy publishes.  Dividing by `remainderCard` (`Summary`'s
`netDeficiencyDensity_le_cap`) gives

  `(def⁺(R) - σ_R) / |R| ≤ (e(R, W) + ∑_v max(0, k - d_G(v))) / |R|`,

which on a residual whose ambient minimum degree meets the presentation's
baseline `k` is exactly `Δ_net(R) ≤ e(R, W) / |R|`, the density form of
`lem:stub-positive`. -/
theorem lowerMass_le_upperCapacity_add_assignedSurplusTotal
    (previous : Previous) :
    CT14.lowerMass profile.capability previous ≤
      CT14.upperCapacity profile.capability previous +
        profile.assignedSurplusTotal previous :=
  Nat.le_trans (profile.lowerMass_le_upperCapacity previous)
    (Nat.le_add_right _ _)

/-- Exact numeric ledger published by one completed local-supply bound.

Every field is an aggregate of the *same* literal member schedule; nothing is
recomputed and no member family is rebuilt.  Against the graph adapter
(`Graph.Strategy.NormalizationRank.localSupply`, whose members are the
normalized support `R`) the published numbers are, in the manuscript's
notation of `def:deficiency-surplus`:

* `requiredMass = netDeficiency.deficiency = CT14.lowerMass`
  `= ∑_{v ∈ R} max(0, k - d_R(v)) = def⁺(R)` at the registered baseline `k`,
  the *internal* positive deficiency.  This is already the manuscript's
  quantity: the registered per-member observation is
  `baseline - supportIncidence v`, and `supportIncidence` counts incidences
  that stay inside `R`.
* `assignedSurplus = netDeficiency.surplus = assignedSurplusTotal
  = ∑_{v ∈ R} max(0, d_G(v) - k) = σ_R`, the ambient surplus carried by the
  members.
* `observedSupplyTotal = ∑_{v ∈ R} boundaryIncidence v = e(R, W)`.
* `assignedDefectTotal = ∑_{v ∈ R} max(0, k - d_G(v))` is the *ambient*
  deficiency of the members.  It is the slack by which this framework drops
  `lem:stub-positive`'s minimum-degree hypothesis; on a residual whose ambient
  minimum degree meets the baseline it is zero.  It is **not** `def⁺(R)`.
* `observedSupply = netDeficiency.coefficient = CT14.upperCapacity
  = e(R, W) + ∑_{v ∈ R} max(0, k - d_G(v))`
  (`upperCapacity_eq_observedSupplyTotal_add_assignedDefectTotal`), the
  *supply* side of `lem:stub-positive`.
* `netDeficiency.remainder = |R|`, and `netDeficiency.scale` is the same `|R|`
  wherever it is nonzero (see below).
* `netDeficiencyCap = lowerMass_le_upperCapacity_add_assignedSurplusTotal`
  `= (def⁺(R) ≤ e(R, W) + ∑_{v ∈ R} max(0, k - d_G(v)) + σ_R)`, the *net*
  deficiency cap.  Divided by the published `netDeficiency.remainder` it is the
  density statement `Summary.netDeficiencyDensity_le_cap`,
  `Δ_net(R) = (def⁺(R) - σ_R)/|R| ≤ observedSupply/|R|`, which is the fourth
  coordinate of `def:remainder-entropy`'s constrained remainder family.

**The published rate.**  `netDeficiency.coefficient / netDeficiency.scale` is
the manuscript's node-`[56]` net-deficiency cap
`Δ_net(R) = (def⁺(R) - σ_R)/|R| ≤ observedSupply/|R|`, and both of its two
numbers are aggregates this same ledger entry publishes:

* `coefficient` is `CT14.upperCapacity`, the supply column;
* `scale` is `remainderCard`, the member count.

No numeral is written and no threshold is chosen here.  In particular the rate
is *not* the domain's discharging rate `α`: `α` is a proof-design parameter of
the presentation (`Graph.ReceiverLoad.LoadCapacityProfile.dischargeRate`,
`α = 1/loadMultiplier`), and it belongs to the *consumer*, which instantiates
`NetDeficiencyAccounting.not_rate_reached`'s universally quantified `rate` at
it.  Publishing `α` as `coefficient/scale` here would be strictly wrong, not
merely redundant: `not_rate_reached` is applicable only *strictly above* the
published rate, so a producer publishing `α` makes the node-`[60]` conclusion
unreachable at `α` itself, which is the one rate the manuscript needs.

`scale` is written `max 1 remainderCard` rather than `remainderCard` because
`NetDeficiencyAccounting.scale_pos` requires a positive denominator and an
empty member schedule has none.  The guard is invisible wherever the ledger
entry is used: `not_rate_reached` and `FiniteStateNetChargeContinuation`'s
`NetCapContradiction60` both take `0 < remainder` as a hypothesis, and there
`max 1 remainderCard = remainderCard`.  On an empty schedule every aggregate is
`0` (`lowerMass_eq_zero_of_remainderCard_eq_zero`) and `finiteCap` degenerates
to `0 ≤ σ_R`.

**What this rate does and does not close.**  Instantiating
`NetCapContradiction60` at the presentation's own `α` discharges the manuscript's
`def:net-charge` alternative `α·|R| + σ_R ≤ def⁺(R)`, i.e. it yields
`def⁺(R) - σ_R < α·|R|` — verbatim `prop:negative-net-charge` — *provided* the
consumer supplies the applicability condition

  `observedSupply / |R| < α`,

which is exactly the manuscript's `Δ_net(R) ≤ τ_win < α` of node `[56]`.  That
condition is not a fact of this Strategy, and the manuscript does not prove it
locally either.  It needs, in the manuscript's own order:

1. `lem:surplus-aware-window-stub`'s supply bound
   `e(R, W) ≤ ∑_{P ∈ 𝒫} (stubs leaving P) = 15 p₁₃ + σ_W`, whose right-hand
   side is available as
   `Graph.InducedPathCold.externalStubSum_p13_eq_add_windowSurplus`.  The
   left-hand comparison is *not* available: it is the identification of this
   Strategy's member schedule with the complement of `⋃ 𝒫`, i.e. CT9's own
   fibre characterization
   `SupportComplementNormalization.PartitionProfile.mem_complementAtPrevious_iff`
   (`item ∈ complement ↔ ¬ Selected packing item`), which is proved at the
   support-complement node and is *not* a field of
   `SupportComplementNormalization.ExactLedger` — the only structure that
   reaches this Strategy (`Profile.ofRegistrationAt`'s `normalizedSupport`
   argument, and `Dag.lean`'s `LocalSupplyCapability.normalized`).  With the
   complement unlabelled, `p₁₃` arrives here as a bare `Nat` that no registered
   law connects to `observedSupplyTotal`.  Recomputing a packing from the
   residual to close the gap is the identification failure that has been removed
   once already: two maximal packings differ, and nothing identifies the
   recomputed one with the selected one this ledger's complement was cut from.

2. The packing-density cap `θ = p₁₃/n < 1/73` of the surviving density branch,
   which publishes no capability (`Dag.lean`, `finiteDensityBudgets`
   resolution, `rightProduced := []`).  Keying that residual would not by itself
   suffice: `prop:p13-density` gives only `θ ≤ θ_win + o(1)` with
   `θ_win = 3/(2 c_hot) = 0.012700…`, whose margin over `1/73 = 0.013698…` is a
   factor `1.079`, and the `o(1)` is inherited from the unquantified
   `O(n) + O(√n log n)` of `lem:near-cubic-budget` and the `⌊log₂ n⌋ - O(1)`
   scale count of `lem:p13-window-package`.  A strict finite-`n` form of
   `73 p₁₃ < n` therefore does not follow from the manuscript as written.

Both missing items are stated on this ledger's own published counts by
`Summary.negativeNetCharge_or_windowStubExcess` and
`Summary.windowJoinPressure_of_not_negativeNetCharge`, which quantify over
`windowOrder`, `stubRate` and `windowCount` rather than naming `13`, `15` or
`73`. -/
def summaryOfResidual {previous : Previous}
    (capacity : profile.CapacityResidual previous) : Summary :=
  let stage := capacity.result.stage.previous
  let required := CT14.lowerMass profile.capability stage
  let observed := CT14.upperCapacity profile.capability stage
  { requiredMass := required
    observedSupply := observed
    assignedSurplus := profile.assignedSurplusTotal stage
    subcubicAtomCard := profile.subcubicAtomCard stage
    netDeficiency :=
      { scale := max 1 (profile.remainderCard stage)
        coefficient := observed
        deficiency := required
        remainder := profile.remainderCard stage
        surplus := profile.assignedSurplusTotal stage
        scale_pos := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)
        finiteCap := by
          rcases Nat.eq_zero_or_pos (profile.remainderCard stage) with
            empty | positive
          · have massZero : required = 0 :=
              profile.lowerMass_eq_zero_of_remainderCard_eq_zero stage empty
            simp [empty, massZero]
          · rw [Nat.max_eq_right positive]
            calc
              profile.remainderCard stage * required
                  ≤ profile.remainderCard stage *
                      (observed + profile.assignedSurplusTotal stage) :=
                    Nat.mul_le_mul_left _
                      (profile.lowerMass_le_upperCapacity_add_assignedSurplusTotal
                        stage)
              _ = observed * profile.remainderCard stage +
                    profile.remainderCard stage *
                      profile.assignedSurplusTotal stage := by ring
      }
    subcubicAtomPart :=
      profile.remainderCard_le_subcubicAtomCard_add_assignedSurplusTotal stage
    assignedSurplusNonAtom := fun positive =>
      profile.subcubicAtomCard_lt_remainderCard_of_assignedSurplusTotal_pos
        stage positive
    netDeficiencyCap :=
      profile.lowerMass_le_upperCapacity_add_assignedSurplusTotal stage
    ambientCount :=
      (profile.accountingSummary stage
        (profile.boundaryAccounting.read stage)).ambientCount
    selectedCount :=
      (profile.accountingSummary stage
        (profile.boundaryAccounting.read stage)).selectedCount
    complementCount :=
      (profile.accountingSummary stage
        (profile.boundaryAccounting.read stage)).complementCount }

/-- **CT9's partition, transported onto the local-supply entry.**

The three window/remainder counts are the boundary-accounting ledger's own,
copied verbatim, which in turn copied them from CT9.  So `|W| + |R| = n`
travels here by definitional transport; the premise is exactly
`BoundaryDemandAccounting.AssignmentProfile.summaryOfResult_selectedCount_add_complementCount_eq_ambientCount`
read at the same predecessor.

This discharges the `partition` premise of
`Summary.negativeNetCharge_or_windowStubExcess` and
`Summary.windowJoinPressure_of_not_negativeNetCharge` whenever the registered
member schedule is CT9's complement, in which case
`netDeficiency.remainder = complementCount`. -/
theorem summaryOfResidual_selectedCount_add_complementCount_eq_ambientCount
    {previous : Previous} (capacity : profile.CapacityResidual previous)
    (partition :
      (profile.accountingSummary capacity.result.stage.previous
          (profile.boundaryAccounting.read
            capacity.result.stage.previous)).selectedCount +
        (profile.accountingSummary capacity.result.stage.previous
          (profile.boundaryAccounting.read
            capacity.result.stage.previous)).complementCount =
      (profile.accountingSummary capacity.result.stage.previous
        (profile.boundaryAccounting.read
          capacity.result.stage.previous)).ambientCount) :
    (profile.summaryOfResidual capacity).selectedCount +
        (profile.summaryOfResidual capacity).complementCount =
      (profile.summaryOfResidual capacity).ambientCount := partition

/-- The published complementary count is the normalization's own `|R|`, and the
published member count is this Strategy's own count of the schedule CT14
aggregated over.  They agree exactly when the registered member schedule is
CT9's complement -- which is the case for the graph adapter, where
`Graph.Strategy.NormalizationRank.localSupply.members` is
`complement.map ULift.down`.  The equation is stated, not assumed: a consumer
supplies it from the registration it actually installed. -/
theorem summaryOfResidual_remainder_eq_complementCount {previous : Previous}
    (capacity : profile.CapacityResidual previous)
    (schedule :
      profile.remainderCard capacity.result.stage.previous =
        (profile.accountingSummary capacity.result.stage.previous
          (profile.boundaryAccounting.read
            capacity.result.stage.previous)).complementCount) :
    (profile.summaryOfResidual capacity).netDeficiency.remainder =
      (profile.summaryOfResidual capacity).complementCount := schedule

/-- The published atom-part count is the literal aggregate over CT14's own
member schedule; a consumer reading the ledger reads exactly this. -/
@[simp] theorem summaryOfResidual_subcubicAtomCard {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).subcubicAtomCard =
      profile.subcubicAtomCard capacity.result.stage.previous :=
  rfl

/-- The published assigned-surplus aggregate is the literal sum over CT14's own
member schedule.  This is the bridge that lets a framework-side consumer which
still holds the profile move from the ledger number to
`exists_surplus_member_of_assignedSurplusTotal_pos`'s individual member. -/
@[simp] theorem summaryOfResidual_assignedSurplus {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).assignedSurplus =
      profile.assignedSurplusTotal capacity.result.stage.previous :=
  rfl

/-- The published required mass is CT14's own lower-mass ledger. -/
@[simp] theorem summaryOfResidual_requiredMass {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).requiredMass =
      CT14.lowerMass profile.capability capacity.result.stage.previous :=
  rfl

/-- The published member count is the cardinality of CT14's own schedule. -/
@[simp] theorem summaryOfResidual_remainder {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).netDeficiency.remainder =
      profile.remainderCard capacity.result.stage.previous :=
  rfl

/-! ### The three tie equations, published at the producing node

A consumer that states its certificate over a `Finset` support reads these
three instead of re-deriving the aggregates.  Each is the corresponding
`_eq_sum_toFinset` fact above, transported to the published `Summary` by the
three projections immediately preceding.  No support is recomputed: the
`Finset` on the right is the underlying finite set of CT14's own schedule. -/

theorem summaryOfResidual_remainder_eq_card {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).netDeficiency.remainder =
      (profile.localCells.read capacity.result.stage.previous).toFinset.card :=
  profile.remainderCard_eq_card_toFinset _

theorem summaryOfResidual_requiredMass_eq_sum {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).requiredMass =
      ∑ member ∈
        (profile.localCells.read capacity.result.stage.previous).toFinset,
        profile.interpretation.requiredMass capacity.result.stage.previous
          (profile.boundaryAccounting.read capacity.result.stage.previous)
          member :=
  profile.lowerMass_eq_sum_toFinset _

theorem summaryOfResidual_assignedSurplus_eq_sum {previous : Previous}
    (capacity : profile.CapacityResidual previous) :
    (profile.summaryOfResidual capacity).assignedSurplus =
      ∑ member ∈
        (profile.localCells.read capacity.result.stage.previous).toFinset,
        profile.interpretation.surplus capacity.result.stage.previous
          (profile.boundaryAccounting.read capacity.result.stage.previous)
          member :=
  profile.assignedSurplusTotal_eq_sum_toFinset _

end Profile

/-- Build the dependent Strategy profile from one inert registration and the
exact boundary-accounting ledger query supplied by the compiler.  The
registration contributes only pointwise semantics; every ledger read is a
Core-owned typed query. -/
def Profile.ofRegistrationAt
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    (registration :
      Registration.{uResidual, uAmbient, uMember, uLabel}
        Residual AmbientItem)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece}
        Previous Residual (fun previous => AmbientItem (current.read previous)))
    (accounting : Query Previous fun _ =>
      ULift.{uBoundary} BoundaryDemandAccounting.Summary) :
    Profile.{uPrevious, uResidual, uBoundary, uMember, uLabel}
      Previous Residual where
  BoundaryAccounting := fun _ =>
    ULift.{uBoundary} BoundaryDemandAccounting.Summary
  boundaryAccounting := accounting
  accountingSummary := fun _ summary => summary.down
  interpretation :=
    { Member := fun previous _ =>
        registration.Member (current.read previous)
      Label := fun previous _ =>
        registration.Label (current.read previous)
      members := fun previous _ =>
        registration.members (current.read previous)
          (normalizedSupport.complement.read previous)
      requiredMass := fun previous _ =>
        registration.requiredMass (current.read previous)
          (normalizedSupport.complement.read previous)
      observedSupply := fun previous _ =>
        registration.observedSupply (current.read previous)
          (normalizedSupport.complement.read previous)
      defectCorrection := fun previous _ member =>
        registration.defectCorrection (current.read previous)
          (normalizedSupport.complement.read previous) member
      surplus := fun previous _ member =>
        registration.surplus (current.read previous)
          (normalizedSupport.complement.read previous) member
      label := fun previous _ =>
        registration.label (current.read previous)
          (normalizedSupport.complement.read previous)
      labelDecidableEq := fun previous _ =>
        registration.labelDecidableEq (current.read previous)
      pointwise := fun previous _ member =>
        registration.pointwise (current.read previous)
          (normalizedSupport.complement.read previous) member }

/-- Stable-residual specialization of the query-native constructor. -/
def Profile.ofRegistration
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    (registration :
      Registration.{uResidual, uAmbient, uMember, uLabel}
        Residual AmbientItem)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece}
        Previous Residual (fun previous => AmbientItem (residualOf previous)))
    (accounting : Query Previous fun _ =>
      ULift.{uBoundary} BoundaryDemandAccounting.Summary) :
    Profile.{uPrevious, uResidual, uBoundary, uMember, uLabel}
      Previous Residual :=
  Profile.ofRegistrationAt registration Query.residual normalizedSupport
    accounting

end Hypostructure.Core.Strategy.LocalSupplyLowerBound
