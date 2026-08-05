import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Core.Strategy.ObstructionPackingData

/-!
# Generic cold-corridor first-failure scan

This module owns the stage-major finite scan used by cold branches.  A domain
supplies only residual-owned schedules, observations, and their proofs of
decidability/coverage.  Core performs the ordered first-hit searches and
returns the first typed failure; no branch result or route is selected by an
application executor.
-/

namespace Hypostructure.Core.Finite.ColdCorridor

open Hypostructure.Core.Finite
open Hypostructure.Core.Finite.ScheduleEvents
open Hypostructure.Core.Residual

universe uPrevious uOwner uItem uState uOutput uInterface uVertex

inductive Failure where
  | f1
  | f2
  | f3
  | f4
  | f5
  deriving DecidableEq, Repr

structure Contract (Item : Type uItem) where
  schedule : Enumeration Item
  Output : Item → Type uOutput
  run : (item : Item) → Output item
  f1 : (item : Item) → Output item → Prop
  f2 : (item : Item) → Output item → Prop
  f3 : (item : Item) → Output item → Prop
  f4 : (item : Item) → Output item → Prop
  f5 : (item : Item) → Output item → Prop
  f1_decidable : ∀ item, Decidable (f1 item (run item))
  f2_decidable : ∀ item, Decidable (f2 item (run item))
  f3_decidable : ∀ item, Decidable (f3 item (run item))
  f4_decidable : ∀ item, Decidable (f4 item (run item))
  exhaustive : ∀ item ∈ schedule.values,
    f1 item (run item) ∨ f2 item (run item) ∨
      f3 item (run item) ∨ f4 item (run item) ∨ f5 item (run item)

/-! A finite event family is a residual-owned schedule of candidate witnesses.
The application presents the candidates and their semantic validity predicate;
Core performs the ordered search and exposes only the resulting hit and its
canonical witness.  In particular, no caller supplies an F1--F4 boolean or
selects a witness by hand. -/
structure EventFamily (Item : Type uItem) (Output : Item → Type uOutput)
    (Candidate : Item → Type uInterface) where
  schedule : (item : Item) → Enumeration (Candidate item)
  valid : (item : Item) → Candidate item → Output item → Prop
  valid_decidable : ∀ item candidate output,
    Decidable (valid item candidate output)

namespace EventFamily

variable {Item : Type uItem} {Output : Item → Type uOutput}
  {Candidate : Item → Type uInterface}

noncomputable def execution (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) :
    Search.Execution (family.schedule item)
      (fun candidate => family.valid item candidate output) :=
  Search.run (family.schedule item)
    (fun candidate => family.valid item candidate output)
    (fun candidate => family.valid_decidable item candidate output)

def hit (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) : Prop :=
  (family.execution item output).HasHit

noncomputable instance hitDecidable (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) : Decidable (family.hit item output) :=
  by
    unfold hit
    infer_instance

noncomputable def witness (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) (hit : family.hit item output) :
    Candidate item :=
  (family.execution item output).hitOfHasHit hit |>.value

theorem witness_mem (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) (hit : family.hit item output) :
    family.witness item output hit ∈ (family.schedule item).values := by
  exact (family.execution item output).hitOfHasHit hit |>.member

theorem witness_valid (family : EventFamily Item Output Candidate)
    (item : Item) (output : Output item) (hit : family.hit item output) :
    family.valid item (family.witness item output hit) output := by
  exact (family.execution item output).hitOfHasHit hit |>.sound

end EventFamily

/-! Four ordered event families are the generic public presentation for a cold
corridor.  Their predicates are evaluated by Core's finite searches; F5 is
then the complement supplied by `Contract.ofObservation`. -/
structure FourEventObservation (Item : Type uItem) where
  Output : Item → Type uOutput
  run : (item : Item) → Output item
  F1Candidate : Item → Type uInterface
  F2Candidate : Item → Type uInterface
  F3Candidate : Item → Type uInterface
  F4Candidate : Item → Type uInterface
  f1 : EventFamily Item Output F1Candidate
  f2 : EventFamily Item Output F2Candidate
  f3 : EventFamily Item Output F3Candidate
  f4 : EventFamily Item Output F4Candidate

namespace FourEventObservation

variable {Item : Type uItem} (observation : FourEventObservation Item)

def f1Hit (item : Item) (output : observation.Output item) : Prop :=
  observation.f1.hit item output

def f2Hit (item : Item) (output : observation.Output item) : Prop :=
  observation.f2.hit item output

def f3Hit (item : Item) (output : observation.Output item) : Prop :=
  observation.f3.hit item output

def f4Hit (item : Item) (output : observation.Output item) : Prop :=
  observation.f4.hit item output

noncomputable instance f1HitDecidable (item : Item) (output : observation.Output item) :
    Decidable (observation.f1Hit item output) :=
  by
    unfold f1Hit
    infer_instance

noncomputable instance f2HitDecidable (item : Item) (output : observation.Output item) :
    Decidable (observation.f2Hit item output) :=
  by
    unfold f2Hit
    infer_instance

noncomputable instance f3HitDecidable (item : Item) (output : observation.Output item) :
    Decidable (observation.f3Hit item output) :=
  by
    unfold f3Hit
    infer_instance

noncomputable instance f4HitDecidable (item : Item) (output : observation.Output item) :
    Decidable (observation.f4Hit item output) :=
  by
    unfold f4Hit
    infer_instance

end FourEventObservation

/-! F5 is not an independent application datum.  Once the stage-major scan
has four genuine event predicates, Core defines the final branch as their
conjunction of failures and derives both its decidability and exhaustiveness.
This constructor is the only public way to build a corridor contract from
the four semantic observations. -/
noncomputable def Contract.ofFirstFour
    (schedule : Enumeration Item)
    (Output : Item → Type uOutput)
    (run : (item : Item) → Output item)
    (f1 f2 f3 f4 : (item : Item) → Output item → Prop)
    (f1_decidable : ∀ item, Decidable (f1 item (run item)))
    (f2_decidable : ∀ item, Decidable (f2 item (run item)))
    (f3_decidable : ∀ item, Decidable (f3 item (run item)))
    (f4_decidable : ∀ item, Decidable (f4 item (run item))) :
    Contract Item where
  schedule := schedule
  Output := Output
  run := run
  f1 := f1
  f2 := f2
  f3 := f3
  f4 := f4
  f5 := fun item output =>
    ¬ f1 item output ∧ ¬ f2 item output ∧
      ¬ f3 item output ∧ ¬ f4 item output
  f1_decidable := f1_decidable
  f2_decidable := f2_decidable
  f3_decidable := f3_decidable
  f4_decidable := f4_decidable
  exhaustive := by
    intro item _member
    classical
    by_cases h1 : f1 item (run item)
    · exact Or.inl h1
    by_cases h2 : f2 item (run item)
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f3 item (run item)
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : f4 item (run item)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)))

/-! Construct the corridor contract directly from the four residual-owned
candidate families.  This is the generic bridge used by graph adapters: the
only semantic input is each family’s candidate schedule and validity test;
Core executes all four searches and derives the F5 complement. -/
noncomputable def Contract.ofObservation
    (schedule : Enumeration Item)
    (observation : FourEventObservation Item) :
    Contract Item :=
  Contract.ofFirstFour
    schedule observation.Output observation.run
    observation.f1Hit observation.f2Hit observation.f3Hit observation.f4Hit
    (fun item => FourEventObservation.f1HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f2HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f3HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f4HitDecidable observation item
      (observation.run item))

@[simp] theorem Contract.ofFirstFour_f5
    (schedule : Enumeration Item)
    (Output : Item → Type uOutput)
    (run : (item : Item) → Output item)
    (f1 f2 f3 f4 : (item : Item) → Output item → Prop)
    (f1_decidable : ∀ item, Decidable (f1 item (run item)))
    (f2_decidable : ∀ item, Decidable (f2 item (run item)))
    (f3_decidable : ∀ item, Decidable (f3 item (run item)))
    (f4_decidable : ∀ item, Decidable (f4 item (run item)))
    (item : Item) (output : Output item) :
    (Contract.ofFirstFour schedule Output run f1 f2 f3 f4
      f1_decidable f2_decidable f3_decidable f4_decidable).f5 item output ↔
      (¬ f1 item output ∧ ¬ f2 item output ∧
        ¬ f3 item output ∧ ¬ f4 item output) := Iff.rfl

namespace Contract

variable {Item : Type uItem} (contract : Contract Item)

/-! The bound layer is deliberately independent of graph semantics.  A graph
domain supplies a finite state type and proves its cardinality bound; Core
then derives the corridor constants used by the finite scan. -/
structure StateBounds (State : Type uOutput) [Fintype State] where
  interfaceBudget : Nat
  /-- A domain-proved multiplicity bound for one bounded support.  Core
  consumes this certificate but does not invent a numerical constant. -/
  overlapBudget : Nat

namespace StateBounds

variable {State : Type uOutput} [Fintype State]

def stateCount : Nat := Fintype.card State

def stateBound (_bounds : StateBounds State) : Nat :=
  stateCount (State := State)

def supportBound (bounds : StateBounds State) : Nat :=
  stateCount (State := State) + bounds.interfaceBudget

def exactSupportBound (bounds : StateBounds State) : Nat :=
  supportBound bounds

def overlapBound (bounds : StateBounds State) : Nat :=
  bounds.overlapBudget

def exactOverlapBound (bounds : StateBounds State) : Nat :=
  bounds.overlapBudget

def extractionDenominator (bounds : StateBounds State) : Nat :=
  supportBound bounds * overlapBound bounds + 1

def exactExtractionDenominator (bounds : StateBounds State) : Nat :=
  exactSupportBound bounds * exactOverlapBound bounds + 1

/-! A finite interface type supplies the budget itself.  This constructor is
the generic route for domains whose interface is represented by an actual
finite type; no numeric budget is copied into a registration. -/
def fromFiniteInterface (Interface : Type uState) [Fintype Interface]
    (overlapBudget : Nat) :
    Contract.StateBounds State :=
  { interfaceBudget := Fintype.card Interface
    overlapBudget }

@[simp] theorem fromFiniteInterface_budget
    (Interface : Type uState) [Fintype Interface] (overlapBudget : Nat) :
    (fromFiniteInterface (State := State) Interface overlapBudget).interfaceBudget =
      Fintype.card Interface := rfl

theorem supportBound_ge_stateBound (bounds : StateBounds State) :
    stateBound bounds ≤ supportBound bounds := by
  simp [stateBound, supportBound]

theorem supportBound_ge_interfaceBudget (bounds : StateBounds State) :
    bounds.interfaceBudget ≤ supportBound bounds := by
  simp [supportBound]

end StateBounds

/-! A state trace keeps the finite schedule and its state observation together.
The schedule remains residual-owned; Core derives the observed state list and
the pigeonhole witness without asking a caller to provide a repeated pair. -/
structure StateTrace (Item : Type uItem) (State : Type uState) [Fintype State] where
  schedule : Enumeration Item
  state : Item → State

namespace StateTrace

variable {Item : Type uItem} {State : Type uState} [Fintype State]

def states (trace : StateTrace Item State) : List State :=
  trace.schedule.values.map trace.state

theorem states_length (trace : StateTrace Item State) :
    (trace.states).length = trace.schedule.card := by
  simp [states, Enumeration.card]

theorem exists_repeated_of_longer
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    ∃ state : State, List.Duplicate state trace.states := by
  apply (List.exists_duplicate_iff_not_nodup).mpr
  intro nodup
  have lengthBound : trace.states.length ≤ Fintype.card State :=
    List.Nodup.length_le_card nodup
  have longer' : Fintype.card State < trace.states.length := by
    simpa [states_length trace] using longer
  exact (Nat.not_le.mpr longer') lengthBound

theorem exists_repeated_indices
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    ∃ (left right : Fin trace.schedule.card), left < right ∧
      trace.state (trace.schedule.get left) =
        trace.state (trace.schedule.get right) := by
  obtain ⟨state, duplicate⟩ := trace.exists_repeated_of_longer longer
  obtain ⟨left, right, ordered, leftEq, rightEq⟩ :=
    (List.duplicate_iff_exists_distinct_get.mp duplicate)
  have cardEq : trace.states.length = trace.schedule.card :=
    trace.states_length
  let left' : Fin trace.schedule.card :=
    ⟨left.1, by simpa [cardEq] using left.2⟩
  let right' : Fin trace.schedule.card :=
    ⟨right.1, by simpa [cardEq] using right.2⟩
  refine ⟨left', right', ?_, ?_⟩
  · exact ordered
  · have leftAt : trace.states.get left =
        trace.state (trace.schedule.get left') := by
      let mapped : Fin (trace.schedule.values.map trace.state).length :=
        ⟨left.val, by simpa [states, cardEq] using left.isLt⟩
      have indexEq : left = Fin.cast (by simp [states]) mapped := by
        apply Fin.ext
        rfl
      rw [indexEq]
      change (trace.schedule.values.map trace.state).get mapped = _
      simp [mapped, left', Enumeration.get]
    have rightAt : trace.states.get right =
        trace.state (trace.schedule.get right') := by
      let mapped : Fin (trace.schedule.values.map trace.state).length :=
        ⟨right.val, by simpa [states, cardEq] using right.isLt⟩
      have indexEq : right = Fin.cast (by simp [states]) mapped := by
        apply Fin.ext
        rfl
      rw [indexEq]
      change (trace.schedule.values.map trace.state).get mapped = _
      simp [mapped, right', Enumeration.get]
    exact leftAt.symm.trans (leftEq.symm.trans (rightEq.trans rightAt))

/-! The canonical first repeated-state search is built from Core's ordered
finite search.  Pair ordering is part of the schedule, so the first hit is a
deterministic corridor witness rather than an application-selected pair. -/
noncomputable def orderedPairSchedule
    (trace : StateTrace Item State) :
    Enumeration {pair : Fin trace.schedule.card × Fin trace.schedule.card //
      pair.1 < pair.2} := by
  let indices : Enumeration (Fin trace.schedule.card) :=
    Enumeration.ofFinEnum (inferInstance : FinEnum (Fin trace.schedule.card))
  exact (indices.product indices).subtype
    (fun pair => pair.1 < pair.2)
    (fun _ => Classical.propDecidable _)

noncomputable def repeatedSearch
    (trace : StateTrace Item State) :
    Search.Execution (orderedPairSchedule trace)
      (fun pair =>
        trace.state (trace.schedule.get pair.1.1) =
          trace.state (trace.schedule.get pair.1.2)) :=
  Search.run (orderedPairSchedule trace)
    (fun pair =>
      trace.state (trace.schedule.get pair.1.1) =
        trace.state (trace.schedule.get pair.1.2))
    (fun _ => Classical.propDecidable _)

theorem repeatedSearch_hasHit
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    (trace.repeatedSearch).HasHit := by
  obtain ⟨left, right, ordered, equal⟩ :=
    trace.exists_repeated_indices longer
  let pair : {pair : Fin trace.schedule.card × Fin trace.schedule.card //
      pair.1 < pair.2} := ⟨(left, right), ordered⟩
  have pair_mem : pair ∈ (orderedPairSchedule trace).values := by
    change pair ∈
      (((Enumeration.ofFinEnum (inferInstance : FinEnum (Fin trace.schedule.card))).product
        (Enumeration.ofFinEnum (inferInstance : FinEnum (Fin trace.schedule.card)))).subtype
        (fun pair => pair.1 < pair.2) (fun _ => Classical.propDecidable _)
        |>.values)
    rw [Enumeration.mem_subtype_values]
    exact (Enumeration.mem_product_values
      (Enumeration.ofFinEnum (inferInstance : FinEnum (Fin trace.schedule.card)))
      (Enumeration.ofFinEnum (inferInstance : FinEnum (Fin trace.schedule.card)))
      (left, right)).mpr ⟨
        Enumeration.mem_ofFinEnum_values _ left,
        Enumeration.mem_ofFinEnum_values _ right⟩
  have pair_holds :
      trace.state (trace.schedule.get pair.1.1) =
        trace.state (trace.schedule.get pair.1.2) := equal
  rcases (trace.repeatedSearch).hit_or_avoids with hit | avoids
  · exact hit
  · obtain ⟨index, index_eq⟩ :=
      (orderedPairSchedule trace).mem_iff_exists_index pair |>.mp pair_mem
    have atIndex :
        trace.state (trace.schedule.get ((orderedPairSchedule trace).get index).1.1) =
          trace.state (trace.schedule.get ((orderedPairSchedule trace).get index).1.2) := by
      rw [index_eq]
      exact pair_holds
    exact False.elim (avoids index atIndex)

noncomputable def repeatedWitness
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    {pair : Fin trace.schedule.card × Fin trace.schedule.card //
      pair.1 < pair.2} :=
  ((trace.repeatedSearch).hitOfHasHit
    (trace.repeatedSearch_hasHit longer)).value

theorem repeatedWitness_order
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    (trace.repeatedWitness longer).1.1 <
      (trace.repeatedWitness longer).1.2 :=
  (trace.repeatedWitness longer).property

theorem repeatedWitness_equal
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    trace.state (trace.schedule.get (trace.repeatedWitness longer).1.1) =
      trace.state (trace.schedule.get (trace.repeatedWitness longer).1.2) := by
  exact (trace.repeatedSearch).hitOfHasHit
    (trace.repeatedSearch_hasHit longer) |>.sound

/-! The bounded prefix used by the corridor pigeonhole step is constructed
from the literal trace.  Its schedule is the first `count` entries in the
original order; no prefix or repeated pair is supplied by a caller. -/
noncomputable def initialTrace (trace : StateTrace Item State) (count : Nat) :
    StateTrace Item State := by
  letI : DecidableEq Item := trace.schedule.decEq
  exact
    { schedule := Enumeration.ofNodupList
        (trace.schedule.values.take count) trace.schedule.nodup.take
      state := trace.state }

@[simp] theorem initialTrace_schedule_values
    (trace : StateTrace Item State) (count : Nat) :
    (trace.initialTrace count).schedule.values =
      trace.schedule.values.take count := rfl

theorem initialTrace_card_eq
    (trace : StateTrace Item State) (count : Nat)
    (count_le : count ≤ trace.schedule.card) :
    (trace.initialTrace count).schedule.card = count := by
  change (trace.schedule.values.take count).length = count
  rw [List.length_take]
  exact Nat.min_eq_left count_le

/-- Canonical repeated-state witness inside the first `Q + 1` entries, where
`Q` is the exact finite state count. -/
structure BoundedRepeat (trace : StateTrace Item State) where
  prefixTrace : StateTrace Item State
  prefix_values : prefixTrace.schedule.values =
    trace.schedule.values.take (Fintype.card State + 1)
  state_eq : prefixTrace.state = trace.state
  prefix_card : prefixTrace.schedule.card = Fintype.card State + 1
  pair : Fin prefixTrace.schedule.card × Fin prefixTrace.schedule.card
  ordered : pair.1 < pair.2
  equal : prefixTrace.state (prefixTrace.schedule.get pair.1) =
    prefixTrace.state (prefixTrace.schedule.get pair.2)

namespace BoundedRepeat

variable {trace : StateTrace Item State}

/-- The stored bounded prefix is literally a prefix of the incoming trace. -/
theorem prefix_card_le (repeated : BoundedRepeat trace) :
    repeated.prefixTrace.schedule.card ≤ trace.schedule.card := by
  change repeated.prefixTrace.schedule.values.length ≤
    trace.schedule.values.length
  rw [repeated.prefix_values]
  simp [List.length_take]

/-- Reindex a bounded-prefix coordinate into the exact incoming schedule. -/
def originalIndex (repeated : BoundedRepeat trace)
    (index : Fin repeated.prefixTrace.schedule.card) :
    Fin trace.schedule.card :=
  ⟨index.1, index.2.trans_le repeated.prefix_card_le⟩

/-- Reading a bounded-prefix coordinate reads the same item from the incoming
schedule. -/
theorem prefix_get_eq_original_get (repeated : BoundedRepeat trace)
    (index : Fin repeated.prefixTrace.schedule.card) :
    repeated.prefixTrace.schedule.get index =
      trace.schedule.get (repeated.originalIndex index) := by
  have prefix_lt : index.1 < repeated.prefixTrace.schedule.values.length :=
    index.2
  have original_lt : index.1 < trace.schedule.values.length :=
    index.2.trans_le repeated.prefix_card_le
  have prefix_index_lt : index.1 < Fintype.card State + 1 := by
    have inTake : index.1 <
        (trace.schedule.values.take (Fintype.card State + 1)).length := by
      simpa [repeated.prefix_values] using prefix_lt
    exact inTake.trans_le (List.length_take_le _ _)
  have atIndex := congrArg
    (fun values : List Item => values[index.1]?) repeated.prefix_values
  rw [List.getElem?_eq_getElem prefix_lt,
    List.getElem?_take_of_lt prefix_index_lt,
    List.getElem?_eq_getElem original_lt] at atIndex
  exact Option.some.inj atIndex

/-- The equal-state witness is equality in the incoming trace's state
observation, not merely in a detached prefix copy. -/
theorem original_state_equal (repeated : BoundedRepeat trace) :
    trace.state (trace.schedule.get (repeated.originalIndex repeated.pair.1)) =
      trace.state (trace.schedule.get
        (repeated.originalIndex repeated.pair.2)) := by
  rw [← repeated.prefix_get_eq_original_get repeated.pair.1,
    ← repeated.prefix_get_eq_original_get repeated.pair.2,
    ← repeated.state_eq]
  exact repeated.equal

end BoundedRepeat

noncomputable def boundedRepeat
    (trace : StateTrace Item State)
    (longer : Fintype.card State < trace.schedule.card) :
    BoundedRepeat trace := by
  let prefixTrace := trace.initialTrace (Fintype.card State + 1)
  have count_le : Fintype.card State + 1 ≤ trace.schedule.card := by omega
  have prefix_card : prefixTrace.schedule.card = Fintype.card State + 1 :=
    trace.initialTrace_card_eq (Fintype.card State + 1) count_le
  have prefix_longer : Fintype.card State < prefixTrace.schedule.card := by
    omega
  let witness := prefixTrace.repeatedWitness prefix_longer
  exact
    { prefixTrace := prefixTrace
      prefix_values := rfl
      state_eq := rfl
      prefix_card := prefix_card
      pair := witness.1
      ordered := witness.property
      equal := prefixTrace.repeatedWitness_equal prefix_longer }

/-- Exhaustive bounded-trace alternative used by F5.  The terminal branch is
already at most the finite state count; otherwise Core constructs the
canonical repeated pair inside a prefix of exactly `Q + 1` entries. -/
inductive BoundedOutcome (trace : StateTrace Item State) where
  | terminal (bounded : trace.schedule.card ≤ Fintype.card State)
  | repeated (witness : BoundedRepeat trace)

/-- Proposition-level view of the terminal branch of an exact stored bounded
outcome.  This is a ledger filter only; it does not recompute the bounded
alternative. -/
def BoundedOutcome.IsTerminal
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) : Prop :=
  match outcome with
  | .terminal _ => True
  | .repeated _ => False

noncomputable instance BoundedOutcome.isTerminalDecidable
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) :
    Decidable outcome.IsTerminal :=
  Classical.propDecidable _

/-- Recover the bound carried by the selected terminal branch of the exact
stored outcome. -/
def BoundedOutcome.terminalBoundOf
    {trace : StateTrace Item State}
    (outcome : BoundedOutcome trace) (selected : outcome.IsTerminal) :
    trace.schedule.card ≤ Fintype.card State := by
  cases outcome with
  | terminal bounded => exact bounded
  | repeated witness => exact False.elim selected

/-- Proposition-level view of the repeated-state branch of a bounded
outcome.  It is used by residual queries to filter the exact outcome already
stored in the ledger; it does not rerun the repeated-state search. -/
def BoundedOutcome.IsRepeated
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) : Prop :=
  match outcome with
  | .terminal _ => False
  | .repeated _ => True

noncomputable instance BoundedOutcome.isRepeatedDecidable
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) :
    Decidable outcome.IsRepeated :=
  Classical.propDecidable _

/-- Recover the repeated-state witness from the selected branch of the exact
stored bounded outcome. -/
def BoundedOutcome.repeatedWitnessOf
    {trace : StateTrace Item State}
    (outcome : BoundedOutcome trace) (selected : outcome.IsRepeated) :
    BoundedRepeat trace := by
  cases outcome with
  | terminal bounded => exact False.elim selected
  | repeated witness => exact witness

/-- The two stored bounded-outcome views are exhaustive. -/
theorem BoundedOutcome.isTerminal_or_isRepeated
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) :
    outcome.IsTerminal ∨ outcome.IsRepeated := by
  cases outcome with
  | terminal _ => exact Or.inl trivial
  | repeated _ => exact Or.inr trivial

/-- The terminal and repeated views of one stored outcome are disjoint. -/
theorem BoundedOutcome.not_terminal_and_repeated
    {trace : StateTrace Item State} (outcome : BoundedOutcome trace) :
    ¬ (outcome.IsTerminal ∧ outcome.IsRepeated) := by
  cases outcome <;> simp [BoundedOutcome.IsTerminal, BoundedOutcome.IsRepeated]

noncomputable def boundedOutcome (trace : StateTrace Item State) :
    BoundedOutcome trace := by
  by_cases bounded : trace.schedule.card ≤ Fintype.card State
  · exact .terminal bounded
  · exact .repeated (trace.boundedRepeat (Nat.lt_of_not_ge bounded))

end StateTrace

/-! A complete trace is the non-application-owned variant of `StateTrace`.
When the item family is genuinely finite, its schedule is obtained from the
`FinEnum` instance.  This is useful at graph registration boundaries: the
caller supplies only the residual-owned state observation, never an ordered
list of items. -/
structure CompleteStateTrace (Item : Type uItem) (State : Type uState)
    [FinEnum Item] [Fintype State] where
  state : Item → State

namespace CompleteStateTrace

variable {Item : Type uItem} {State : Type uState}
  [FinEnum Item] [Fintype State]

def toStateTrace (trace : CompleteStateTrace Item State) :
    StateTrace Item State where
  schedule := Enumeration.ofFinEnum (inferInstance : FinEnum Item)
  state := trace.state

@[simp] theorem schedule_values
    (trace : CompleteStateTrace Item State) :
    (trace.toStateTrace.schedule).values = @FinEnum.toList Item inferInstance := rfl

end CompleteStateTrace

end Contract

/-! Exact finite overlap accounting.  Given the literal schedule of candidate
supports, Core computes the maximum number of scheduled supports containing a
vertex.  This is the bounded-overlap constant used by greedy extraction; no
problem-specific multiplier is embedded in the framework. -/
noncomputable def overlapCount {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex)
    (vertex : Vertex) : Nat := by
  classical
  exact (schedule.toFinset.filter (fun item => vertex ∈ support item)).card

noncomputable def overlapBound {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) : Nat :=
  vertices.toFinset.sup (fun vertex => overlapCount schedule support vertex)

theorem overlapCount_le_bound {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) (vertex : Vertex)
    (vertex_mem : vertex ∈ vertices.values) :
    overlapCount schedule support vertex ≤ overlapBound schedule vertices support := by
  classical
  unfold overlapBound
  exact Finset.le_sup
    (s := vertices.toFinset)
    (f := fun vertex => overlapCount schedule support vertex)
    ((Enumeration.mem_toFinset vertices vertex).mpr vertex_mem)

/-! Exact support size accounting over the same literal schedule. -/
noncomputable def supportSizeBound {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex) : Nat :=
  schedule.toFinset.sup fun item => (support item).card

theorem support_card_le_supportSizeBound
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex)
    {item : Item} (member : item ∈ schedule.values) :
    (support item).card ≤ supportSizeBound schedule support := by
  classical
  unfold supportSizeBound
  exact Finset.le_sup
    (s := schedule.toFinset)
    (f := fun item => (support item).card)
    ((Enumeration.mem_toFinset schedule item).mpr member)

/-- Two scheduled supports conflict exactly when they share a vertex. -/
def SupportConflict {Item : Type uItem} {Vertex : Type uState}
    (support : Item → Finset Vertex) (left right : Item) : Prop :=
  ¬ Disjoint (support left) (support right)

theorem supportConflict_symmetric
    {Item : Type uItem} {Vertex : Type uState}
    (support : Item → Finset Vertex) :
    Symmetric (SupportConflict support) := by
  intro left right conflict disjoint
  exact conflict disjoint.symm

/-- The canonical disjoint-support packing computed from a literal schedule. -/
noncomputable def supportPacking
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex) :
    Core.Strategy.ObstructionPackingClosure.Packing schedule
      (SupportConflict support) :=
  Core.Strategy.ObstructionPackingClosure.Packing.canonical
    schedule (SupportConflict support) (Classical.decRel _)
    (supportConflict_symmetric support)

noncomputable def conflictNeighborhood
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex)
    (selectedItem : Item) : Finset Item := by
  classical
  exact schedule.toFinset.filter fun item =>
    SupportConflict support item selectedItem

theorem supportPacking_pairwise_disjoint
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex)
    {left right : Item}
    (left_mem : left ∈ (supportPacking schedule support).selected)
    (right_mem : right ∈ (supportPacking schedule support).selected)
    (different : left ≠ right) :
    Disjoint (support left) (support right) := by
  exact not_not.mp
    ((supportPacking schedule support).pairwiseCompatible
      left_mem right_mem different)

/-! Exact finite support accounting bounds the conflict neighbourhood of every
selected occurrence.  The proof is the union bound over the selected
support's literal vertices; both factors are computed from schedules. -/
theorem supportConflict_neighborhood_card_le
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex)
    (support_vertices : ∀ item ∈ schedule.values,
      support item ⊆ vertices.toFinset)
    (selectedItem : Item)
    (selected_mem :
      selectedItem ∈ (supportPacking schedule support).selected) :
    (conflictNeighborhood schedule support selectedItem).card ≤
      supportSizeBound schedule support *
        overlapBound schedule vertices support := by
  classical
  let itemsAt := fun vertex =>
    schedule.toFinset.filter fun item => vertex ∈ support item
  have selected_schedule : selectedItem ∈ schedule.values :=
    (supportPacking schedule support).selected_mem_schedule selected_mem
  have covered :
      conflictNeighborhood schedule support selectedItem ⊆
        (support selectedItem).biUnion itemsAt := by
    intro item item_mem
    change item ∈ schedule.toFinset.filter
      (fun item => SupportConflict support item selectedItem) at item_mem
    rcases Finset.mem_filter.mp item_mem with ⟨item_schedule, conflict⟩
    change ¬ Disjoint (support item) (support selectedItem) at conflict
    rw [Finset.not_disjoint_iff] at conflict
    rcases conflict with ⟨vertex, item_support, selected_support⟩
    exact Finset.mem_biUnion.mpr
      ⟨vertex, selected_support,
        Finset.mem_filter.mpr ⟨item_schedule, item_support⟩⟩
  have each_vertex : ∀ vertex ∈ support selectedItem,
      (itemsAt vertex).card ≤ overlapBound schedule vertices support := by
    intro vertex vertex_mem
    have vertex_mem_all : vertex ∈ vertices.values := by
      apply (Enumeration.mem_toFinset vertices vertex).mp
      exact support_vertices selectedItem selected_schedule vertex_mem
    simpa [itemsAt, overlapCount] using
      overlapCount_le_bound schedule vertices support vertex vertex_mem_all
  calc
    (conflictNeighborhood schedule support selectedItem).card ≤
        ((support selectedItem).biUnion itemsAt).card :=
      Finset.card_le_card covered
    _ ≤ ∑ vertex ∈ support selectedItem, (itemsAt vertex).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _vertex ∈ support selectedItem,
        overlapBound schedule vertices support := by
      exact Finset.sum_le_sum fun vertex vertex_mem =>
        each_vertex vertex vertex_mem
    _ = (support selectedItem).card *
        overlapBound schedule vertices support := by simp
    _ ≤ supportSizeBound schedule support *
        overlapBound schedule vertices support := by
      exact Nat.mul_le_mul_right _
        (support_card_le_supportSizeBound schedule support selected_schedule)

theorem supportPacking_card_bound
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex)
    (support_vertices : ∀ item ∈ schedule.values,
      support item ⊆ vertices.toFinset) :
    schedule.card ≤ (supportPacking schedule support).selected.length *
      (supportSizeBound schedule support *
        overlapBound schedule vertices support + 1) := by
  classical
  apply Core.Strategy.ObstructionPackingClosure.Packing.schedule_card_le_selected_mul
    (supportPacking schedule support)
    (supportSizeBound schedule support * overlapBound schedule vertices support)
    (Classical.decRel _)
  intro selectedItem selected_mem
  simpa [conflictNeighborhood] using
    supportConflict_neighborhood_card_le schedule vertices support
      support_vertices selectedItem selected_mem

theorem supportPacking_selected_nonempty
    {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (support : Item → Finset Vertex)
    (schedule_nonempty : schedule.values ≠ []) :
    (supportPacking schedule support).selected ≠ [] := by
  intro selected_empty
  obtain ⟨item, item_mem⟩ :=
    List.exists_mem_of_ne_nil schedule.values schedule_nonempty
  obtain ⟨selectedItem, selected_mem, _conflict_or_equal⟩ :=
    (supportPacking schedule support).maximal item item_mem
  simp [selected_empty] at selected_mem

/-! Derive the overlap and extraction budgets from the literal finite support
schedule.  A domain producer supplies only its finite interface type,
vertex enumeration, and support observation; Core computes both numerical
budgets and therefore no registration can inject `B_cold` or `D_cold`. -/
noncomputable def Contract.StateBounds.fromFiniteInterfaceAndSupport
    {State : Type uOutput} [Fintype State]
    (Interface : Type uInterface) [Fintype Interface]
    {Item : Type uItem} {Vertex : Type uVertex}
    (schedule : Enumeration Item)
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) :
    StateBounds State :=
  { interfaceBudget := Fintype.card Interface
    overlapBudget :=
      _root_.Hypostructure.Core.Finite.ColdCorridor.overlapBound
        schedule vertices support }

@[simp] theorem Contract.StateBounds.fromFiniteInterfaceAndSupport_interfaceBudget
    {State : Type uOutput} [Fintype State]
    (Interface : Type uInterface) [Fintype Interface]
    {Item : Type uItem} {Vertex : Type uVertex}
    (schedule : Enumeration Item)
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) :
    (Contract.StateBounds.fromFiniteInterfaceAndSupport (State := State) Interface
      schedule vertices support).interfaceBudget = Fintype.card Interface := rfl

@[simp] theorem Contract.StateBounds.fromFiniteInterfaceAndSupport_overlapBudget
    {State : Type uOutput} [Fintype State]
    (Interface : Type uInterface) [Fintype Interface]
    {Item : Type uItem} {Vertex : Type uVertex}
    (schedule : Enumeration Item)
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) :
    (Contract.StateBounds.fromFiniteInterfaceAndSupport (State := State) Interface
      schedule vertices support).overlapBudget =
      _root_.Hypostructure.Core.Finite.ColdCorridor.overlapBound
        schedule vertices support := rfl

noncomputable def extractionDenominator {Item : Type uItem} {Vertex : Type uState}
    (schedule : Enumeration Item) (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) (supportBound : Nat) : Nat :=
  supportBound * overlapBound schedule vertices support + 1

namespace Contract

variable {Item : Type uItem} (contract : Contract Item)

def event (failure : Failure) : (item : Item) → contract.Output item → Prop
  | item, output => match failure with
    | .f1 => contract.f1 item output
    | .f2 => contract.f2 item output
    | .f3 => contract.f3 item output
    | .f4 => contract.f4 item output
    | .f5 => contract.f5 item output

noncomputable def eventDecidable (failure : Failure) (item : Item) :
    Decidable (contract.event failure item (contract.run item)) := by
  cases failure
  · exact contract.f1_decidable item
  · exact contract.f2_decidable item
  · exact contract.f3_decidable item
  · exact contract.f4_decidable item
  · classical exact Classical.propDecidable _

noncomputable def first? (failure : Failure) : Option Item :=
  ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
    (contract.event failure)
    (contract.eventDecidable failure)).hit?.map fun hit => hit.value

/-! The option returned by `first?` is not an untyped dispatch token: when it
contains an item, the item is accompanied by the exact schedule-membership
and event proofs stored by Core's first-hit execution.  This query is the
public bridge used by continuations that need the selected residual item. -/
theorem first?_sound
    {failure : Failure} {item : Item}
    (selected : contract.first? failure = some item) :
    item ∈ contract.schedule.values ∧
      contract.event failure item (contract.run item) := by
  unfold first? at selected
  let execution :=
    (ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
      (contract.event failure)
      (contract.eventDecidable failure)
  have valueSelected : execution.value? = some item := by
    simpa [execution, Search.Execution.value?] using selected
  exact Search.value_sound
    contract.schedule
    (fun item => contract.event failure item (contract.run item))
    (contract.eventDecidable failure) valueSelected

def priorFailure : Fin 4 → Failure
  | ⟨0, _⟩ => .f1
  | ⟨1, _⟩ => .f2
  | ⟨2, _⟩ => .f3
  | ⟨3, _⟩ => .f4

theorem priorFailure_ne_f5 (index : Fin 4) : priorFailure index ≠ .f5 := by
  fin_cases index <;> simp [priorFailure]

/-! The paper order is stage-major: for each corridor stage Core tests
F1, F2, F3, and F4 before advancing to the next stage.  This is one ordinary
Core search over the product of the residual-owned stage schedule and the
fixed four-event schedule. -/
noncomputable def priorFailureSchedule : Enumeration (Fin 4) :=
  Enumeration.ofFinEnum inferInstance

noncomputable def stageMajorSchedule : Enumeration (Item × Fin 4) :=
  contract.schedule.product priorFailureSchedule

noncomputable def stageMajorExecution :
    Search.Execution contract.stageMajorSchedule
      (fun pair => contract.event (priorFailure pair.2) pair.1
        (contract.run pair.1)) :=
  Search.run contract.stageMajorSchedule
    (fun pair => contract.event (priorFailure pair.2) pair.1
      (contract.run pair.1))
    (fun pair => contract.eventDecidable (priorFailure pair.2) pair.1)

noncomputable def classify : Failure :=
  match contract.stageMajorExecution.hit? with
  | some hit => priorFailure hit.value.2
  | none => .f5

/-! Restrict the literal corridor schedule to F5 entries.  This is the
Core-owned successor schedule; callers cannot replace it with a manufactured
list without changing the contract itself. -/
noncomputable def f5Schedule : Enumeration
    {item : Item // contract.f5 item (contract.run item)} :=
  contract.schedule.subtype
    (fun item => contract.f5 item (contract.run item))
    (fun _ => Classical.propDecidable _)

theorem mem_f5Schedule_values
    {item : Item} (member : item ∈ contract.schedule.values)
    (f5 : contract.f5 item (contract.run item)) :
    (⟨item, f5⟩ : {item : Item // contract.f5 item (contract.run item)}) ∈
      (f5Schedule contract).values := by
  simp [f5Schedule, member]

theorem f5Schedule_nonempty
    (existsF5 : ∃ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item)) :
    (f5Schedule contract).values ≠ [] := by
  rcases existsF5 with ⟨item, member, f5⟩
  intro empty
  have hmem := mem_f5Schedule_values contract member f5
  rw [empty] at hmem
  simp at hmem

theorem mem_f5Schedule_values_iff
    {item : {item : Item // contract.f5 item (contract.run item)}} :
    item ∈ (f5Schedule contract).values ↔
      item.1 ∈ contract.schedule.values := by
  exact Enumeration.mem_subtype_values
    contract.schedule
    (fun item => contract.f5 item (contract.run item))
    (fun _ => Classical.propDecidable _)
    item

theorem state_repeat_of_longer
    {State : Type uOutput} [Fintype State]
    (states : List State)
    (longer : Fintype.card State < states.length) :
    ¬ states.Nodup := by
  intro nodup
  exact (Nat.not_le.mpr longer) (List.Nodup.length_le_card nodup)

theorem exists_repeated_state
    {State : Type uOutput} [Fintype State]
    (states : List State)
    (longer : Fintype.card State < states.length) :
    ∃ state : State, List.Duplicate state states := by
  apply (List.exists_duplicate_iff_not_nodup).mpr
  exact state_repeat_of_longer states longer

theorem classify_sound :
    contract.event (classify contract) =
      contract.event (classify contract) := rfl

theorem f5_of_no_prior
    (no1 : first? contract .f1 = none)
    (no2 : first? contract .f2 = none)
    (no3 : first? contract .f3 = none)
    (no4 : first? contract .f4 = none) :
    ∀ item ∈ contract.schedule.values, contract.f5 item (contract.run item) := by
  intro item member
  have no1' :
      ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f1) (contract.eventDecidable .f1)).hit? = none := by
    simpa [first?] using no1
  have no2' :
      ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f2) (contract.eventDecidable .f2)).hit? = none := by
    simpa [first?] using no2
  have no3' :
      ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f3) (contract.eventDecidable .f3)).hit? = none := by
    simpa [first?] using no3
  have no4' :
      ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f4) (contract.eventDecidable .f4)).hit? = none := by
    simpa [first?] using no4
  rcases contract.exhaustive item member with h | h | h | h | h
  · exact False.elim (by
      have := ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f1) (contract.eventDecidable .f1)).exhaustive no1'
      rcases contract.schedule.mem_iff_exists_index item |>.mp member with
        ⟨index, rfl⟩
      exact this index h)
  · exact False.elim (by
      have := ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f2) (contract.eventDecidable .f2)).exhaustive no2'
      rcases contract.schedule.mem_iff_exists_index item |>.mp member with
        ⟨index, rfl⟩
      exact this index h)
  · exact False.elim (by
      have := ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f3) (contract.eventDecidable .f3)).exhaustive no3'
      rcases contract.schedule.mem_iff_exists_index item |>.mp member with
        ⟨index, rfl⟩
      exact this index h)
  · exact False.elim (by
      have := ((ScheduleEvents.Contract.mk contract.schedule contract.Output contract.run).firstHit
        (contract.event .f4) (contract.eventDecidable .f4)).exhaustive no4'
      rcases contract.schedule.mem_iff_exists_index item |>.mp member with
        ⟨index, rfl⟩
      exact this index h)
  · exact h

/-! Once the ordered scan has discharged F1--F4, a nonempty literal corridor
produces an actual F5 witness.  This is the typed handoff used by later
continuations; it does not manufacture an item or inspect a detached list. -/
theorem f5Witness_of_no_prior
    (no1 : first? contract .f1 = none)
    (no2 : first? contract .f2 = none)
    (no3 : first? contract .f3 = none)
    (no4 : first? contract .f4 = none)
    (schedule_nonempty : contract.schedule.values ≠ []) :
    ∃ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item) := by
  obtain ⟨item, item_mem⟩ :=
    List.exists_mem_of_ne_nil contract.schedule.values schedule_nonempty
  exact ⟨item, item_mem,
    contract.f5_of_no_prior no1 no2 no3 no4 item item_mem⟩

theorem all_f5_of_stageMajor_none
    (absent : contract.stageMajorExecution.hit? = none) :
    ∀ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item) := by
  have avoids := contract.stageMajorExecution.exhaustive absent
  intro item item_mem
  have noPrior : ∀ index : Fin 4,
      ¬ contract.event (priorFailure index) item (contract.run item) := by
    intro index holds
    have pair_mem : (item, index) ∈ contract.stageMajorSchedule.values := by
      exact (Enumeration.mem_product_values
        contract.schedule priorFailureSchedule (item, index)).mpr
          ⟨item_mem, Enumeration.mem_ofFinEnum_values inferInstance index⟩
    obtain ⟨pairIndex, pairEq⟩ :=
      (contract.stageMajorSchedule.mem_iff_exists_index (item, index)).mp pair_mem
    apply avoids pairIndex
    rw [pairEq]
    exact holds
  rcases contract.exhaustive item item_mem with h | h | h | h | h
  · exact (noPrior ⟨0, by omega⟩ h).elim
  · exact (noPrior ⟨1, by omega⟩ h).elim
  · exact (noPrior ⟨2, by omega⟩ h).elim
  · exact (noPrior ⟨3, by omega⟩ h).elim
  · exact h

theorem all_f5_of_classify_eq_f5
    (classified : contract.classify = .f5) :
    ∀ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item) := by
  cases found : contract.stageMajorExecution.hit? with
  | none => exact contract.all_f5_of_stageMajor_none found
  | some hit =>
      have notF5 := priorFailure_ne_f5 hit.value.2
      exact (notF5 (by simpa [classify, found] using classified)).elim

structure HitWitness where
  hit : Search.IndexedHit contract.stageMajorSchedule
    (fun pair => contract.event (priorFailure pair.2) pair.1
      (contract.run pair.1))

namespace HitWitness

noncomputable def item (witness : HitWitness contract) : Item :=
  witness.hit.value.1

noncomputable def failure (witness : HitWitness contract) : Failure :=
  priorFailure witness.hit.value.2

theorem notF5 (witness : HitWitness contract) : witness.failure ≠ .f5 :=
  priorFailure_ne_f5 witness.hit.value.2

theorem member (witness : HitWitness contract) :
    witness.item ∈ contract.schedule.values :=
  (Enumeration.mem_product_values
    contract.schedule priorFailureSchedule witness.hit.value).mp
      witness.hit.member |>.1

theorem sound (witness : HitWitness contract) :
    contract.event witness.failure witness.item (contract.run witness.item) :=
  witness.hit.sound

end HitWitness

inductive Classification where
  | hit : HitWitness contract → Classification
  | f5 : (∀ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item)) → Classification

/-- Proposition-level view of any stored terminal.  It inspects only the
selected classification and never re-evaluates an event predicate. -/
def Classification.IsFailure
    (classification : Classification contract) (failure : Failure) : Prop :=
  match classification with
  | .hit witness => witness.failure = failure
  | .f5 _ => failure = .f5

noncomputable instance Classification.isFailureDecidable
    (failure : Failure) (classification : Classification contract) :
    Decidable (Classification.IsFailure contract classification failure) :=
  Classical.propDecidable _

noncomputable def classification : Classification contract := by
  cases found : contract.stageMajorExecution.hit? with
  | some hit => exact .hit ⟨hit⟩
  | none => exact .f5 (contract.all_f5_of_stageMajor_none found)

/-- One typed event selected by the stage-major scan.  This is an elimination
view of `Classification`, not a second classifier: the scheduled item,
membership proof, and event proof are projections of the original indexed
hit. -/
structure EventWitness (failure : Failure) where
  item : Item
  member : item ∈ contract.schedule.values
  sound : contract.event failure item (contract.run item)

/-- Eliminate an already-recorded non-F5 classification into its exact event
witness.  This is a projection of the stored classification; it performs no
new predicate evaluation or schedule search. -/
noncomputable def Classification.failureEvent
    (classification : Classification contract)
    (failure : Failure) (notF5 : failure ≠ .f5)
    (selected : classification.IsFailure contract failure) :
    EventWitness contract failure := by
  cases classification with
  | hit witness =>
      change witness.failure = failure at selected
      cases selected
      exact ⟨witness.item, witness.member, witness.sound⟩
  | f5 all =>
      change failure = .f5 at selected
      exact (notF5 selected).elim

/-- Eliminate an already-recorded F5 classification into the universal F5
fact stored by that classification.  This is the F5 analogue of
`failureEvent`: it inspects no predicate and performs no new search. -/
theorem Classification.allF5
    (classification : Classification contract)
    (selected : classification.IsFailure contract .f5) :
    ∀ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item) := by
  cases classification with
  | hit witness =>
      change witness.failure = .f5 at selected
      exact ((HitWitness.notF5 contract witness) selected).elim
  | f5 all => exact all

/-- Exhaustive typed view of the existing F1--F5 classification.  Domain
adapters consume this view to interpret their own event predicates without
reopening Core's `Fin 4` implementation index. -/
inductive ClassifiedEvent where
  | f1 : EventWitness contract .f1 → ClassifiedEvent
  | f2 : EventWitness contract .f2 → ClassifiedEvent
  | f3 : EventWitness contract .f3 → ClassifiedEvent
  | f4 : EventWitness contract .f4 → ClassifiedEvent
  | f5 : (∀ item ∈ contract.schedule.values,
      contract.f5 item (contract.run item)) → ClassifiedEvent

/-- Eliminate the result of the one Core-owned search into its five semantic
cases.  No predicate is re-evaluated and no outcome can be supplied by a
registration. -/
noncomputable def Classification.toClassifiedEvent :
    Classification contract → ClassifiedEvent contract
  | .f5 all => .f5 all
  | .hit witness => by
      let item := witness.item
      have member := witness.member
      have sound := witness.sound
      let index := witness.hit.value.2
      change contract.event (priorFailure index) item (contract.run item) at sound
      match index with
      | ⟨0, _⟩ => exact .f1 ⟨item, member, sound⟩
      | ⟨1, _⟩ => exact .f2 ⟨item, member, sound⟩
      | ⟨2, _⟩ => exact .f3 ⟨item, member, sound⟩
      | ⟨3, _⟩ => exact .f4 ⟨item, member, sound⟩

end Contract

/-! A producer is the reusable Core boundary for a cold corridor.  Its
schedule and state space are derived from one trace; only graph/domain event
predicates remain at the registration boundary. -/
structure Producer (Item : Type uItem) (State : Type uState)
    [Fintype State] where
  trace : Contract.StateTrace Item State
  Output : Item → Type uOutput
  run : (item : Item) → Output item
  f1 : (item : Item) → Output item → Prop
  f2 : (item : Item) → Output item → Prop
  f3 : (item : Item) → Output item → Prop
  f4 : (item : Item) → Output item → Prop
  f5 : (item : Item) → Output item → Prop
  f1_decidable : ∀ item, Decidable (f1 item (run item))
  f2_decidable : ∀ item, Decidable (f2 item (run item))
  f3_decidable : ∀ item, Decidable (f3 item (run item))
  f4_decidable : ∀ item, Decidable (f4 item (run item))
  exhaustive : ∀ item ∈ trace.schedule.values,
    f1 item (run item) ∨ f2 item (run item) ∨
      f3 item (run item) ∨ f4 item (run item) ∨ f5 item (run item)

namespace Producer

variable {Item : Type uItem} {State : Type uState} [Fintype State]

/-! Producer constructor corresponding to `Contract.ofFirstFour`.  The
state trace, output runner, and four graph/domain observations are retained;
Core derives F5 and the exhaustive proof. -/
noncomputable def ofFirstFour
    (trace : Contract.StateTrace Item State)
    (Output : Item → Type uOutput)
    (run : (item : Item) → Output item)
    (f1 f2 f3 f4 : (item : Item) → Output item → Prop)
    (f1_decidable : ∀ item, Decidable (f1 item (run item)))
    (f2_decidable : ∀ item, Decidable (f2 item (run item)))
    (f3_decidable : ∀ item, Decidable (f3 item (run item)))
    (f4_decidable : ∀ item, Decidable (f4 item (run item))) :
    Producer Item State where
  trace := trace
  Output := Output
  run := run
  f1 := f1
  f2 := f2
  f3 := f3
  f4 := f4
  f5 := fun item output =>
    ¬ f1 item output ∧ ¬ f2 item output ∧
      ¬ f3 item output ∧ ¬ f4 item output
  f1_decidable := f1_decidable
  f2_decidable := f2_decidable
  f3_decidable := f3_decidable
  f4_decidable := f4_decidable
  exhaustive := by
    intro item member
    exact (Contract.ofFirstFour trace.schedule Output run f1 f2 f3 f4
      f1_decidable f2_decidable f3_decidable f4_decidable).exhaustive item member

/-! Producer bridge for the public four-family presentation. -/
noncomputable def ofObservation
    (trace : Contract.StateTrace Item State)
    (observation : FourEventObservation Item) :
    Producer Item State :=
  Producer.ofFirstFour
    trace observation.Output observation.run
    observation.f1Hit observation.f2Hit observation.f3Hit observation.f4Hit
    (fun item => FourEventObservation.f1HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f2HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f3HitDecidable observation item
      (observation.run item))
    (fun item => FourEventObservation.f4HitDecidable observation item
      (observation.run item))

def contract (producer : Producer Item State) : Contract Item where
  schedule := producer.trace.schedule
  Output := producer.Output
  run := producer.run
  f1 := producer.f1
  f2 := producer.f2
  f3 := producer.f3
  f4 := producer.f4
  f5 := producer.f5
  f1_decidable := producer.f1_decidable
  f2_decidable := producer.f2_decidable
  f3_decidable := producer.f3_decidable
  f4_decidable := producer.f4_decidable
  exhaustive := producer.exhaustive

/-! A classified producer result is an ordinary residual ledger extension.  The
extension stores only Core's dependent first-hit/F5 classification; it does
not store a copied event, route, terminal, or application outcome. -/
abbrev ClassificationStage (Previous : Type uPrevious) (producer : Producer Item State) :=
  Ledger.Extension Previous (fun _ => (contract producer).Classification)

noncomputable def classifyIntoLedger
    {Previous : Type uPrevious}
    (producer : Producer Item State) (previous : Previous) :
    ClassificationStage Previous producer :=
  Ledger.extend previous (Contract.classification (contract producer))

@[simp] theorem classifyIntoLedger_previous
    {Previous : Type uPrevious}
    (producer : Producer Item State) (previous : Previous) :
    (classifyIntoLedger producer previous).previous = previous := rfl

def classificationQuery
    {Previous : Type uPrevious}
    (producer : Producer Item State) :
    Query (ClassificationStage Previous producer)
      (fun stage => (contract producer).Classification) :=
  Query.latest

/-! ## Exact finite families of cold corridors

The pointwise producer above is the only owner of the F1--F5 search.  A cold
branch normally contains a finite residual-owned family of corridors, so the
following adapter merely evaluates that same producer at every member of the
literal owner schedule and appends the dependent results to the ordinary
ledger.  It introduces no second classifier, recursion, or routing table. -/

structure FamilyProducer (Owner : Type uOwner) where
  owners : Enumeration Owner
  Item : Owner → Type uItem
  State : Owner → Type uState
  stateFintype : (owner : Owner) → Fintype (State owner)
  producer : (owner : Owner) →
    @Producer.{uItem, uState, uOutput}
      (Item owner) (State owner) (stateFintype owner)

namespace FamilyProducer

variable {Owner : Type uOwner}
variable (family : FamilyProducer.{uOwner, uItem, uState, uOutput} Owner)

noncomputable def contractAt (owner : Owner) : Contract (family.Item owner) := by
  letI := family.stateFintype owner
  exact (family.producer owner).contract

/-- Project the state trace already owned by a scheduled producer. -/
noncomputable def traceAt (owner : Owner) :
    @Contract.StateTrace
      (family.Item owner) (family.State owner) (family.stateFintype owner) := by
  letI := family.stateFintype owner
  exact (family.producer owner).trace

@[simp] theorem contractAt_schedule (owner : Owner) :
    (family.contractAt owner).schedule =
      @Contract.StateTrace.schedule
        (family.Item owner) (family.State owner) (family.stateFintype owner)
        (family.traceAt owner) :=
  rfl

/-- Core's existing bounded-trace alternative for one scheduled owner. -/
noncomputable def boundedOutcomeAt (owner : Owner) :
    @Contract.StateTrace.BoundedOutcome
      (family.Item owner) (family.State owner) (family.stateFintype owner)
      (family.traceAt owner) := by
  letI := family.stateFintype owner
  exact (family.traceAt owner).boundedOutcome

/-- The exact dependent classification for every member of the registered
owner schedule.  Membership is retained in the index, so later queries cannot
classify an object that was not part of the incoming residual family. -/
structure Classification where
  classify : (owner : {owner : Owner // owner ∈ family.owners.values}) →
    (family.contractAt owner.1).Classification

/-- One scheduled owner whose stored pointwise classification selected the
given terminal. -/
abbrev FailureOwner (classification : family.Classification)
    (failure : Failure) :=
  {owner : {owner : Owner // owner ∈ family.owners.values} //
    Contract.Classification.IsFailure (family.contractAt owner.1)
      (classification.classify owner) failure}

/-- One scheduled owner whose stored pointwise classification selected F5. -/
abbrev F5Owner (classification : family.Classification) :=
  family.FailureOwner classification .f5

/-- Exact owner schedule for one terminal, filtered only from the stored
classification. -/
noncomputable def failureOwners (classification : family.Classification)
    (failure : Failure) : Enumeration (family.FailureOwner classification failure) :=
  family.owners.attach.subtype
    (fun owner => Contract.Classification.IsFailure
      (family.contractAt owner.1) (classification.classify owner) failure)
    (fun _ => Classical.propDecidable _)

/-- Exact surviving-owner schedule obtained solely by filtering the stored
family classification.  No corridor event is evaluated a second time. -/
noncomputable def f5Owners (classification : family.Classification) :
    Enumeration (family.F5Owner classification) :=
  family.owners.attach.subtype
    (fun owner => Contract.Classification.IsFailure
      (family.contractAt owner.1) (classification.classify owner) .f5)
    (fun _ => Classical.propDecidable _)

/-! ### Partition completeness and its branch-condition contradiction

The stored partitions are *filters* of the one owner schedule, so they are
complete: an owner of a partition always occurs in that partition's own
enumeration.  A branch that recorded a partition as empty therefore admits no
owner of it at all, and a leaf holding one is impossible on that branch.

This is the schedule-level counterpart of
`Core.Residual.Decision.Stage.absurd_of_exclusive`
(`Core/Residual/Decision.lean:53`): there the recorded branch is a binary
decision, here it is the recorded emptiness of a stored partition.  Both are
domain agnostic -- nothing below mentions graphs, corridors or PDEs. -/

/-- Stored failure partitions are complete: every owner of one occurs in its
own enumeration, because the enumeration filters the single owner schedule the
owner was drawn from. -/
theorem mem_failureOwners (classification : family.Classification)
    (failure : Failure)
    (owner : family.FailureOwner classification failure) :
    owner ∈ (family.failureOwners classification failure).values :=
  (Enumeration.mem_subtype_values _ _ _ owner).mpr
    (Enumeration.mem_attach_values _ _)

/-- The surviving partition is complete for the same reason. -/
theorem mem_f5Owners (classification : family.Classification)
    (owner : family.F5Owner classification) :
    owner ∈ (family.f5Owners classification).values :=
  family.mem_failureOwners classification .f5 owner

/-- Branch-condition contradiction for a stored failure partition: a leaf
holding an owner of a partition its own branch recorded as empty cannot exist.
The branch supplies the emptiness it already wrote; nothing is recomputed. -/
theorem absurd_of_empty_failureOwners (classification : family.Classification)
    (failure : Failure)
    (empty : (family.failureOwners classification failure).values = [])
    (owner : family.FailureOwner classification failure) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _
    (family.mem_failureOwners classification failure owner)

/-- The same contradiction for the surviving partition. -/
theorem absurd_of_empty_f5Owners (classification : family.Classification)
    (empty : (family.f5Owners classification).values = [])
    (owner : family.F5Owner classification) : False :=
  family.absurd_of_empty_failureOwners classification .f5 empty owner

/-- The complete Core-owned state of one family scan.  Classification and
the exact F5-owner schedule are stored together, so a consumer cannot detach
the surviving schedule from the classification that produced its dependent
owner type. -/
structure ClassifiedState where
  classification : family.Classification
  f1Owners : Enumeration (family.FailureOwner classification .f1)
  f2Owners : Enumeration (family.FailureOwner classification .f2)
  f3Owners : Enumeration (family.FailureOwner classification .f3)
  f4Owners : Enumeration (family.FailureOwner classification .f4)
  survivingOwners : Enumeration (family.F5Owner classification)
  boundedOutcomes : (owner : family.F5Owner classification) →
    @Contract.StateTrace.BoundedOutcome
      (family.Item owner.1.1) (family.State owner.1.1)
      (family.stateFintype owner.1.1) (family.traceAt owner.1.1)
  firstNonF5 : Search.Execution family.owners.attach
    (fun owner => ¬ Contract.Classification.IsFailure
      (family.contractAt owner.1) (classification.classify owner) .f5)
  /-- Each stored partition lists *every* owner of its own type.  The
  partitions are filters of the one owner schedule, so this holds by
  construction; retaining it is what lets a branch that recorded a partition
  as empty rule the corresponding owner out instead of merely not finding it. -/
  f1Owners_complete : ∀ owner, owner ∈ f1Owners.values
  f2Owners_complete : ∀ owner, owner ∈ f2Owners.values
  f3Owners_complete : ∀ owner, owner ∈ f3Owners.values
  f4Owners_complete : ∀ owner, owner ∈ f4Owners.values
  survivingOwners_complete : ∀ owner, owner ∈ survivingOwners.values

/-- Branch-condition contradiction at a stored classified ledger entry: a leaf
holding an owner of a partition that this very entry recorded as empty cannot
exist.  The emptiness is the branch's own written fact and the completeness is
carried by the entry, so nothing is recomputed and no second scan is run.

Every arm below is the same statement for one terminal; applications match on
the stored list, and the `[]` case hands the recorded emptiness straight back. -/
theorem ClassifiedState.absurd_of_empty_f1Owners
    (state : family.ClassifiedState)
    (empty : state.f1Owners.values = [])
    (owner : family.FailureOwner state.classification .f1) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _ (state.f1Owners_complete owner)

theorem ClassifiedState.absurd_of_empty_f2Owners
    (state : family.ClassifiedState)
    (empty : state.f2Owners.values = [])
    (owner : family.FailureOwner state.classification .f2) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _ (state.f2Owners_complete owner)

theorem ClassifiedState.absurd_of_empty_f3Owners
    (state : family.ClassifiedState)
    (empty : state.f3Owners.values = [])
    (owner : family.FailureOwner state.classification .f3) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _ (state.f3Owners_complete owner)

theorem ClassifiedState.absurd_of_empty_f4Owners
    (state : family.ClassifiedState)
    (empty : state.f4Owners.values = [])
    (owner : family.FailureOwner state.classification .f4) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _ (state.f4Owners_complete owner)

theorem ClassifiedState.absurd_of_empty_survivingOwners
    (state : family.ClassifiedState)
    (empty : state.survivingOwners.values = [])
    (owner : family.F5Owner state.classification) : False :=
  (List.eq_nil_iff_forall_not_mem.mp empty) _
    (state.survivingOwners_complete owner)

/-- Every scheduled owner occurs in one of the five partitions stored in the
same classified-family ledger entry.  This eliminates the stored pointwise
classification only; it does not rerun a corridor search. -/
theorem ClassifiedState.owner_partition
    (state : family.ClassifiedState)
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f1 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f2 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f3 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f4 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f5 := by
  cases selected : state.classification.classify owner with
  | f5 all => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | hit witness =>
      have notF5 := Contract.HitWitness.notF5 (family.contractAt owner.1) witness
      rcases failure : witness.failure with _ | _ | _ | _ | _
      · exact Or.inl (by simpa [selected, failure,
          Contract.Classification.IsFailure])
      · exact Or.inr (Or.inl (by simpa [selected, failure,
          Contract.Classification.IsFailure]))
      · exact Or.inr (Or.inr (Or.inl (by simpa [selected, failure,
          Contract.Classification.IsFailure])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [selected, failure,
          Contract.Classification.IsFailure]))))
      · exact (notF5 failure).elim

/-- With all four failure partitions recorded empty, every scheduled owner
survived to F5.  This is `owner_partition` with the four impossible arms
discharged by the branch's own emptiness records. -/
theorem ClassifiedState.f5_of_empty_failurePartitions
    (state : family.ClassifiedState)
    (noF1 : state.f1Owners.values = []) (noF2 : state.f2Owners.values = [])
    (noF3 : state.f3Owners.values = []) (noF4 : state.f4Owners.values = [])
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Contract.Classification.IsFailure (family.contractAt owner.1)
      (state.classification.classify owner) .f5 := by
  rcases state.owner_partition family owner with h | h | h | h | h
  · exact (state.absurd_of_empty_f1Owners family noF1 ⟨owner, h⟩).elim
  · exact (state.absurd_of_empty_f2Owners family noF2 ⟨owner, h⟩).elim
  · exact (state.absurd_of_empty_f3Owners family noF3 ⟨owner, h⟩).elim
  · exact (state.absurd_of_empty_f4Owners family noF4 ⟨owner, h⟩).elim
  · exact h

/-- The exhaustive form: an entry that recorded *all five* partitions empty
has no scheduled owner at all.  A branch whose owner schedule is nonempty
therefore always reaches one of the five arms. -/
theorem ClassifiedState.absurd_of_empty_partitions
    (state : family.ClassifiedState)
    (noF1 : state.f1Owners.values = []) (noF2 : state.f2Owners.values = [])
    (noF3 : state.f3Owners.values = []) (noF4 : state.f4Owners.values = [])
    (noF5 : state.survivingOwners.values = [])
    (owner : {owner : Owner // owner ∈ family.owners.values}) : False :=
  state.absurd_of_empty_survivingOwners family noF5
    ⟨owner, state.f5_of_empty_failurePartitions family noF1 noF2 noF3 noF4 owner⟩

/-- If Core's stored first-non-F5 scan has no hit, every owner in the
incoming schedule was classified F5.  This eliminates the stored scan and
classification certificates; it does not rerun either computation. -/
theorem ClassifiedState.all_f5_of_no_firstNonF5
    (state : family.ClassifiedState)
    (absent : ¬ state.firstNonF5.HasHit)
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Contract.Classification.IsFailure (family.contractAt owner.1)
      (state.classification.classify owner) .f5 := by
  have avoids := state.firstNonF5.avoids_of_not_hasHit absent
  let index := family.owners.attach.indexOfMember owner
    (Enumeration.mem_attach_values family.owners owner)
  have rejected := avoids index
  have selected : family.owners.attach.get index = owner :=
    family.owners.attach.get_indexOfMember owner
      (Enumeration.mem_attach_values family.owners owner)
  rw [selected] at rejected
  exact Classical.byContradiction rejected

/-- A hit in Core's stored first-non-F5 scan retains the exact scheduled
owner and proves that its already-stored classification is one of F1--F4. -/
theorem ClassifiedState.firstNonF5_partition
    (state : family.ClassifiedState)
    (found : state.firstNonF5.HasHit) :
    let owner := state.firstNonF5.hitOfHasHit found |>.value
    Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f1 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f2 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f3 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        (state.classification.classify owner) .f4 := by
  let hit := state.firstNonF5.hitOfHasHit found
  have notF5 := hit.sound
  rcases state.owner_partition family hit.value with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))
  · exact (notF5 h5).elim

/-- The repeated-state predicate for one exact stored F5 outcome.  The
producer-owned finite-state instance is installed locally before eliminating
the outcome. -/
def ClassifiedState.IsRepeatedF5
    (state : family.ClassifiedState)
    (owner : family.F5Owner state.classification) : Prop := by
  letI := family.stateFintype owner.1.1
  exact (state.boundedOutcomes owner).IsRepeated

/-- The terminal predicate for one exact stored F5 outcome. -/
def ClassifiedState.IsTerminalF5
    (state : family.ClassifiedState)
    (owner : family.F5Owner state.classification) : Prop := by
  letI := family.stateFintype owner.1.1
  exact (state.boundedOutcomes owner).IsTerminal

/-- Every stored F5 owner belongs to one of the two exact bounded-outcome
partitions. -/
theorem ClassifiedState.terminal_or_repeated
    (state : family.ClassifiedState)
    (owner : family.F5Owner state.classification) :
    state.IsTerminalF5 family owner ∨ state.IsRepeatedF5 family owner := by
  letI := family.stateFintype owner.1.1
  exact (state.boundedOutcomes owner).isTerminal_or_isRepeated

/-- No stored F5 owner can appear in both bounded-outcome partitions. -/
theorem ClassifiedState.not_terminal_and_repeated
    (state : family.ClassifiedState)
    (owner : family.F5Owner state.classification) :
    ¬ (state.IsTerminalF5 family owner ∧ state.IsRepeatedF5 family owner) := by
  letI := family.stateFintype owner.1.1
  exact (state.boundedOutcomes owner).not_terminal_and_repeated

/-- One exact F5 owner whose stored bounded outcome selected the terminal
alternative. -/
abbrev TerminalF5Owner (state : family.ClassifiedState) :=
  {owner : family.F5Owner state.classification //
    state.IsTerminalF5 family owner}

/-- One exact F5 owner whose already-stored bounded outcome selected the
repeated-state alternative. -/
abbrev RepeatedF5Owner (state : family.ClassifiedState) :=
  {owner : family.F5Owner state.classification //
    state.IsRepeatedF5 family owner}

/-- Filter repeated-state owners from the stored F5 partition and stored
bounded outcomes.  No corridor event or repeated-state search is evaluated
again. -/
noncomputable def ClassifiedState.repeatedF5Owners
    (state : family.ClassifiedState) :
    Enumeration (family.RepeatedF5Owner state) :=
  state.survivingOwners.subtype
    (state.IsRepeatedF5 family)
    (fun _ => Classical.propDecidable _)

/-- Filter terminal owners from the stored F5 partition and stored bounded
outcomes.  No corridor event or bounded-outcome decision is rerun. -/
noncomputable def ClassifiedState.terminalF5Owners
    (state : family.ClassifiedState) :
    Enumeration (family.TerminalF5Owner state) :=
  state.survivingOwners.subtype
    (state.IsTerminalF5 family)
    (fun _ => Classical.propDecidable _)

/-- Eliminate the selected terminal branch for one owner in the stored family
state and recover its exact schedule bound. -/
def ClassifiedState.terminalF5Bound
    (state : family.ClassifiedState)
    (owner : family.TerminalF5Owner state) :
    (@Contract.StateTrace.schedule
      (family.Item owner.1.1.1) (family.State owner.1.1.1)
      (family.stateFintype owner.1.1.1)
      (family.traceAt owner.1.1.1)).card ≤
      @Fintype.card (family.State owner.1.1.1)
        (family.stateFintype owner.1.1.1) := by
  letI := family.stateFintype owner.1.1.1
  exact (state.boundedOutcomes owner.1).terminalBoundOf owner.2

/-- Eliminate the selected repeated-state branch for one owner in the stored
family state.  The returned witness is the one contained in that exact
bounded outcome. -/
noncomputable def ClassifiedState.repeatedF5Witness
    (state : family.ClassifiedState)
    (owner : family.RepeatedF5Owner state) :
    @Contract.StateTrace.BoundedRepeat
      (family.Item owner.1.1.1) (family.State owner.1.1.1)
      (family.stateFintype owner.1.1.1) (family.traceAt owner.1.1.1) := by
  letI := family.stateFintype owner.1.1.1
  exact (state.boundedOutcomes owner.1).repeatedWitnessOf owner.2

noncomputable def classification : family.Classification where
  classify := fun owner =>
    (family.contractAt owner.1).classification

/-- Compute the family classification once and derive its F5 owners from that
same value. -/
noncomputable def classifiedState : family.ClassifiedState := by
  let classification := family.classification
  exact
    { classification := classification
      f1Owners := family.failureOwners classification .f1
      f2Owners := family.failureOwners classification .f2
      f3Owners := family.failureOwners classification .f3
      f4Owners := family.failureOwners classification .f4
      survivingOwners := family.f5Owners classification
      boundedOutcomes := fun owner => family.boundedOutcomeAt owner.1.1
      firstNonF5 := Search.run family.owners.attach
        (fun owner => ¬ Contract.Classification.IsFailure
          (family.contractAt owner.1)
          (classification.classify owner) .f5)
        (fun _ => Classical.propDecidable _)
      f1Owners_complete := family.mem_failureOwners classification .f1
      f2Owners_complete := family.mem_failureOwners classification .f2
      f3Owners_complete := family.mem_failureOwners classification .f3
      f4Owners_complete := family.mem_failureOwners classification .f4
      survivingOwners_complete := family.mem_f5Owners classification }

/-- The complete classified family is appended in one ordinary ledger
extension. -/
abbrev ClassifiedStateStage (Previous : Type uPrevious) :=
  Ledger.Extension Previous (fun _ => family.ClassifiedState)

noncomputable def classifyStateIntoLedger
    {Previous : Type uPrevious} (previous : Previous) :
    family.ClassifiedStateStage Previous :=
  Ledger.extend previous family.classifiedState

/-- Read the exact finite family state from its single ledger entry. -/
def classifiedStateQuery
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun _ => family.ClassifiedState) :=
  Query.latest

/-- Project the stored classification without rerunning the scan. -/
def storedClassificationQuery
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun _ => family.Classification) :=
  family.classifiedStateQuery.map fun _ state => state.classification

/-- Project Core's first non-F5 search from the same ledger entry as the
classification it searches.  Its dependent predicate mentions that exact
stored classification, so it cannot be paired with a detached family scan. -/
def storedFirstNonF5Query
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Search.Execution family.owners.attach
        (fun owner => ¬ Contract.Classification.IsFailure
          (family.contractAt owner.1)
          ((family.storedClassificationQuery stage).classify owner) .f5)) :=
  family.classifiedStateQuery.dependentMap fun _ state => state.firstNonF5

/-- Eliminate the no-hit branch of the exact first-non-F5 search read from
the active ledger. -/
theorem storedAllOwnersF5OfNoFirstNonF5
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (absent : ¬ (family.storedFirstNonF5Query stage).HasHit)
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Contract.Classification.IsFailure (family.contractAt owner.1)
      ((family.storedClassificationQuery stage).classify owner) .f5 :=
  ClassifiedState.all_f5_of_no_firstNonF5 family
    (family.classifiedStateQuery stage) absent owner

/-- Eliminate the hit branch of the exact first-non-F5 search read from the
active ledger.  The result is the typed F1--F4 partition for the stored hit. -/
theorem storedFirstNonF5Partition
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (found : (family.storedFirstNonF5Query stage).HasHit) :
    let owner := (family.storedFirstNonF5Query stage).hitOfHasHit found |>.value
    Contract.Classification.IsFailure (family.contractAt owner.1)
        ((family.storedClassificationQuery stage).classify owner) .f1 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        ((family.storedClassificationQuery stage).classify owner) .f2 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        ((family.storedClassificationQuery stage).classify owner) .f3 ∨
      Contract.Classification.IsFailure (family.contractAt owner.1)
        ((family.storedClassificationQuery stage).classify owner) .f4 :=
  ClassifiedState.firstNonF5_partition family
    (family.classifiedStateQuery stage) found

/-- Project the exact F5-owner schedule with its dependency on the stored
classification preserved in the result type. -/
def storedSurvivingOwnersQuery
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration
        (family.F5Owner (family.storedClassificationQuery stage))) :=
  family.classifiedStateQuery.dependentMap fun stage state => by
    simpa using state.survivingOwners

/-- Project the exact repeated-state F5 subschedule from the newest family
ledger entry.  Both membership proofs are indexed by the same stored
classification and bounded-outcome family. -/
noncomputable def storedRepeatedF5OwnersQuery
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration
        (family.RepeatedF5Owner (family.classifiedStateQuery stage))) :=
  family.classifiedStateQuery.dependentMap fun _ state =>
    state.repeatedF5Owners family

/-- Project the exact terminal F5 subschedule from the newest family ledger
entry.  It is indexed by the same stored classification and bounded outcomes
as the repeated subschedule. -/
noncomputable def storedTerminalF5OwnersQuery
    {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration
        (family.TerminalF5Owner (family.classifiedStateQuery stage))) :=
  family.classifiedStateQuery.dependentMap fun _ state =>
    state.terminalF5Owners family

/-- Project the exact F1 owner schedule from the stored partition. -/
def storedF1OwnersQuery {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration (family.FailureOwner
        (family.storedClassificationQuery stage) .f1)) :=
  family.classifiedStateQuery.dependentMap fun _ state => state.f1Owners

/-- Project the exact F2 owner schedule from the stored partition. -/
def storedF2OwnersQuery {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration (family.FailureOwner
        (family.storedClassificationQuery stage) .f2)) :=
  family.classifiedStateQuery.dependentMap fun _ state => state.f2Owners

/-- Project the exact F3 owner schedule from the stored partition. -/
def storedF3OwnersQuery {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration (family.FailureOwner
        (family.storedClassificationQuery stage) .f3)) :=
  family.classifiedStateQuery.dependentMap fun _ state => state.f3Owners

/-- Project the exact F4 owner schedule from the stored partition. -/
def storedF4OwnersQuery {Previous : Type uPrevious} :
    Query (family.ClassifiedStateStage Previous)
      (fun stage => Enumeration (family.FailureOwner
        (family.storedClassificationQuery stage) .f4)) :=
  family.classifiedStateQuery.dependentMap fun _ state => state.f4Owners

/-- Project one scheduled owner's classification from the stored family
state. -/
def storedMemberClassificationQuery
    {Previous : Type uPrevious}
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Query (family.ClassifiedStateStage Previous)
      (fun _ => (family.contractAt owner.1).Classification) :=
  family.storedClassificationQuery.map fun _ classification =>
    classification.classify owner

/-- Typed F1--F5 event for one scheduled owner, obtained only from the stored
family state. -/
noncomputable def storedMemberClassifiedEventQuery
    {Previous : Type uPrevious}
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Query (family.ClassifiedStateStage Previous)
      (fun _ => (family.contractAt owner.1).ClassifiedEvent) :=
  (family.storedMemberClassificationQuery owner).map fun _ classification =>
    classification.toClassifiedEvent

/-- Recover the exact stored event witness for a non-F5 owner in one stored
family state.  This only eliminates the recorded classification: it does not
rerun the corridor predicate or search the schedule again. -/
noncomputable def ClassifiedState.failureEvent
    (state : family.ClassifiedState)
    (failure : Failure) (notF5 : failure ≠ .f5)
    (owner : family.FailureOwner state.classification failure) :
    (family.contractAt owner.1.1).EventWitness failure :=
  Contract.Classification.failureEvent
    (family.contractAt owner.1.1)
    (state.classification.classify owner.1) failure notF5 owner.2

/-- Recover the universal F5 fact from an owner selected by the stored family
classification.  No corridor predicate is re-evaluated. -/
theorem ClassifiedState.allF5
    (state : family.ClassifiedState)
    (owner : family.F5Owner state.classification) :
    ∀ item ∈ (family.contractAt owner.1.1).schedule.values,
      (family.contractAt owner.1.1).f5 item
        ((family.contractAt owner.1.1).run item) :=
  Contract.Classification.allF5
    (family.contractAt owner.1.1)
    (state.classification.classify owner.1) owner.2

/-- Read the universal F5 fact from the newest family ledger entry. -/
theorem storedAllF5
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (owner : family.F5Owner
      (family.storedClassificationQuery stage)) :
    ∀ item ∈ (family.contractAt owner.1.1).schedule.values,
      (family.contractAt owner.1.1).f5 item
        ((family.contractAt owner.1.1).run item) :=
  ClassifiedState.allF5 family
    (family.classifiedStateQuery stage) owner

/-- Read Core's bounded-trace alternative for an F5 owner from the same
newest ledger entry that selected that owner. -/
noncomputable def storedF5BoundedOutcome
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (owner : family.F5Owner
      (family.storedClassificationQuery stage)) :
    @Contract.StateTrace.BoundedOutcome
      (family.Item owner.1.1) (family.State owner.1.1)
      (family.stateFintype owner.1.1) (family.traceAt owner.1.1) :=
  (family.classifiedStateQuery stage).boundedOutcomes owner

/-- Recover the exact repeated-state witness selected by the repeated F5
subschedule in the newest ledger entry. -/
noncomputable def storedRepeatedF5Witness
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (owner : family.RepeatedF5Owner
      (family.classifiedStateQuery stage)) :
    @Contract.StateTrace.BoundedRepeat
      (family.Item owner.1.1.1) (family.State owner.1.1.1)
      (family.stateFintype owner.1.1.1) (family.traceAt owner.1.1.1) :=
  (family.classifiedStateQuery stage).repeatedF5Witness family owner

/-- Recover the exact schedule bound selected by a terminal F5 owner in the
newest ledger entry. -/
def storedTerminalF5Bound
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (owner : family.TerminalF5Owner
      (family.classifiedStateQuery stage)) :
    (@Contract.StateTrace.schedule
      (family.Item owner.1.1.1) (family.State owner.1.1.1)
      (family.stateFintype owner.1.1.1)
      (family.traceAt owner.1.1.1)).card ≤
      @Fintype.card (family.State owner.1.1.1)
        (family.stateFintype owner.1.1.1) :=
  (family.classifiedStateQuery stage).terminalF5Bound family owner

/-- Read and eliminate one non-F5 owner from the newest family ledger entry.
The owner remains indexed by the classification read from that same entry. -/
noncomputable def storedFailureEvent
    {Previous : Type uPrevious}
    (stage : family.ClassifiedStateStage Previous)
    (failure : Failure) (notF5 : failure ≠ .f5)
    (owner : family.FailureOwner
      (family.storedClassificationQuery stage) failure) :
    (family.contractAt owner.1.1).EventWitness failure :=
  ClassifiedState.failureEvent family
    (family.classifiedStateQuery stage) failure notF5 owner

@[simp] theorem classifiedStateQuery_read_classifyStateIntoLedger
    {Previous : Type uPrevious} (previous : Previous) :
    family.classifiedStateQuery (family.classifyStateIntoLedger previous) =
      family.classifiedState := rfl

/-- The family classification is one ordinary dependent ledger extension. -/
abbrev ClassificationStage (Previous : Type uPrevious) :=
  Ledger.Extension Previous (fun _ => family.Classification)

noncomputable def classifyIntoLedger
    {Previous : Type uPrevious} (previous : Previous) :
    family.ClassificationStage Previous :=
  Ledger.extend previous family.classification

/-- Read the complete family classification from the newest ledger entry. -/
def classificationQuery
    {Previous : Type uPrevious} :
    Query (family.ClassificationStage Previous)
      (fun _ => family.Classification) :=
  Query.latest

/-- Read one scheduled corridor's dependent classification from the family
ledger without inspecting predecessor fields. -/
def memberClassificationQuery
    {Previous : Type uPrevious}
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Query (family.ClassificationStage Previous)
      (fun _ => (family.contractAt owner.1).Classification) :=
  family.classificationQuery.map fun _ result => result.classify owner

/-- Typed F1--F5 elimination view for one scheduled corridor, read directly
from the family ledger.  This preserves the original Core classification and
does not traverse or reconstruct a predecessor. -/
noncomputable def memberClassifiedEventQuery
    {Previous : Type uPrevious}
    (owner : {owner : Owner // owner ∈ family.owners.values}) :
    Query (family.ClassificationStage Previous)
      (fun _ => (family.contractAt owner.1).ClassifiedEvent) :=
  (family.memberClassificationQuery owner).map fun _ classified =>
    classified.toClassifiedEvent

/-- Canonical access to a scheduled owner once nonemptiness has been proved
from the producer ledger.  Core selects from the literal enumeration; a
consumer cannot supply an owner outside that schedule. -/
noncomputable def scheduledOwnerOfNonempty
    (owners_nonempty : family.owners.values ≠ []) :
    {owner : Owner // owner ∈ family.owners.values} := by
  let existsOwner :=
    List.exists_mem_of_ne_nil family.owners.values owners_nonempty
  exact ⟨Classical.choose existsOwner, Classical.choose_spec existsOwner⟩

/-- Read the F1--F5 event of Core's canonical scheduled owner.  This is a
specialization of `memberClassifiedEventQuery`, not a second classifier or
routing rule. -/
noncomputable def firstClassifiedEventQuery
    {Previous : Type uPrevious}
    (owners_nonempty : family.owners.values ≠ []) :
    Query (family.ClassificationStage Previous)
      (fun _ =>
        (family.contractAt
          (family.scheduledOwnerOfNonempty owners_nonempty).1).ClassifiedEvent) :=
  family.memberClassifiedEventQuery
    (family.scheduledOwnerOfNonempty owners_nonempty)

@[simp] theorem classificationQuery_read_classifyIntoLedger
    {Previous : Type uPrevious} (previous : Previous) :
    family.classificationQuery (family.classifyIntoLedger previous) =
      family.classification := rfl

end FamilyProducer

@[simp] theorem classificationQuery_read_classifyIntoLedger
    {Previous : Type uPrevious}
    (producer : Producer Item State) (previous : Previous) :
    (classificationQuery producer) (classifyIntoLedger producer previous) =
      Contract.classification (contract producer) := rfl

def bounds (producer : Producer Item State) (interfaceBudget overlapBudget : Nat) :
    Contract.StateBounds State :=
  { interfaceBudget, overlapBudget }

def qCold (_producer : Producer Item State) : Nat :=
  Fintype.card State

def mCold (producer : Producer Item State) (interfaceBudget overlapBudget : Nat) : Nat :=
  (producer.bounds interfaceBudget overlapBudget).supportBound

def bCold (producer : Producer Item State) (interfaceBudget overlapBudget : Nat) : Nat :=
  (producer.bounds interfaceBudget overlapBudget).exactOverlapBound

def dCold (producer : Producer Item State) (interfaceBudget overlapBudget : Nat) : Nat :=
  (producer.bounds interfaceBudget overlapBudget).exactExtractionDenominator

def boundsOfFiniteInterface
    (producer : Producer Item State) (Interface : Type uState) [Fintype Interface]
    (overlapBudget : Nat) :
    Contract.StateBounds State :=
  Contract.StateBounds.fromFiniteInterface Interface overlapBudget

/-! Producer-facing form of the schedule-derived budget constructor.  The
producer's trace supplies the literal item schedule; the caller supplies only
the finite vertex enumeration and support observation used by its domain. -/
noncomputable def boundsOfFiniteInterfaceAndSupport
    (producer : Producer Item State)
    (Interface : Type uInterface) [Fintype Interface]
    {Vertex : Type uVertex}
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) :
    Contract.StateBounds State :=
  Contract.StateBounds.fromFiniteInterfaceAndSupport Interface
    producer.trace.schedule vertices support

noncomputable def mColdOfFiniteInterfaceAndSupport
    (producer : Producer Item State)
    (Interface : Type uInterface) [Fintype Interface]
    {Vertex : Type uVertex}
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) : Nat :=
  (producer.boundsOfFiniteInterfaceAndSupport Interface vertices support).supportBound

noncomputable def bColdOfFiniteInterfaceAndSupport
    (producer : Producer Item State)
    (Interface : Type uInterface) [Fintype Interface]
    {Vertex : Type uVertex}
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) : Nat :=
  (producer.boundsOfFiniteInterfaceAndSupport Interface vertices support).exactOverlapBound

noncomputable def dColdOfFiniteInterfaceAndSupport
    (producer : Producer Item State)
    (Interface : Type uInterface) [Fintype Interface]
    {Vertex : Type uVertex}
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) : Nat :=
  (producer.boundsOfFiniteInterfaceAndSupport Interface vertices support).exactExtractionDenominator

def mColdOfFiniteInterface
    (producer : Producer Item State) (Interface : Type uState) [Fintype Interface]
    (overlapBudget : Nat) : Nat :=
  (producer.boundsOfFiniteInterface Interface overlapBudget).supportBound

def bColdOfFiniteInterface
    (producer : Producer Item State) (Interface : Type uState) [Fintype Interface]
    (overlapBudget : Nat) : Nat :=
  (producer.boundsOfFiniteInterface Interface overlapBudget).exactOverlapBound

def dColdOfFiniteInterface
    (producer : Producer Item State) (Interface : Type uState) [Fintype Interface]
    (overlapBudget : Nat) : Nat :=
  (producer.boundsOfFiniteInterface Interface overlapBudget).exactExtractionDenominator

noncomputable def f5Schedule (producer : Producer Item State) : Enumeration
    {item : Item // producer.f5 item (producer.run item)} :=
  Contract.f5Schedule producer.contract

theorem f5Schedule_nonempty
    (producer : Producer Item State)
    (existsF5 : ∃ item ∈ producer.trace.schedule.values,
      producer.f5 item (producer.run item)) :
    (producer.f5Schedule).values ≠ [] := by
  exact Contract.f5Schedule_nonempty producer.contract existsF5

theorem repeatedStateIndices
    (producer : Producer Item State)
    (longer : Fintype.card State < producer.trace.schedule.card) :
    ∃ (left right : Fin producer.trace.schedule.card), left < right ∧
      producer.trace.state (producer.trace.schedule.get left) =
        producer.trace.state (producer.trace.schedule.get right) :=
  producer.trace.exists_repeated_indices longer

/-! Canonical extraction is owned by the packing strategy.  A domain
registration supplies only the literal schedule and conflict observation;
the selected family is computed by Core. -/
noncomputable def canonicalPacking
    {Occurrence : Type uState}
    (schedule : Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict)
    (symmetric : Symmetric conflict) :
    Core.Strategy.ObstructionPackingClosure.Packing schedule conflict :=
  Core.Strategy.ObstructionPackingClosure.Packing.canonical
    schedule conflict decConflict symmetric

theorem canonicalPacking_selected_nonempty
    {Occurrence : Type uState}
    (schedule : Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict)
    (symmetric : Symmetric conflict)
    (schedule_nonempty : schedule.values ≠ []) :
    (canonicalPacking schedule conflict decConflict symmetric).selected ≠ [] := by
  intro selected_empty
  obtain ⟨item, item_mem⟩ :=
    List.exists_mem_of_ne_nil schedule.values schedule_nonempty
  obtain ⟨selectedItem, selected_mem, _ | equal⟩ :=
    (canonicalPacking schedule conflict decConflict symmetric).maximal item item_mem
  · simp [selected_empty] at selected_mem
  · simp [selected_empty] at selected_mem

end Producer

end Hypostructure.Core.Finite.ColdCorridor
