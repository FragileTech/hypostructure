import Hypostructure.Core.Finite.Enumeration

/-!
# Private execution kernel for official finite-table strategies

This module is the operational boundary for finite official strategies.  Its
input contains finite carriers and decidable mathematical relations only.
There is no observation function, transition function, branch classifier,
target predicate, target finalizer, or application-produced terminal.

Core derives the unique observation and the optional unique successor by
searching the certified relations.  It then performs well-founded recursion
and returns the literal irreducible table state.
-/

namespace Hypostructure.Core.Strategy.Official

universe uState uObservation

/-- Inert finite relational presentation of a deterministic, terminating
machine.  The two relations are mathematical table data; all operational
choices are derived by the private kernel below. -/
structure CertifiedFiniteTable where
  State : Type uState
  Observation : Type uObservation
  states : Core.Finite.CompleteEnumeration State
  observations : Core.Finite.CompleteEnumeration Observation
  initial : State
  observes : State → Observation → Prop
  observesDecidable : ∀ state observation, Decidable (observes state observation)
  observesTotal : ∀ state, ∃ observation, observes state observation
  observesFunctional : ∀ {state left right},
    observes state left → observes state right → left = right
  transitions : State → Observation → State → Prop
  transitionsDecidable :
    ∀ state observation next, Decidable (transitions state observation next)
  transitionsFunctional : ∀ {state observation left right},
    transitions state observation left →
    transitions state observation right →
    left = right
  measure : State → Nat
  transitionsDecrease : ∀ {state observation next},
    transitions state observation next → measure next < measure state

namespace CertifiedFiniteTable

variable (table : CertifiedFiniteTable)

private def observation? (state : table.State) : Option table.Observation :=
  letI := table.observesDecidable state
  table.observations.values.find? (table.observes state)

private theorem observation?_isSome (state : table.State) :
    (table.observation? state).isSome := by
  letI := table.observesDecidable state
  obtain ⟨observation, related⟩ := table.observesTotal state
  rw [Option.isSome_iff_ne_none]
  intro absent
  have misses := (List.find?_eq_none.mp absent) observation
    (table.observations.complete observation)
  exact misses (decide_eq_true related)

private def derivedObservation (state : table.State) :
    table.Observation :=
  (table.observation? state).get (table.observation?_isSome state)

private theorem derivedObservation_spec (state : table.State) :
    table.observes state (table.derivedObservation state) := by
  unfold derivedObservation
  have selected :
      table.observation? state =
        some ((table.observation? state).get
          (table.observation?_isSome state)) :=
    (Option.some_get _).symm
  unfold observation? at selected
  letI := table.observesDecidable state
  exact of_decide_eq_true (List.find?_eq_some_iff_append.mp selected).1

/-- The relation-derived observation.  The result is independent of carrier
order because the relation is functional. -/
theorem observation_unique (state : table.State) (observation : table.Observation)
    (related : table.observes state observation) :
    observation = table.derivedObservation state :=
  table.observesFunctional related (table.derivedObservation_spec state)

private noncomputable def successor? (state : table.State) : Option table.State :=
  let observation := table.derivedObservation state
  letI := table.transitionsDecidable state observation
  table.states.values.find? (table.transitions state observation)

private theorem successor?_related {state next : table.State}
    (equal : table.successor? state = some next) :
    table.transitions state (table.derivedObservation state) next := by
  dsimp [successor?] at equal
  letI := table.transitionsDecidable state (table.derivedObservation state)
  exact of_decide_eq_true (List.find?_eq_some_iff_append.mp equal).1

private theorem successor?_complete {state next : table.State}
    (related : table.transitions state (table.derivedObservation state) next) :
    table.successor? state = some next := by
  have member := table.states.complete next
  unfold successor?
  letI := table.transitionsDecidable state (table.derivedObservation state)
  cases equal : table.states.values.find?
      (table.transitions state (table.derivedObservation state)) with
  | none =>
      have absent := (List.find?_eq_none.mp equal) next member
      exact False.elim (absent (decide_eq_true related))
  | some found =>
      have foundRelated :
          table.transitions state (table.derivedObservation state) found :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp equal).1
      have same := table.transitionsFunctional foundRelated related
      simpa [same] using equal

/-- A terminal is the exact state for which the certified transition relation
has no successor at its uniquely derived observation. -/
structure Terminal where
  state : table.State
  observation : table.Observation
  observed : table.observes state observation
  irreducible :
    ∀ next, ¬table.transitions state observation next

/-- Framework-produced execution result.  `rounds` is derived, never supplied
as a registration parameter. -/
structure Result where
  terminal : table.Terminal
  rounds : Nat
  rounds_le_initial_measure : rounds ≤ table.measure table.initial

private noncomputable def runFrom (state : table.State) :
    table.Terminal × Nat :=
  match equal : table.successor? state with
  | some next =>
      let result := runFrom next
      (result.1, result.2 + 1)
  | none =>
      ( { state := state
          observation := table.derivedObservation state
          observed := table.derivedObservation_spec state
          irreducible := by
            intro next related
            have impossible : (none : Option table.State) = some next := by
              rw [← equal]
              exact table.successor?_complete related
            cases impossible },
        0 )
termination_by table.measure state
decreasing_by
  exact table.transitionsDecrease (table.successor?_related (by assumption))

private theorem runFrom_rounds_le (state : table.State) :
    (runFrom table state).2 ≤ table.measure state := by
  rw [runFrom]
  split <;> rename_i equal
  next next =>
    simp only
    exact Nat.succ_le_of_lt
      (lt_of_le_of_lt (runFrom_rounds_le next)
        (table.transitionsDecrease (table.successor?_related equal)))
  next => simp
termination_by table.measure state
decreasing_by
  exact table.transitionsDecrease (table.successor?_related (by assumption))

/-- Execute an official finite table.  This is the sole public operation:
callers can provide no code that participates in a round. -/
noncomputable def execute : table.Result where
  terminal := (runFrom table table.initial).1
  rounds := (runFrom table table.initial).2
  rounds_le_initial_measure :=
    runFrom_rounds_le table table.initial

theorem execute_terminal_irreducible :
    ∀ next, ¬table.transitions table.execute.terminal.state
      table.execute.terminal.observation next :=
  table.execute.terminal.irreducible

end CertifiedFiniteTable

end Hypostructure.Core.Strategy.Official
