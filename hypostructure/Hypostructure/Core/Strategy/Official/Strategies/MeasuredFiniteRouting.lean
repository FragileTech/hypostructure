/-!
# Framework-owned measured finite routing

This module is the recursion kernel used by closed Core, Graph, and PDE
strategy backends.  It is intentionally not a problem-presentation slot:
applications cannot register a `Machine`, select a successor, or expose a
feedback edge in an official DAG.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.MeasuredFiniteRouting

universe uState uTerminal

/-- One closed backend step either reaches an exhaustive terminal or returns
the unique next state. -/
inductive Step (State : Type uState) (Terminal : Type uTerminal) where
  | terminal (value : Terminal)
  | feedback (next : State)

/-- A strictly decreasing machine.  Values of this structure are constructed
only inside reviewed framework backends; the official problem schema has no
field of this type. -/
structure Machine where
  State : Type uState
  Terminal : Type uTerminal
  step : State → Step State Terminal
  measure : State → Nat
  decreases : ∀ state next, step state = .feedback next →
    measure next < measure state

namespace Machine

/-- The proof-relevant trace of the exact framework-selected route. -/
inductive Run (machine : Machine.{uState, uTerminal}) :
    machine.State → Type (max uState uTerminal) where
  | terminal (state : machine.State) (value : machine.Terminal)
      (selected : machine.step state = .terminal value) :
      Run machine state
  | feedback (state next : machine.State)
      (selected : machine.step state = .feedback next)
      (decreases : machine.measure next < machine.measure state)
      (tail : Run machine next) :
      Run machine state

/-- Core executes feedback internally.  The outer official DAG sees only the
terminal and the proof-relevant decreasing trace. -/
def execute (machine : Machine.{uState, uTerminal}) :
    (state : machine.State) → machine.Run state
  | state =>
      match selected : machine.step state with
      | .terminal value => .terminal state value selected
      | .feedback next =>
          .feedback state next selected
            (machine.decreases state next selected)
            (machine.execute next)
termination_by state => machine.measure state
decreasing_by
  simpa using machine.decreases _ _ selected

def Run.terminalValue {machine : Machine.{uState, uTerminal}}
    {state : machine.State} : machine.Run state → machine.Terminal
  | .terminal _ value _ => value
  | .feedback _ _ _ _ tail => tail.terminalValue

def Run.feedbackSteps {machine : Machine.{uState, uTerminal}}
    {state : machine.State} : machine.Run state → Nat
  | .terminal .. => 0
  | .feedback _ _ _ _ tail => tail.feedbackSteps + 1

def Run.states {machine : Machine.{uState, uTerminal}}
    {state : machine.State} : machine.Run state → List machine.State
  | .terminal state .. => [state]
  | .feedback state _ _ _ tail => state :: tail.states

theorem Run.feedbackSteps_le_measure
    {machine : Machine.{uState, uTerminal}} {state : machine.State}
    (run : machine.Run state) :
    run.feedbackSteps ≤ machine.measure state := by
  induction run with
  | terminal => simp [feedbackSteps]
  | feedback state next _ decreases tail ih =>
      simp only [feedbackSteps]
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih decreases)

theorem execute_feedbackSteps_le_measure
    (machine : Machine.{uState, uTerminal}) (state : machine.State) :
    (machine.execute state).feedbackSteps ≤ machine.measure state :=
  (machine.execute state).feedbackSteps_le_measure

end Machine

end Hypostructure.Core.Strategy.Official.Strategies.MeasuredFiniteRouting
