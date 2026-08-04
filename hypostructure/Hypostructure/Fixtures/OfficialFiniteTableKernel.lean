import Hypostructure.Core.Strategy.Official.FiniteTableKernel

/-!
# Fixture: official callback-free finite-table execution

The table is intentionally domainless.  Observations and transitions are
relations, and Core derives the complete run.  Reversing either carrier cannot
change the terminal because both relations are certified functional.
-/

namespace Hypostructure.Fixtures.OfficialFiniteTableKernel

open Hypostructure.Core
open Hypostructure.Core.Strategy.Official

def completeFin (n : Nat) : Finite.CompleteEnumeration (Fin n) :=
  Finite.CompleteEnumeration.ofFinEnum inferInstance

def machine : CertifiedFiniteTable where
  State := Fin 4
  Observation := Fin 2
  states := completeFin 4
  observations := completeFin 2
  initial := 3
  observes := fun state observation => observation = ⟨state.val % 2, by omega⟩
  observesDecidable := fun _ _ => inferInstance
  observesTotal := by
    intro state
    exact ⟨⟨state.val % 2, by omega⟩, rfl⟩
  observesFunctional := by
    intro state left right leftEq rightEq
    exact leftEq.trans rightEq.symm
  transitions := fun state _ next => state.val > 0 ∧ next.val + 1 = state.val
  transitionsDecidable := fun _ _ _ => inferInstance
  transitionsFunctional := by
    intro state observation left right leftRel rightRel
    apply Fin.ext
    omega
  measure := fun state => state.val
  transitionsDecrease := by
    intro state observation next related
    omega

noncomputable def result := machine.execute

example : result.rounds ≤ machine.measure machine.initial :=
  result.rounds_le_initial_measure

example : ∀ next, ¬machine.transitions result.terminal.state
    result.terminal.observation next :=
  machine.execute_terminal_irreducible

theorem terminal_measure_zero :
    machine.measure result.terminal.state = 0 := by
  by_contra nonzero
  have positive : 0 < result.terminal.state.val := by
    simpa [machine] using Nat.pos_of_ne_zero nonzero
  let next : Fin 4 :=
    ⟨result.terminal.state.val - 1, by omega⟩
  have related :
      machine.transitions result.terminal.state
        result.terminal.observation next := by
    change result.terminal.state.val > 0 ∧ next.val + 1 =
      result.terminal.state.val
    dsimp [next]
    omega
  exact result.terminal.irreducible next related

#print axioms result
#print axioms terminal_measure_zero

end Hypostructure.Fixtures.OfficialFiniteTableKernel
