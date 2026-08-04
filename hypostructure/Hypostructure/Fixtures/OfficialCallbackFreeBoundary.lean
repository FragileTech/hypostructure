import Hypostructure.Core.Strategy.Official.Availability

namespace Hypostructure.Fixtures.OfficialCallbackFreeBoundary

open Core
open Core.Strategy.Official
open Core.Strategy.OfficialRegistry

private noncomputable def unitCarrier : FiniteCarrier where
  Carrier := Unit
  finite := inferInstance

private noncomputable def schedule : ScheduleSlot where
  carrier := unitCarrier
  rows := [()]
  covers := by intro x; cases x; simp

private def problem : Problem where
  Ambient := Unit
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private def target : Target problem where
  Predicate := fun _ => True
  Statement := True
  statement_to_target := by simp
  target_to_statement := by simp

private noncomputable def definition : Core.Strategy.Official.ProblemDefinition where
  problem := problem
  target := target
  schema := {
    core := {
      schedules := [schedule]
    }
  }

example : Available definition ⟨.orderedExhaustion, 0⟩ := by
  exact ⟨by simp [definition, slotCount]⟩

example : ¬ Available definition ⟨.orderedExhaustion, 1⟩ := by
  rw [available_iff]
  simp [definition, slotCount]

example :
    (describe ({ id := .orderedExhaustion, slot := 0 } : StrategyRef).id).owner =
    (describe ({ id := .orderedExhaustion, slot := 37 } : StrategyRef).id).owner := by
  rfl

example : ¬ Available definition ⟨.targetDecision, 0⟩ := by
  rw [available_iff]
  simp [slotCount]

end Hypostructure.Fixtures.OfficialCallbackFreeBoundary
