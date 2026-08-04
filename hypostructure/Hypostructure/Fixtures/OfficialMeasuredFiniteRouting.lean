import Hypostructure.Core.Strategy.Official.Strategies.MeasuredFiniteRouting

namespace Hypostructure.Fixtures.OfficialMeasuredFiniteRouting

open Core.Strategy.Official.Strategies.MeasuredFiniteRouting

abbrev countdown : Machine where
  State := Nat
  Terminal := Unit
  step
    | 0 => .terminal ()
    | n + 1 => .feedback n
  measure := fun n => n
  decreases := by
    intro state next selected
    cases state with
    | zero => simp at selected
    | succ n =>
        simp at selected
        subst next
        omega

example : (countdown.execute 4).feedbackSteps = 4 := by native_decide
example : (countdown.execute 4).states = [4, 3, 2, 1, 0] := by native_decide
example : (countdown.execute 4).terminalValue = () := rfl
example : (countdown.execute 4).feedbackSteps ≤ countdown.measure 4 :=
  countdown.execute_feedbackSteps_le_measure 4

#print axioms Machine.execute
#print axioms Machine.execute_feedbackSteps_le_measure

end Hypostructure.Fixtures.OfficialMeasuredFiniteRouting
