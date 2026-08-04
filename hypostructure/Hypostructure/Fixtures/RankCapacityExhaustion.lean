import Hypostructure.CTAdapters

/-!
# Core rank-capacity exhaustion fixture

Two genuine CT15 executions are composed dependently.  The second receives
the complete ledger extension produced by the first.  `RankCapacityExhaustion` then
exposes the composed result as target/left/right semantic outcomes without
an application-created execution or copied predecessor.
-/

namespace Hypostructure.Fixtures.RankCapacityExhaustion

open Hypostructure
open Hypostructure.Core.Residual

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun object => object = true
  Statement := ∀ object : Bool, object = true
  statement_to_target := fun statement object _ => statement object
  target_to_statement := fun closure object => closure object trivial

abbrev Input := Core.Strategy.ProblemInput problem

def firstSpec : CT15.Spec Input where
  Coordinate := fun _ => Unit
  TargetDependent := fun input _ => input.object = true
  charge := fun _ _ => 0
  capacity := fun _ => 0

def firstCapability : CT15.Capability firstSpec where
  coordinates := Query.ofFunction fun input => by
    change Core.Finite.Enumeration Unit
    exact Core.Finite.Enumeration.singleton ()
  targetDependentDecidable := fun input _ => by
    change Decidable (input.object = true)
    exact Bool.decEq input.object true
  inputSize := fun _ => 1
  workCoefficient := 3
  workDegree := 1
  workBound := fun _ => by
    change 3 ≤ 3 * (1 + 1) ^ 1
    decide

noncomputable def firstExecution : Core.Strategy.CTExecution Input :=
  CTAdapters.ct15 firstCapability

abbrev Middle :=
  Ledger.Extension Input firstExecution.Output

def secondSpec : CT15.Spec Middle where
  Coordinate := fun _ => Unit
  TargetDependent := fun _ _ => False
  charge := fun _ _ => 0
  capacity := fun _ => 0

def secondCapability : CT15.Capability secondSpec where
  coordinates := Query.ofFunction fun previous => by
    change Core.Finite.Enumeration Unit
    exact Core.Finite.Enumeration.singleton ()
  targetDependentDecidable := fun _ _ => by
    change Decidable False
    exact .isFalse id
  inputSize := fun _ => 1
  workCoefficient := 3
  workDegree := 1
  workBound := fun _ => by
    change 3 ≤ 3 * (1 + 1) ^ 1
    decide

noncomputable def secondExecution : Core.Strategy.CTExecution Middle :=
  CTAdapters.ct15 secondCapability

noncomputable def pipeline : Core.Strategy.CTExecution Input :=
  firstExecution.compose secondExecution

noncomputable def strategy :
    Core.Strategy.RankCapacityExhaustion problem target pipeline where
  Left := fun _ => Unit
  Right := fun _ => Unit
  interpret := fun input _output => by
    classical
    exact if h : input.object = true then
        .inl ⟨h⟩
      else if _hFalse : input.object = false then
        .inr (.inl ())
      else
        .inr (.inr ())
  metadata := { name := "two-CT frontier" }
  leftMetadata := { name := "left continuation" }
  rightMetadata := { name := "right continuation" }

noncomputable def dichotomy : Core.DichotomyData problem target :=
  strategy.toDichotomy

theorem composition_preserves_input (input : Input) :
    (pipeline.run input).1.stage.previous = input := rfl

#print axioms composition_preserves_input
#print axioms dichotomy

end Hypostructure.Fixtures.RankCapacityExhaustion
