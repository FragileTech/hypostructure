import Hypostructure.Core.Strategy.Dag
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Strategy.CounterexampleLocalization

/-!
# Sealed generic Graph counterexample localization

The Graph adapter retains Core's exact selected minimal context as the next
local graph residual.  The DAG contains only the registered generic strategy.
-/

namespace Hypostructure.Fixtures.GraphCounterexampleLocalization

open Hypostructure
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Graph.FiniteObject
  Baseline := fun object => 0 < object.vertexCount
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun object => object.vertexCount = 0
  Statement := ∀ object, problem.Baseline object → object.vertexCount = 0
  statement_to_target := fun statement object baseline => statement object baseline
  target_to_statement := fun closure object baseline => closure object baseline

def selection : Core.MinimalCounterexampleSelectionData problem :=
  Core.MinimalCounterexampleSelectionData.ofProgress
    (Graph.CanonicalProgress.progress (P := problem))

def localization :
    Core.CounterexampleLocalizationData problem target :=
  Graph.Strategy.CounterexampleLocalization.registration selection

def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input =>
      inferInstanceAs (Decidable (input.object.vertexCount = 0))
    counterexampleLocalizations := [localization]
  }

instance : NeZero definition.data.counterexampleLocalizations.length :=
  ⟨by simp [definition]⟩

def program : Program definition.data :=
  Program.ofBlueprint Blueprint.root.counterexampleLocalization

noncomputable def declaration : ReductionDeclaration :=
  reduceDag% definition program

example :
    declaration.report.path =
      [Core.Strategy.Dag.StrategyKey.counterexampleLocalization 0] :=
  rfl

end Hypostructure.Fixtures.GraphCounterexampleLocalization
