import Hypostructure.PDE.Strategy.CounterexampleLocalization

/-!
# Sealed generic PDE counterexample localization

This fixture exercises the public strategy boundary:

`global residual → Core minimal selection → represented local PDE residual`.

It supplies only a problem presentation, progress measure, and PDE locality
semantics.  The DAG contains one sealed strategy invocation.
-/

namespace Hypostructure.Fixtures.PDECounterexampleLocalization

open Hypostructure
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun n => 0 < n
  BranchState := fun _ => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _ _ => True
  nested := fun _ _ => True
  nested_refl := fun _ => trivial
  nested_trans := fun _ _ => trivial
  core := id
  core_nested := fun _ => trivial
  LocalObject := fun _ => Nat
  restrict := fun object _ => object
  restrictLocal := fun _ object => object
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by intros; rfl

def equation : PDE.RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun {_} {_} _ {_} data => data
  restrict_satisfies := fun {_} {_} _ {_} _ valid => valid

def model : PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def target : Core.Target problem where
  Predicate := fun (n : Nat) => n = 0
  Statement := ∀ (object : Nat), problem.Baseline object → object = 0
  statement_to_target := fun statement object baseline => statement object baseline
  target_to_statement := fun closure object baseline => closure object baseline

def localization :
    Core.CounterexampleLocalizationData problem target :=
  PDE.Strategy.CounterexampleLocalization.registration model target

def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input =>
      by
        change Decidable ((show Nat from input.object) = 0)
        infer_instance
    counterexampleLocalizations := [localization]
  }

instance : NeZero definition.data.counterexampleLocalizations.length :=
  ⟨by simp [definition]⟩

def program : Program definition.data :=
  Program.ofBlueprint Blueprint.root.counterexampleLocalization

noncomputable def declaration : ReductionDeclaration :=
  reduceDag% definition program

#check declaration.report.statement
#check declaration.report.path

example :
    declaration.report.path =
      [Core.Strategy.Dag.StrategyKey.counterexampleLocalization 0] :=
  rfl

end Hypostructure.Fixtures.PDECounterexampleLocalization
