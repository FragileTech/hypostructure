import Hypostructure.Core.Strategy.Dag

namespace HypostructureQuickstart

open Hypostructure
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := ∀ n : Nat, n + 0 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input => .isTrue (Nat.add_zero input.object)
  }
  metadata := {
    name := "Natural-number identity"
    statement := "Every natural number satisfies n + 0 = n."
  }

noncomputable def strategyDag : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root.targetOrAvoid
      (name := "Close the registered target")
  )

noncomputable def proofReduction : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% definition strategyDag

#check proofReduction.report.statement

end HypostructureQuickstart
