import Hypostructure.Core.Strategy.Dag

/-!
# Sealed strategy-DAG reduction boundary

An empty DAG cannot prove the target, but it unconditionally returns the
initial residual.  This fixture verifies that `reduceDag%` seals that exact
target-or-residual execution without accepting a closure argument.
-/

namespace Hypostructure.Fixtures.StrategyDagReductionBoundary

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

def reductionDag : Program definition.data :=
  Program.ofBlueprint Blueprint.root

noncomputable def reductionDefinition : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% definition reductionDag

#check reductionDefinition.report.statement
#check reductionDefinition.report.path
#check reductionDefinition.report.workBound

end Hypostructure.Fixtures.StrategyDagReductionBoundary
