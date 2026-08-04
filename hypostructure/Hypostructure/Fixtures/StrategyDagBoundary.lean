import Hypostructure.Core.Strategy.Dag

/-!
# Strategy DAG application boundary

This fixture verifies the application boundary independently of any domain
backend.  An application declares a problem with an honest registered target
(no hardcoded `True`/`False` — the strict frontend rejects banal targets),
selects the empty official DAG through the sealed `ofDag%` frontend, and
reads the certified statement from the sealed report.  Backend strategy
capabilities and compiled execution data are not part of this module's
source language.
-/

namespace Hypostructure.Fixtures.StrategyDagBoundary

open Hypostructure
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := forall n : Nat, n + 0 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object) }

def strategyDag : Blueprint :=
  Blueprint.root.targetOrAvoid

noncomputable def problemDefinition : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag

#check Blueprint.root
#check problemDefinition.report

/-- The certified statement is a total projection of the sealed report. -/
theorem boundary_statement : forall n : Nat, n + 0 = n :=
  problemDefinition.report.statement.down

end Hypostructure.Fixtures.StrategyDagBoundary
