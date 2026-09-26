import Hypostructure.Core.Strategy.RegistrationAudit

/-! Compile-time fixture for the strict registration audit. -/

namespace Hypostructure.Fixtures.RegistrationAudit

open Hypostructure Core Core.Strategy Core.Strategy.Dag
open scoped Hypostructure.Core.Strategy.RegistrationAudit

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun n => n = n
  Statement := ∀ n : Nat, n = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def scan : Core.ScanData problem where
  Item := fun _ => Fin 1
  schedule := fun _ => Core.Finite.Enumeration.singleton 0
  witness := fun _ _ => True
  witnessDecidable := fun _ _ => inferInstance

def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun _ => .isTrue rfl
    scans := [scan]
  }

def goodDag : Blueprint := .root |>.orderedWitnessScan 0

#hypostructure_strict_audit definition goodDag

/-- The rejection predicates themselves are framework-generic and executable. -/
example : goodDag.CompliantWith definition.data := by decide

#guard_msgs (drop error) in
#hypostructure_strict_audit definition (.root |>.targetOrAvoid)

#guard_msgs (drop error) in
#hypostructure_strict_audit definition
  (Blueprint.root |>.orderedWitnessScan 0 |>.orderedWitnessScan 0)

def unusedDefinition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun _ => .isTrue rfl
    scans := [scan]
  }

#guard_msgs (drop error) in
#hypostructure_strict_audit unusedDefinition .root

end Hypostructure.Fixtures.RegistrationAudit
