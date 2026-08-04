import Hypostructure.Core.Strategy.Dag

/-!
# Strategy frontend validation

Rejection pins for the strict `ofDag%` frontend.  Every curated error
variant is pinned verbatim: banal targets (hardcoded `True`/`False`
statements and predicates, object-independent predicates, `False`
baselines), blueprints naming unregistered strategies, and problems that do
not certify their target.  The honest escape hatch — an explicit closure
proof — is pinned to succeed, and pinned not to bypass blueprint
compliance.  The kernel never sees any of the rejected declarations: the
frontend refuses them before the private compiler is invoked.
-/

namespace Hypostructure.Fixtures.StrategyDagValidation

open Hypostructure
open Hypostructure.Core.Strategy.Dag

/-! ## An honest registered problem (accepted) -/

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

noncomputable def accepted : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition Blueprint.root.targetOrAvoid

/-- The honest escape hatch: an explicit closure proof is accepted. -/
noncomputable def acceptedExplicit : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition Blueprint.root
    (certifies := fun input => Nat.add_zero input.object)

/-- The certified statement is total: an accepted declaration always
exports its registered theorem. -/
theorem accepted_statement : forall n : Nat, n + 0 = n :=
  accepted.report.statement.down

/-! ## Rejection: unregistered strategies -/

/--
error: ofDag% rejected this declaration: the blueprint references strategies the problem does not register:
  • orderedWitnessScan 3 — only 0 registered families (StrategyData field `scans`)
  • capacityLedger 1 — only 0 registered families (StrategyData field `capacities`)
Only official strategy keys backed by registered data may appear in a DAG.
Remove the offending vertices or register the corresponding families.
-/
#guard_msgs (error) in
noncomputable def rejectedKeys : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition (Blueprint.root.orderedWitnessScan 3 |>.capacityLedger 1)

/--
error: ofDag% rejected this declaration: the blueprint references strategies the problem does not register:
  • orderedWitnessScan 3 — only 0 registered families (StrategyData field `scans`)
Only official strategy keys backed by registered data may appear in a DAG.
Remove the offending vertices or register the corresponding families.
-/
#guard_msgs (error) in
noncomputable def rejectedKeysExplicit : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition (Blueprint.root.orderedWitnessScan 3)
    (certifies := fun input => Nat.add_zero input.object)

/-! ## Rejection: banal targets -/

def trivialStatementTarget : Core.Target problem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := True
  statement_to_target := fun _ n _ => Nat.add_zero n
  target_to_statement := fun _ => trivial

def trivialStatementDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := trivialStatementTarget
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object) }

/--
error: ofDag% rejected this declaration: the registered target is banal: `Statement` reduces to `True`.
The strict frontend refuses hardcoded targets — a certified run must prove real registered content, not a constant.
Register the actual mathematical statement this problem is meant to certify.
-/
#guard_msgs (error) in
noncomputable def rejectedTrivialStatement : ProblemDeclaration.{0, 0, 0} :=
  ofDag% trivialStatementDefinition Blueprint.root

def trivialPredicateTarget : Core.Target problem where
  Predicate := fun _ => True
  Statement := forall _n : Nat, True
  statement_to_target := fun _ _ _ => trivial
  target_to_statement := fun _ _ => trivial

def trivialPredicateDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := trivialPredicateTarget
  initialState := fun _ => ()
  data := { targetDecidable := fun _ => .isTrue trivial }

/--
error: ofDag% rejected this declaration: the registered target is banal: `Predicate` reduces to `True` for every ambient object.
The strict frontend refuses hardcoded targets — a certified run must prove real registered content, not a constant.
Register the actual per-object target the strategies are meant to establish.
-/
#guard_msgs (error) in
noncomputable def rejectedTrivialPredicate : ProblemDeclaration.{0, 0, 0} :=
  ofDag% trivialPredicateDefinition Blueprint.root

def constantPredicateTarget : Core.Target problem where
  Predicate := fun _ => 0 = 0
  Statement := forall _n : Nat, 0 = 0
  statement_to_target := fun _ _ _ => rfl
  target_to_statement := fun _ _ => rfl

def constantPredicateDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := constantPredicateTarget
  initialState := fun _ => ()
  data := { targetDecidable := fun _ => .isTrue rfl }

/--
error: ofDag% rejected this declaration: the registered target is banal: `Predicate` does not depend on the ambient object.
Every certified run proves the target for each problem input; an object-independent predicate would banalize the theorem.
Index the target predicate by the ambient object it constrains.
-/
#guard_msgs (error) in
noncomputable def rejectedConstantPredicate : ProblemDeclaration.{0, 0, 0} :=
  ofDag% constantPredicateDefinition Blueprint.root

def vacuousProblem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => False
  BranchState := fun _ => Unit

def vacuousTarget : Core.Target vacuousProblem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := forall n : Nat, n + 0 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun _ n => Nat.add_zero n

def vacuousDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := vacuousProblem
  target := vacuousTarget
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object) }

/--
error: ofDag% rejected this declaration: the registered problem is vacuous: `Baseline` reduces to `False`, so no problem input exists.
Certification over an empty input space is meaningless; the strict frontend refuses it.
Register a satisfiable baseline (use `fun _ => True` when there is no precondition).
-/
#guard_msgs (error) in
noncomputable def rejectedVacuous : ProblemDeclaration.{0, 0, 0} :=
  ofDag% vacuousDefinition Blueprint.root

/-! ## Rejection: the problem does not certify its target -/

def stuckTarget : Core.Target problem where
  Predicate := fun n : Nat => n = 0
  Statement := forall n : Nat, n = 0
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def stuckDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := stuckTarget
  initialState := fun _ => ()
  data := { targetDecidable := fun input => Nat.decEq input.object 0 }

/--
error: ofDag% rejected this declaration: the registered problem does not certify its target: `targetDecidable` does not reduce to `isTrue` for an arbitrary input.
The strict frontend only compiles declarations guaranteed to produce an unconditional theorem.
Register a decision procedure of the form `fun input => .isTrue (proof input)`, or supply an explicit closure proof with `ofDag% definition dag (certifies := proof)`.
-/
#guard_msgs (error) in
noncomputable def rejectedStuck : ProblemDeclaration.{0, 0, 0} :=
  ofDag% stuckDefinition Blueprint.root

def refutedTarget : Core.Target problem where
  Predicate := fun n : Nat => n + 1 = n
  Statement := forall n : Nat, n + 1 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def refutedDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := refutedTarget
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isFalse (Nat.succ_ne_self input.object) }

/--
error: ofDag% rejected this declaration: the registered problem does not certify its target: `targetDecidable` does not reduce to `isTrue` for an arbitrary input.
The strict frontend only compiles declarations guaranteed to produce an unconditional theorem.
Register a decision procedure of the form `fun input => .isTrue (proof input)`, or supply an explicit closure proof with `ofDag% definition dag (certifies := proof)`.
-/
#guard_msgs (error) in
noncomputable def rejectedRefuted : ProblemDeclaration.{0, 0, 0} :=
  ofDag% refutedDefinition Blueprint.root

/-! ## Rejection: malformed first argument -/

/--
error: ofDag% rejected this declaration: the first argument must be a `Core.ProblemDefinition`.
-/
#guard_msgs (error) in
noncomputable def rejectedNotAProblem : ProblemDeclaration.{0, 0, 0} :=
  ofDag% (42 : Nat) Blueprint.root

/-! ## Kernel trust -/

/--
info: 'Hypostructure.Fixtures.StrategyDagValidation.accepted_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms accepted_statement

end Hypostructure.Fixtures.StrategyDagValidation
