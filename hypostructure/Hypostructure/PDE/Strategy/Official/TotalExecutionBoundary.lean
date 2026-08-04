import Hypostructure.Core.Strategy.Dag
import Hypostructure.PDE.NavierStokes.Basic

/-!
# Total official execution boundary for PDE applications

This PDE fixture pins the domain-transfer side of the sealed strategy-DAG
API.  A PDE application contributes represented analytic data, an honest
target, and a key-only `Dag.Blueprint`.  It cannot contribute a dispatcher,
route callback, executor result, or unsupported terminal.

The declaration below is deliberately PDE-valued: its ambient objects are
Navier--Stokes fields and its target is the pointwise additive identity for
the registered pressure field.  Execution and certification remain entirely
behind Core's sealed `ofDag%` boundary.
-/

namespace Hypostructure.PDE.Strategy.Official.TotalExecutionBoundary

open Hypostructure
open Hypostructure.PDE.NavierStokes
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun (field : Field) =>
    ∀ z, field.pressure z + 0 = field.pressure z
  Statement := ∀ (field : Field) z,
    field.pressure z + 0 = field.pressure z
  statement_to_target := by
    intro statement field _baseline
    exact statement field
  target_to_statement := by
    intro closure field
    exact closure field trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input =>
      .isTrue (fun z => add_zero (input.object.pressure z))
  }
  metadata := {
    name := "PDE total official execution boundary"
    statement := "pressure pointwise additive identity"
    note := "PDE official sealed-DAG fixture"
  }

def strategyDag : Blueprint :=
  Blueprint.root

noncomputable def declaration : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag

/-- A PDE application reads a total kernel theorem, not an executor result
that could dynamically contain `unsupported`. -/
theorem certified_statement : target.Statement :=
  declaration.report.statement.down

/-! ## No application-owned routing

The public blueprint language accepts only official strategy keys.  Even a
total function with a plausible routing shape cannot be attached to a DAG
vertex.
-/

def applicationRouteCallback :
    StrategyKey → Field → Option StrategyKey :=
  fun key _field => some key

/--
error: Application type mismatch: The argument
  applicationRouteCallback
has type
  StrategyKey → NavierStokes.Field → Option StrategyKey
but is expected to have type
  StrategyKey
in the application
  Blueprint.root.step applicationRouteCallback
-/
#guard_msgs (error) in
example : Blueprint :=
  Blueprint.root.step applicationRouteCallback

/-! ## No dynamic unsupported result

The sealed declaration exposes a total report statement.  Its execution and
result are private, so PDE application code cannot inspect, manufacture, or
route around a runtime failure.
-/

/--
error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.run`
-/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.run

/--
error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.outcome`
-/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.outcome

/--
info: 'Hypostructure.PDE.Strategy.Official.TotalExecutionBoundary.certified_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certified_statement

end Hypostructure.PDE.Strategy.Official.TotalExecutionBoundary
