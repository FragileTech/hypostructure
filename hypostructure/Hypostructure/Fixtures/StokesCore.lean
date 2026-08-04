import Hypostructure.Core.Strategy.Dag
import Hypostructure.PDE.NavierStokes.Basic

/-!
# Strategy-first Stokes pressure DAG

The application boundary is the current Core API: one problem definition and
one DAG blueprint assembled from a registered Core strategy.  The pressure
split is a PDE observable, not an application-defined execution stage.
-/

namespace Hypostructure.Fixtures.StokesCore

open Hypostructure
open Hypostructure.PDE.NavierStokes

structure PressureDecomposition (field : Field) where
  localPart : Spacetime → Real
  globalPart : Spacetime → Real
  pressure : Spacetime → Real
  pressure_eq : pressure = field.pressure
  reconstruct : ∀ z, localPart z + globalPart z = pressure z

def canonicalPressureDecomposition (field : Field) :
    PressureDecomposition field where
  localPart := field.pressure
  globalPart := fun _ => 0
  pressure := field.pressure
  pressure_eq := rfl
  reconstruct := by intro z; simp

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun field => Nonempty (PressureDecomposition field)
  Statement := ∀ field, Nonempty (PressureDecomposition field)
  statement_to_target := by
    intro statement field _baseline
    exact statement field
  target_to_statement := by
    intro target field
    exact target field trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input =>
        .isTrue ⟨canonicalPressureDecomposition input.object⟩ }

def rootDag : Core.Strategy.Dag.Blueprint :=
  Core.Strategy.Dag.Blueprint.root

def strategyDag : Core.Strategy.Dag.Blueprint :=
  rootDag

open Hypostructure.Core.Strategy.Dag in
noncomputable def problemDefinition :
    Core.Strategy.Dag.ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag

theorem canonical_pressure_split (field : Field) :
    Nonempty (PressureDecomposition field) :=
  ⟨canonicalPressureDecomposition field⟩

theorem unconditional_pressure_reconstruction : target.Statement := by
  intro field
  exact canonical_pressure_split field

/-- The acceptance criterion end to end: the application supplies one
problem definition and one key-only DAG, and reads the kernel-certified
registered statement from the sealed report. -/
theorem strategy_certified_pressure_reconstruction : target.Statement :=
  problemDefinition.report.statement.down

#check problemDefinition.report
#print axioms unconditional_pressure_reconstruction
#print axioms strategy_certified_pressure_reconstruction

end Hypostructure.Fixtures.StokesCore
