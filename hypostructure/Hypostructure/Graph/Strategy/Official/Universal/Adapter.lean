import Hypostructure.Core.Strategy.Official.ProblemDefinition
import Hypostructure.Graph.Strategy.Official.Universal.Declaration

/-!
# Universal Graph declaration adapter

This module is the closed Graph-owned conversion from the inert universal
declaration language to Core's mathematical problem boundary.  It performs no
strategy execution and accepts no application callback.
-/

namespace Hypostructure.Graph.Strategy.Official.Universal

open Hypostructure
open Hypostructure.Graph

universe u

namespace Declaration

variable (declaration : Declaration)

/-- The canonical theorem represented by a universal graph declaration. -/
abbrev Statement : Prop :=
  ∀ object : FiniteObject.{u}, declaration.Baseline object →
    HasCycleWithLength declaration.target.CycleLengthOK object

/-- The exact Core target induced by the closed baseline and cycle target.
Both formulation maps are identities; in particular, this adapter contributes
no theorem certificate. -/
noncomputable def coreTarget : Core.Target declaration.problem where
  Predicate :=
    HasCycleWithLength declaration.target.CycleLengthOK
  Statement := declaration.Statement
  statement_to_target := fun statement object baseline =>
    statement object baseline
  target_to_statement := fun allTargets => allTargets

/-- Convert the universal Graph declaration to the callback-free official Core
problem shape.  The authored program remains inert data and is deliberately
not installed as an executor. -/
noncomputable def toOfficialProblemDefinition :
    Core.Strategy.Official.ProblemDefinition where
  problem := declaration.problem
  target := declaration.coreTarget
  schema := declaration.schema
  metadata := {
    name := "universal finite-graph cycle target"
    statement := "every baseline graph has a cycle of an accepted length"
    source := "Graph.Strategy.Official.Universal.Declaration"
  }

@[simp] theorem toOfficialProblemDefinition_problem :
    declaration.toOfficialProblemDefinition.problem = declaration.problem :=
  rfl

@[simp] theorem toOfficialProblemDefinition_target :
    declaration.toOfficialProblemDefinition.target = declaration.coreTarget :=
  rfl

@[simp] theorem coreTarget_predicate (object : FiniteObject.{u}) :
    declaration.coreTarget.Predicate object =
      HasCycleWithLength declaration.target.CycleLengthOK object :=
  rfl

end Declaration

end Hypostructure.Graph.Strategy.Official.Universal
