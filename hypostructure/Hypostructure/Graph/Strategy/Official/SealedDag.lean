import Hypostructure.Core.Strategy.Dag
import Hypostructure.Graph.Strategy
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Strategy.CounterexampleReduction

/-!
# Sealed DAG boundary for official Graph proofs

Graph does not own an executor.  An official Graph proof is registered as a
`Core.ProblemDefinition`, described by a key-only `Dag.Program`, and sealed by
Core's `ofDag%` frontend.  This module deliberately exposes no dispatch,
merge, runtime result, application callback, or alternate execution path.
-/

namespace Hypostructure.Graph.Strategy.Official.SealedDag

open Hypostructure
open Hypostructure.Core.Strategy.Dag

universe uAmbient uBranch uData uVertex

/-- The only declaration type used by the official Graph boundary. -/
abbrev Declaration :=
  Core.Strategy.Dag.ProblemDeclaration.{uAmbient, uBranch, uData}

/-- Framework-derived opening definition for Graph proofs that begin by
selecting a minimal counterexample.  The application supplies only its
registered problem, target, and problem-owned branch-state initializer.
Graph contributes its canonical progress profile; Core contributes target
decision and the executable Strategy registration. -/
noncomputable def minimalCounterexampleDefinition
    (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P)
    (initialState : (object : P.Ambient) -> P.BranchState object)
    (reduction :
      Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T) :
    Core.ProblemDefinition.{uAmbient, uBranch, uData} where
  problem := P
  target := T
  initialState := initialState
  data := {
    targetDecidable := fun input =>
      Classical.propDecidable (T.Predicate input.object)
    counterexampleReductions := [reduction]
  }

instance minimalCounterexampleDefinition_hasSelection
    (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P)
    (initialState : (object : P.Ambient) -> P.BranchState object)
    (reduction :
      Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T) :
    NeZero
      (Core.StrategyData.counterexampleReductions
        (Core.ProblemDefinition.data
          (minimalCounterexampleDefinition P T initialState reduction))).length :=
  ⟨by simp [minimalCounterexampleDefinition]⟩

/-- Fully derived opening definition for minimum-degree cycle problems.
Graph constructs all three structural capabilities; the application provides
only its problem presentation, target semantics, and branch-state
initializer. -/
noncomputable def minimumDegreeCycleDefinition
    (k : Nat)
    (BranchState : Graph.FiniteObject.{uVertex} → Type uBranch)
    (Presentation : Type)
    (presentation : Presentation)
    (LengthOK : Nat → Prop)
    (T : Core.Target
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation))
    (targetBridge : ∀ object, T.Predicate object ↔
      Graph.HasCycleWithLength LengthOK object)
    (initialState : ∀ object, BranchState object) :
    Core.ProblemDefinition.{uVertex + 1, uBranch, 0} :=
  minimalCounterexampleDefinition
    (Graph.problemWithPresentation
      (Graph.MinimumDegreeAtLeast k) BranchState Presentation presentation)
    T initialState
    (Graph.Strategy.minimumDegreeCycleCounterexampleReduction
      k BranchState Presentation presentation LengthOK T targetBridge
      initialState)

instance minimumDegreeCycleDefinition_hasSelection
    (k : Nat)
    (BranchState : Graph.FiniteObject.{uVertex} → Type uBranch)
    (Presentation : Type)
    (presentation : Presentation)
    (LengthOK : Nat → Prop)
    (T : Core.Target
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation))
    (targetBridge : ∀ object, T.Predicate object ↔
      Graph.HasCycleWithLength LengthOK object)
    (initialState : ∀ object, BranchState object) :
    NeZero
      (Core.ProblemDefinition.data
        (minimumDegreeCycleDefinition k BranchState Presentation presentation
          LengthOK T targetBridge initialState)).counterexampleReductions.length :=
  ⟨by simp [minimumDegreeCycleDefinition, minimalCounterexampleDefinition]⟩

/-- Read the kernel-checked theorem from a declaration sealed by `ofDag%`.
The declaration retains its normalized DAG privately, so callers cannot
substitute a different program at theorem-extraction time. -/
noncomputable def statement
    (declaration : Declaration.{uAmbient, uBranch, uData}) :=
  declaration.report.statement.down

/-- Read-only static path of the exact DAG stored in the sealed declaration. -/
noncomputable def path
    (declaration : Declaration.{uAmbient, uBranch, uData}) :
    List StrategyKey :=
  declaration.report.path

/-- Read-only certificate artifact for the exact DAG stored in the sealed
declaration. -/
noncomputable def traceJson
    (declaration : Declaration.{uAmbient, uBranch, uData}) :
    Lean.Json :=
  declaration.report.traceJson

end Hypostructure.Graph.Strategy.Official.SealedDag
