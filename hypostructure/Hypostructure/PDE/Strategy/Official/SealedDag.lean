import Hypostructure.Core.Strategy.Dag
import Hypostructure.PDE.Strategy.CounterexampleLocalization
import Hypostructure.PDE.Strategy.RegularityStratification

/-!
# Sealed DAG boundary for official PDE proofs

The PDE specialization does not own an executor.  An official PDE proof is
registered as a `Core.ProblemDefinition`, described by a key-only
`Dag.Program`, and sealed by Core's `ofDag%` frontend.  This module exposes no
dispatch, merge, runtime result, application callback or alternate execution
path --- exactly as `Graph/Strategy/Official/SealedDag.lean` does for graphs.

An interior-regularity proof opens the same way every time: Core selects the
minimal counterexample, which for a regularity target *is* a singularity
(`PDE/Singularity.lean`), and the framework's own localization profiles it on
a nested window tower around that point.  Neither step is application data, so
both are pre-populated here.
-/

namespace Hypostructure.PDE.Strategy.Official.SealedDag

open Hypostructure
open Hypostructure.Core.Strategy.Dag

universe u

/-- The only declaration type used by the official PDE boundary. -/
abbrev Declaration := Core.Strategy.Dag.ProblemDeclaration.{u, u, 0}

/--
**Framework-derived opening definition for a represented PDE proof.**

The application supplies its local model, its target, its problem-owned
branch-state initializer, and the ordered stratification it wants walked.  The
framework contributes target decision and the canonical counterexample
localization, which is the step that turns the selected minimal counterexample
into a local residual on a window tower.

No route, dispatcher, executor result or terminal is contributed by anyone.
-/
noncomputable def localRegularityDefinition
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (metadata : Core.ProblemMetadata := {}) :
    Core.ProblemDefinition.{u, u, 0} where
  problem := M.problem
  target := T
  initialState := initialState
  data := {
    targetDecidable := fun input =>
      Classical.propDecidable (T.Predicate input.object)
    dichotomies := dichotomies
    counterexampleLocalizations :=
      [PDE.Strategy.CounterexampleLocalization.registration M T] }
  metadata := metadata

instance localRegularityDefinition_hasLocalization
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (metadata : Core.ProblemMetadata) :
    NeZero
      (Core.StrategyData.counterexampleLocalizations
        (Core.ProblemDefinition.data
          (localRegularityDefinition M T initialState dichotomies metadata))).length :=
  ⟨by simp [localRegularityDefinition]⟩

/--
**The same, with a registered component/pressure split.**

An elliptic system splits its selected residual into a local child and its
complementary tail before the stratification runs; that vertex is
`Core.AtomContextObstructionDichotomyData`, produced by
`PDE/Strategy/AtomContextObstructionDichotomy.lean` from the application's
public presentation and elliptic constraint.
-/
noncomputable def localRegularityWithSplitDefinition
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (split : Core.AtomContextObstructionDichotomyData.{u, u, 0} M.problem)
    (metadata : Core.ProblemMetadata := {}) :
    Core.ProblemDefinition.{u, u, 0} where
  problem := M.problem
  target := T
  initialState := initialState
  data := {
    targetDecidable := fun input =>
      Classical.propDecidable (T.Predicate input.object)
    dichotomies := dichotomies
    atomContextObstructionDichotomies := [split]
    counterexampleLocalizations :=
      [PDE.Strategy.CounterexampleLocalization.registration M T] }
  metadata := metadata

instance localRegularityWithSplitDefinition_hasLocalization
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (split : Core.AtomContextObstructionDichotomyData.{u, u, 0} M.problem)
    (metadata : Core.ProblemMetadata) :
    NeZero
      (Core.StrategyData.counterexampleLocalizations
        (Core.ProblemDefinition.data
          (localRegularityWithSplitDefinition M T initialState dichotomies split
            metadata))).length :=
  ⟨by simp [localRegularityWithSplitDefinition]⟩

instance localRegularityWithSplitDefinition_hasSplit
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (split : Core.AtomContextObstructionDichotomyData.{u, u, 0} M.problem)
    (metadata : Core.ProblemMetadata) :
    NeZero
      (Core.StrategyData.atomContextObstructionDichotomies
        (Core.ProblemDefinition.data
          (localRegularityWithSplitDefinition M T initialState dichotomies split
            metadata))).length :=
  ⟨by simp [localRegularityWithSplitDefinition]⟩

/--
**Framework-derived opening definition for a canonically registered
no-singularity problem.**

The mirror of `Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition`.
Where the graph opener installs the counterexample *reduction* it builds from a
target bridge, this one installs the reduction
`PDE.Strategy.Registry.CounterexampleReduction.counterexampleReduction` builds
from the balanced system --- so a PDE proof opens with the same four vertices a
graph proof does (`targetAlgebraReduction`, `minimalSubobjectExclusion`,
`criticalModificationStructure`, `interfaceReplacementClosure`) rather than with
a bare localization.

The application supplies its model, target, branch-state initializer, the
stratification's dichotomy list and the reduction; it writes no bridge and no
proof.
-/
noncomputable def noSingularityDefinition
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (reduction : Core.CounterexampleReductionData.{u, u, 0} M.problem T)
    (metadata : Core.ProblemMetadata := {}) :
    Core.ProblemDefinition.{u, u, 0} where
  problem := M.problem
  target := T
  initialState := initialState
  data := {
    targetDecidable := fun input =>
      Classical.propDecidable (T.Predicate input.object)
    dichotomies := dichotomies
    counterexampleLocalizations :=
      [PDE.Strategy.CounterexampleLocalization.registration M T]
    counterexampleReductions := [reduction] }
  metadata := metadata

instance noSingularityDefinition_hasLocalization
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (reduction : Core.CounterexampleReductionData.{u, u, 0} M.problem T)
    (metadata : Core.ProblemMetadata) :
    NeZero
      (Core.StrategyData.counterexampleLocalizations
        (Core.ProblemDefinition.data
          (noSingularityDefinition M T initialState dichotomies reduction
            metadata))).length :=
  ⟨by simp [noSingularityDefinition]⟩

instance noSingularityDefinition_hasReduction
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (initialState : (object : M.problem.Ambient) → M.problem.BranchState object)
    (dichotomies : List (Core.DichotomyData.{u, u, 0} M.problem T))
    (reduction : Core.CounterexampleReductionData.{u, u, 0} M.problem T)
    (metadata : Core.ProblemMetadata) :
    NeZero
      (Core.StrategyData.counterexampleReductions
        (Core.ProblemDefinition.data
          (noSingularityDefinition M T initialState dichotomies reduction
            metadata))).length :=
  ⟨by simp [noSingularityDefinition]⟩

/-! ## Sealed readers

The three projections an official boundary may expose.  None of them can run
anything: a `ProblemDeclaration` is produced only by Core's `ofDag%`.
-/

/-- The registered statement of a sealed declaration. -/
noncomputable def statement (declaration : Declaration.{u}) :=
  declaration.report.statement

/-- The strategy path the sealed declaration walked. -/
noncomputable def path (declaration : Declaration.{u}) :
    List Core.Strategy.Dag.StrategyKey :=
  declaration.report.path

end Hypostructure.PDE.Strategy.Official.SealedDag
