import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Erdős–Gyárfás as a Hypostructure application

This is the library root and the package's default target.

The application entrypoint imports exactly the problem presentation and the
generic exact-ledger continuation surface:

- `Problem` -- the pinned public statement, one Core problem, one Core target,
  and the one record of registered data the framework's entry spine reads.
  This is where the problem's own inputs live: the Hegde--Sandeep--Shashank
  theorem (via `WindowAlgebra`) and the audited finite curvature table (via
  `FiniteChecks.P13Barrier`).  The framework reads them from here and names
  neither.
- `Graph.Strategy.SpineContinuationRun` -- the framework-owned direct
  `ExactLedger` runner surface.  The package root does not depend on the sealed
  StrategyDag frontend.

`WindowAlgebra` and `FiniteChecks.P13Barrier` are supporting inputs of
`Problem` rather than entry points, so they are reached through it.

The legacy registration layer -- `Official/Definition.lean`,
`Official/Problem.lean`, `Official/StructuralProgram.lean`,
`Official/ClosureProbe.lean`, the `AB/` directory and `Presentation.lean` --
built a `Core.ProblemDefinition`: a registry of parallel capability lists whose
entries were resolved by list position.  The canonical API replaces that
outright, so the layer was deleted rather than carried; it remains in git
history.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Final aggregation boundary for the EG application.

The theorem consumes exactly the framework-owned selected exact ledger.  The
remaining proof obligation is the end-to-end branch contradiction on that same
ledger; once the generic spine proves it unconditionally, `erdos_64` is the
same statement with this argument supplied.
-/
theorem erdos_64_of_selectedContradiction
    (closeSelected :
      ∀ {current : Hypostructure.Graph.Strategy.Spine.Input
          BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData.{u}},
        Hypostructure.Core.Residual.ExactLedger
          (Hypostructure.Graph.Strategy.Spine.Input
            BranchState Graph.ReceiverLoad.LoadCapacityProfile
            erdosReceiverLoadProfile spineData.{u})
          current
          [Hypostructure.Graph.Strategy.Spine.K
            (data := spineData.{u}) .selection] →
        False) :
    OfficialStatement.{u} :=
  letI :=
    Hypostructure.Graph.Strategy.Spine.factSystem
      BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData.{u}
  let spineTarget :
      Core.Target
        (Hypostructure.Graph.Strategy.Spine.problem
          BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData.{u}) :=
    Graph.minimumDegreeCycleTarget spineData.threshold
      BranchState
      Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
      spineData.LengthOK (fun exponent => exponent ≥ 2)
      (fun exponent => 2 ^ exponent) powerOfTwoLength_iff
  spineTarget.target_to_statement (by
    intro object baseline
    by_contra avoids
    let input :
        Hypostructure.Graph.Strategy.Spine.Input
          BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData.{u} :=
      { object := object
        baseline := baseline
        branchState := () }
    let opened :=
      Hypostructure.Core.Strategy.openMinimalCounterexampleScope
        spineTarget
        (Hypostructure.Graph.Strategy.Spine.progress
          BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData.{u})
        (fun _object => ())
        (Hypostructure.Graph.Strategy.Spine.K
          (data := spineData.{u}) .selection)
        (fun context =>
          .up ⟨context.avoids, fun smaller smallerLt baseline =>
            context.minimal smaller smallerLt baseline⟩)
        input avoids
    exact closeSelected opened.history)

end HypostructureErdos64EG
