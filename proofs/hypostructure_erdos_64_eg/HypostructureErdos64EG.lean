import HypostructureErdos64EG.Problem
import HypostructureErdos64EG.StrategyDag

/-!
# Erdős–Gyárfás as a Hypostructure application

This is the library root and the package's default target.

The application is exactly two modules:

* `Problem` -- the pinned public statement, one Core problem, one Core target,
  and the one record of registered data the framework's entry spine reads.
  This is where the problem's own inputs live: the Hegde--Sandeep--Shashank
  theorem (via `WindowAlgebra`) and the audited finite curvature table (via
  `FiniteChecks.P13Barrier`).  The framework reads them from here and names
  neither.
* `StrategyDag` -- the authored topology.  Its single endpoint, `strategyDag`,
  roots Block A on `Graph.Strategy.Spine` at this problem's registered data,
  with Figure 8's Type A exit list and node `[19]`'s sparse surplus branch
  attached.  It declares nothing else: the file authors topology, and every
  statement it needs is the framework's.

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
