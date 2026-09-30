import HypostructureErdos64EG.Problem
import HypostructureErdos64EG.Assembly
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
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

end HypostructureErdos64EG
