import HypostructureErdos64EG.Official.StructuralProgram
import HypostructureErdos64EG.Official.ClosureProbe
import HypostructureErdos64EG.AB.Execution

/-!
# Erdős–Gyárfás as a Hypostructure application

This is the library root and the package's default target.  It pulls in the
three entry points that constitute the development, and nothing else:

* `Official.StructuralProgram` -- the official problem, its registered strategy
  data, and the sealed `reduceDag%` reduction whose JSON certificate is
  exported for the validator.
* `Official.ClosureProbe` -- the strict `ofDag%` frontend, which accepts the
  declaration only when no residual survives.  This is the honest closure test:
  `reduceDag%` retains residuals and therefore succeeds whatever remains open.
* `AB.Execution` -- the Type-A/Type-B frontier reduction against the single
  disjunctive target `OfficialTarget ∨ GlobalTypeA ∨ GlobalTypeB`.

Both runs share one authored topology, the `erdosOfficialBlueprint%` macro in
`HypostructureErdos64EG.StrategyDag`, so the official and A/B registries cannot
drift apart.

Everything reachable from here is live.  The per-node modules of the earlier
`NodeN.lean` development, together with the contract, fixture and workflow
modules that supported them, were removed once the framework-native
registration replaced them; they remain in git history.
-/
