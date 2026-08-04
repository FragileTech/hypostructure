import Hypostructure.Core.Strategy.Official.Schema

/-!
# Callback-free official problem definition

This is the author-facing mathematical boundary for the sealed official
compiler.  It deliberately contains no strategy registry, runner, decider,
classifier, transition, closure, or theorem certificate.
-/

namespace Hypostructure.Core.Strategy.Official

universe uAmbient uBranch

/-- Documentation carried into reports without affecting execution. -/
structure ProblemMetadata where
  name : String := ""
  statement : String := ""
  source : String := ""
  deriving Repr, Inhabited

/-- A callback-free problem declaration.

The only function-valued fields are the mathematical baseline/target already
required by `Core.Problem`.  Official execution never reads
`problem.BranchState`: residual state is constructed by the owning framework
domain and retained in its typed terminals. -/
structure ProblemDefinition where
  problem : Core.Problem.{uAmbient, uBranch}
  target : Core.Target problem
  schema : ProblemSchema
  metadata : ProblemMetadata := {}

/-- Closed official strategy references are the only operation names accepted
by the future sealed official DAG frontend. -/
abbrev StrategyRef := Core.Strategy.OfficialRegistry.Ref

end Hypostructure.Core.Strategy.Official
