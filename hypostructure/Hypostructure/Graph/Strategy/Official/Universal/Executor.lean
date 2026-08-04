import Hypostructure.Graph.Strategy.Official.SealedDag

/-!
# No alternate universal Graph executor

This compatibility import location intentionally exports no `execute`,
`dispatch`, `merge`, runtime `Result`, or application-visible state.  Official
Graph proofs are sealed by `ofDag%` and their theorem is read from the exact
stored declaration through `SealedDag.statement`.
-/

namespace Hypostructure.Graph.Strategy.Official.Universal.Executor

open Hypostructure

universe uAmbient uBranch uData

abbrev Declaration :=
  Strategy.Official.SealedDag.Declaration.{uAmbient, uBranch, uData}

noncomputable def statement
    (declaration : Declaration.{uAmbient, uBranch, uData}) :=
  Strategy.Official.SealedDag.statement declaration

end Hypostructure.Graph.Strategy.Official.Universal.Executor
