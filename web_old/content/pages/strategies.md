# Compose framework strategies

Application authors register the mathematical problem and compose the strategies exposed by `Hypostructure.Core.Strategy.Dag`. Each strategy is a reusable proof move with a typed input, an exhaustive result, and a precise continuation interface.

## The authoring flow

Start with `Blueprint.root`, append fluent strategy constructors, wrap the result with `Program.ofBlueprint`, and pass the Program and its `Core.ProblemDefinition` to `ofDag%` or `reduceDag%`.

## Read the current residual

Every strategy reads the literal predecessor residual and the complete accumulated ledger. Its page lists the registration facts supplied by the problem, the predecessor capabilities consumed at that vertex, and the facts added to the ledger.

## Compose linear results and alternatives

Linear strategies append one result and continue. Binary and finite alternatives retain the selected witness and run the corresponding branch Blueprint. Shared continuations receive the typed join constructed by Core.

## Follow dependent chains

The counterexample reduction has five stages. Each stage returns the dependent input required by the next stage, and `interfaceReplacementClosure` returns the completed chain to the ordinary Blueprint API.

## Read the theorem

`ofDag% definition strategyDag` produces the theorem at `problemDefinition.report.statement.down`. `reduceDag% definition strategyDag` produces the corresponding target-or-residual statement for a reduction with live terminals.
