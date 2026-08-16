# Getting started

Build one complete, kernel-checked Hypostructure declaration. This example is intentionally small, but it uses the same public boundary as a Graph theorem, a represented PDE argument, or a large routed proof.

## 1. Define the problem

`Core.Problem` separates ambient objects, the baseline assumption, and the branch state carried at the theorem boundary. The branch state is application data; it is not an execution ledger.

## 2. Define the target

`Core.Target` connects the object-level predicate used by strategies with the theorem-level `Statement`. Both conversion laws are explicit, so the final report returns exactly the registered theorem.

## 3. Register strategy data

`Core.ProblemDefinition` packages the problem, target, initial state, and `StrategyData`. Every indexed Blueprint key must resolve to an entry in the matching registered list.

## 4. Compose and seal the DAG

The Blueprint is pure key-only syntax. `ofDag%` checks target honesty, strategy registration, Blueprint compliance, and target certification before constructing the sealed `ProblemDeclaration`.

## 5. Read the certified theorem

Use `problemDefinition.report.statement.down`. Diagnostics such as `path`, `proofTrace`, `checksBound`, `workBound`, and `describe` are report projections; they do not replace the theorem.
