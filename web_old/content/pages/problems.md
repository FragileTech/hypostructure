# Define a Problem

A problem definition is the complete mathematical registration consumed by the DAG runner. Applications provide data and proofs here; they do not construct contracts, ledgers, stages, or compiler recipes.

## Core.Problem

`Ambient` is the family of objects under study. `Baseline` records which objects are theorem inputs. `BranchState` stores application-level state chosen at the boundary. Keep it mathematical and stable; accumulated proof evidence belongs to Core.

## Core.Target

`Predicate` is the property strategies test on one ambient object. `Statement` is the public theorem. The two conversion fields show that the object-level closure and theorem statement express the same result under the baseline.

## Strategy.ProblemInput

Core packages an ambient object, its baseline proof, and its initial branch state into the first residual. Every registered family is indexed by this stable input, and the compiler lifts it through later accumulated stages.

## Core.StrategyData

Register only the families the DAG will use. Each list position is a stable architecture index: `.responseClassifier 1` means the second `ResponseData`, not a runtime value. `targetDecidable` powers early target closure and frontend certification.

## Core.ProblemDefinition

The final record contains `problem`, `target`, `initialState`, `data`, and optional documentation metadata. It contains no execution callbacks beyond the mathematical finite searches and classifiers inside registered strategy data.

## Frontend validation

The sealed frontend rejects banal or object-independent targets, false baselines, unregistered strategy indices, invalid Programs, and registrations that cannot certify the target. Treat these messages as API diagnostics, not obligations to bypass.
