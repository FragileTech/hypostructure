# Build the DAG

`Dag.Blueprint` is a declarative, first-order description of proof
architecture. Authors provide one canonical `Program` entry and therefore one
runtime root and initial ledger. Vertices select sealed Strategies; Core
derives stages, contracts, residual transport, branch joins, semantic routes,
and work.

## Linear composition

Append sealed Strategy constructors from the single root. Repeated Strategies
are allowed. Each occurrence consumes the literal incoming residual and
complete accumulated ledger.

## Exhaustive branching

`dichotomy` receives complete typed continuations. Core selects the terminal,
retains its witness, and instantiates the corresponding continuation. Branches
do not create new runtime roots or exchange payloads. In the current fluent
syntax, a branch-local blueprint starts from neutral `Blueprint.root`; this
means “no preceding Strategy in this continuation” and never resets the
residual or ledger.

## Semantic autoroute

Targetless `Blueprint.autoroute` is the only author-facing route:

```lean
... |>.autoroute
```

There are no named blocks, string destinations, static expansion operations,
or author-selected target nodes.

The marker must terminate a branch with an enclosing structural continuation.
Core selects the first Strategy in the nearest such continuation. That entry
is the deepest compatible destination because later entries depend on its
ledger output. The author supplies no candidate, destination, equivalence,
priority, work value, or bridge.

Core appends a literal-residual bridge certificate to the incoming ledger.
Trace provenance records the Core-generated source and destination IDs and
depths, the singleton candidate set, literal relation, fixed work, and
framework bridge construction. Orphan and nonterminal markers are rejected.

## Names and documentation

Labels and notes are display metadata only. They cannot name destinations,
affect candidate ranking, provide capabilities, or alter execution.

## Seal and inspect

`ofDag% definition strategyDag` is the sole application entrypoint. It accepts
the one canonical `Program`, verifies semantic routes, executes the sealed
program, and returns a declaration only after every terminal closes. Reports
and paired PDF/JSON artifacts read the same certified route provenance.
