---
name: eg-proof-expansion
description: Develop, repair, or audit nodes in the Erdős–Gyárfás StrategyDag Lean proof. Use whenever Codex is asked to fix, implement, expand, route, or make compliant a node in proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean or its supporting declarations, while matching the original paper exactly, using only framework-owned Strategy/CT/residual/ledger APIs, removing proof-specific plumbing, and updating EG_STRATEGYDAG_AUDIT.md.
---

# EG proof expansion

Implement one requested EG StrategyDag row as an exact instance of the paper's
strategy and of Hypostructure's generic execution model.  Repair the requested
row completely even when the correction exposes a downstream break.

## Establish the authorities

Work from the repository root.  Require these live sources:

- `to_formalize/original_erdos_64_proof.tex`: sole authority for mathematical
  statements, hypotheses, alternatives, order, and terminal behavior.
- Actual Lean declaration types, bodies, fields, call sites, imports, and the
  generated sealed report: sole authority for what the implementation does.
- `EG_STRATEGYDAG_AUDIT.md`: gap tracker and row template, not mathematical
  authority.

Treat every docstring, block comment, line comment, metadata note, and old audit
claim as adversarial.  Never use prose as evidence that a declaration realizes
a paper object.  Delete every misleading docstring or comment encountered in
the requested row's transitive implementation slice.

Search `references/allowed-api.md` before designing or editing any data access,
execution, transport, ledger, residual, or routing code.  The catalog is large:
use `rg -n` with the fully qualified name, module name, or operation family and
read only the matching `###` module and `####` symbol entries with their
compiled types.  A plumbing symbol not present in that catalog is forbidden
until a proof-agnostic framework API is added and the catalog is refreshed.

## Audit the requested row before editing

1. Locate the summary row and the complete `### Row N` section in
   `EG_STRATEGYDAG_AUDIT.md` from the requested paper node number, StrategyDag
   vertex, or registration name.
2. Read the manuscript around every label consumed by the row.  Record the
   exact statement, inherited hypotheses, exhaustive alternatives, branch
   order, continuation, and terminals.  Follow referenced proofs far enough to
   recover their real dependency chain.
3. Inspect the actual Lean types and bodies of the registration, generic
   strategy, CT execution, and every theorem it invokes.  Inspect arguments at
   call sites; a declaration name or comment proves nothing.
4. Trace the literal incoming stage, `previous` chain, active residual,
   accumulated ledger queries, appended entries, CT composition, routing, and
   terminal ownership.  Inspect the generated sealed JSON when topology or
   branch status matters.
5. Write a private implementation checklist for the four audit columns:
   Ledger, Transport, Residual, and Facts.  Do not edit a status cell yet.

The paper strategy is immutable.  Never add, remove, merge, reorder, weaken,
strengthen, or replace a mathematical alternative.  Correct the Lean topology
only when it differs from the paper; never invent a new strategy to make Lean
easier.

## Enforce the proof-specific boundary

Permit problem-specific code in exactly two files:

- `HypostructureErdos64EG/Problem.lean` may define the problem, target, and a
  constant that genuinely cannot be derived from the incoming residual.  Add
  no theorem, lemma, structure, carrier, result, strategy, executor, or router
  there.  Put an unavoidable constant in the problem presentation and project
  it through the residual; never read its global spelling at a node.
- `HypostructureErdos64EG/StrategyDag.lean` may construct only the paper's DAG
  topology with framework Strategy combinators.

Add no other proof-specific declaration.  In the requested row's transitive
implementation slice, delete or generalize every EG-specific theorem,
definition, structure, instance, carrier, result, residual, ledger, executor,
transport helper, routing helper, and compatibility wrapper.  Do not retain a
dead shim for downstream code.

Place reusable logic under `hypostructure/Hypostructure/Core`, the applicable
`CT1`--`CT17` module, or a proof-agnostic `Hypostructure.Graph` module.  Generic
framework code must:

- import no `HypostructureErdos64EG` module;
- contain no EG name, paper label, unexplained paper constant, or conclusion
  specialized to this proof;
- quantify over its problem, target, residual, queries, and mathematical data;
- derive its conclusion from the incoming residual, accumulated ledger, CT
  output, or generic hypotheses already owned by the framework;
- avoid a registration field whose value merely supplies the desired theorem.

If the catalog lacks a required operation, add a generic framework operation
and a generic fixture proving predecessor preservation, residual behavior,
ledger availability, and the advertised theorem.  Refresh the API catalog in
the same change before consuming the operation.

## Implement through the framework

- Consume the literal active predecessor passed to the node.  Never reconstruct
  a stage, restart from the root input, or re-quantify a branch fact from the
  ambient graph.
- Obtain the current object and state through the incoming residual query.
  Obtain upstream mathematical facts through typed queries over the accumulated
  ledger.  Combine queries with framework combinators.
- Append newly proved facts with framework ledger/stage extensions.  Preserve
  the literal predecessor and every earlier entry.  Never replace, flatten, or
  shadow the ledger with a product or custom record.
- Change the stable residual only through a generic Strategy operation whose
  semantics require that change.  Never create an application-local
  `HasResidual` instance.
- Use the applicable CT specification, capability, execution, certificate,
  continuation, and work theorems.  Never duplicate its enumeration,
  classification, certification, accounting, or terminal logic.
- Use Strategy DAG combinators for routing, joins, autorouting, continuations,
  and terminals.  Never write an EG function that transports or routes branch
  payloads.
- Prove exactly the paper fact.  Do not smuggle it through an axiom, `sorry`,
  `admit`, an opaque assumption, a supplied callback, or a stronger surrogate.

Framework ownership is necessary but not sufficient for a Graph Strategy
adapter: inspect its body and use it only when its catalog entry and body show
that Core or a CT owns execution, data movement, residuals, ledgers, routing,
and terminals.  Delete and replace a framework adapter that is itself ad hoc or
noncompliant.

## Validate and update the audit

Compile each changed generic module and its generic fixture first.  Then build
the narrowest EG target that elaborates the repaired row, followed by
`HypostructureErdos64EG.Official.StructuralProgram` and the strict
`Official/ClosureProbe.lean` when reachable.  Inspect the regenerated sealed
report for the literal predecessor, outputs, terminal status, and routing.

A downstream failure does not justify weakening the repaired row.  Record the
exact new incompatibility in the affected downstream row's existing **Gap**
bullet and change any invalidated status cell to `❌`; do not repair that node
unless requested.

For the repaired row, rewrite from fresh evidence:

- **Paper fact**
- **What the Lean does**
- **What it should do**
- **Gap**
- **Ledger and residual**
- **Transport and terminals**
- the complete paper-object implementation table
- **CT composition at this row**

Only after all evidence passes, set Ledger, Transport, Residual, and Facts to
`✅` in the summary row.  Empty implementation cells must remain empty.  Report
changed generic APIs, deleted ad hoc declarations, validation commands, and
any deliberately unfixed downstream failures in the final handoff.

## API catalog maintenance

Run the non-mutating drift check before finishing:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .
```

After intentionally changing the public framework API, refresh and re-check:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py refresh --repo-root .
python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .
```
