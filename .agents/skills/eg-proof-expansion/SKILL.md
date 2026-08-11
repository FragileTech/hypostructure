---
name: eg-proof-expansion
description: Develop, repair, or audit nodes in the Erdős–Gyárfás StrategyDag Lean proof. Use whenever Codex is asked to fix, implement, expand, route, or make compliant a node in proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean or its supporting declarations, while matching the original paper exactly, using only the canonical ExactLedger and sealed Strategy/CT APIs, removing proof-specific plumbing, and synchronizing the label and node tables in Assembly_node_audit.md.
---

# EG proof expansion

Implement one requested EG StrategyDag row as an exact instance of the paper's
strategy and of Hypostructure's generic execution model.  Repair the requested
row completely even when the correction exposes a downstream break.

## Keep the task to one requested label

This is the controlling workflow. Apply every broader audit, dependency,
cleanup, and framework instruction below only inside this scope.

1. Identify the single manuscript label explicitly requested by the user. If
   the user names a node, use the live tables to identify its single first
   failing label. Do not begin a second label in the same turn.
2. Copy that label's exact proposition, inherited hypotheses, alternatives,
   and proof strategy from the manuscript. Do not infer a stronger
   prerequisite, global version, replacement theorem, or different strategy.
3. Identify only the facts already present on the literal incoming residual
   that the manuscript proof consumes. Read them only through
   `FactInputs.current` and `FactInputs.get` inside the executor. Never request
   a sibling fact, ambient theorem parameter, callback, side carrier, supplied
   certificate, or detached universal proof.
4. Translate that one proof into Lean. Publish each externally usable
   conclusion prescribed for that label in one literal `FactManifest`, and
   append it with `AtomicCT.run` to the same `ExactLedger`.
5. Delete an illegal wrapper, callback, side carrier, or compatibility shim
   only while repairing the valid mathematical proof it transported to use
   the canonical ledger API. Never delete, weaken, broaden, or replace a
   correct paper fact merely because its current transport is illegal.
6. Update exactly the corresponding paper-fact row and node row from the
   kernel-checked implementation. Build the narrow target and report the first
   downstream failure. Stop there unless the user explicitly requests the
   next label.

Dependency tracing is diagnostic and read-only. It never expands the edit
scope. A missing downstream interface, inconvenient schema, or compiler error
does not authorize a new API, mathematical certificate, carrier, strategy, or
repair of another label. Do not speculate about such designs. State the exact
requested formula that remains unproved and implement it with a permitted
Type A pattern.

### Ban detached proof declarations

Implement the selected paper fact only as the value returned for its declared
`Produces` key by the sealed atomic executor. Keep its proof as an anonymous
tactic or term subexpression inside that executor. Do not declare a `theorem`,
`lemma`, helper `def`, public conversion, quotient-system constructor, or other
standalone declaration whose conclusion supplies, implies, packages, or
reconstructs the selected fact. This prohibition applies even when the
declaration is generic, mathematically true, reusable, or convenient to test.

Before editing, name the exact existing atomic row that will own the proof. If
no such row exists, create only the permitted Type A row and its vocabulary
entry; do not first stage the mathematics in a detached declaration. Construct
all temporary mathematical objects with local `let` or `have` bindings inside
the executor from `inputs.current` and `inputs.get` facts.

Before compiling or updating the audit tables, inspect the complete diff for
new top-level declarations. If any new declaration outside the vocabulary and
Type A row carries mathematical content for the selected label, the repair is
invalid: delete it, inline its proof into the executor, and repeat the diff
inspection. Never report the fact as implemented while such a declaration
exists. A downstream elaboration failure after its removal is the required
loud failure, not permission to restore the declaration.

### Never confuse mathematical data with a transport interface

There is exactly one proof-data interface: the incoming `ExactLedger`, read by
sealed `FactInputs` and extended by `AtomicCT.run`. Mathematical structures
such as quotients, families, coordinates, witnesses, and certificates are
objects appearing inside propositions; they do not authorize another channel
and must never be described as a second interface.

When a paper proof needs such an object, obtain its prerequisites from the
incoming ledger, construct the object locally in the executor, prove the exact
paper proposition, and return that proposition under its declared semantic
key. If the object must be used later, make it part of that key's exact `Holds`
proposition and publish it in `Produces`; do not pass it separately.

Never respond to an awkward mathematical schema by proposing, requesting, or
waiting for permission to add an interface, source certificate, carrier,
wrapper, callback, theorem parameter, or compatibility layer. Never call such
a proposal a prerequisite or blocker. Either the existing mathematical
declarations suffice for the local proof, or delete the illegal transport,
repair the proof as far as the canonical ledger permits, and let the first
unresolved Lean obligation or downstream compilation failure remain loud.

Do not delete valid mathematics when deleting illegal transport. Reconstruct
and publish the same paper fact through the ledger. Do not replace it with a
surrogate, a universally quantified detached theorem, or a stronger fact that
bypasses the manuscript argument.

This section overrides every broader paragraph below. In particular, “repair
the row completely”, “transitive implementation slice”, “follow referenced
proofs”, and “inspect every theorem” do not authorize edits outside the
selected label or changes to the manuscript's proof strategy.

## Establish the authorities

Work from the repository root.  Require these live sources:

- `to_formalize/original_erdos_64_proof.tex`: sole authority for mathematical
  statements, hypotheses, alternatives, order, and terminal behavior.
- Actual Lean declaration types, bodies, fields, call sites, imports, and the
  generated sealed report: sole authority for what the implementation does.
- `Assembly_node_audit.md`: sole authority for current Lean implementation
  status, wiring, ledger compliance, and the next unresolved work. Its two
  implementation tables are live; its stable rubrics are explanatory.

Treat every docstring, block comment, line comment, metadata note, and old audit
claim as adversarial. Never use prose as evidence that a declaration realizes
a paper object. Within the selected label only, correct a misleading comment
when the implementation edit would otherwise leave it false. Do not perform a
transitive comment cleanup.

Search `references/allowed-api.md` before designing or editing any data access,
execution, transport, ledger, residual, or routing code.  The catalog is large:
use `rg -n` with the fully qualified name, module name, or operation family and
read only the matching `###` module and `####` symbol entries with their
compiled types. A plumbing symbol not present in that catalog is forbidden for
the label implementation. Do not add an API to make a proposed design legal.

The catalog is a closed allowlist, not a list of suggestions.  Declarations
outside it are unavailable for proof plumbing.  Run the
catalog check before inspecting or editing a row; it also rejects noncanonical
plumbing already written directly in `StrategyDag.lean`.

## Audit the requested row before editing

1. Locate every affected row in both `Assembly_node_audit.md` tables: the
   `Paper-fact implementation table` by manuscript label and the
   `Node-by-node table` by diagram node. Run the table checker before relying
   on either table:

   ```bash
   python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check \
     --repo-root .
   ```
2. Read the manuscript around every label consumed by the row.  Record the
   exact statement, inherited hypotheses, exhaustive alternatives, branch
   order, continuation, and terminals.  Follow referenced proofs far enough to
   recover their real dependency chain.
3. Inspect the actual Lean types and bodies of the registration, generic
   strategy, CT execution, and every theorem it invokes.  Inspect arguments at
   call sites; a declaration name or comment proves nothing.
4. Trace the literal incoming `ExactLedger`, its immutable ancestry, indexed
   active residual, complete exact-key list, CT/Strategy manifests, commits,
   routing, and closure facts.  Inspect the generated sealed JSON
   when topology or branch status matters.
5. Write a private checklist for every affected table column. At the label
   level cover tactic, Lean declaration, partial match, kernel check,
   residual locality, ledger reads/writes, wiring, legality, and hardcoded
   facts. At the node level cover implementation, combinator, CT ownership,
   reachability, wiring, locality, registration, illegal carriers,
   manuscript difference, kernel check, and manuscript labels. Do not edit a
   cell before collecting fresh evidence.

### Report failures by the two live table rows

Every explanation of a missing fact, noncompliant node, compilation break, or
next repair must identify both live audit rows before drawing a conclusion:

- name the diagram row as `Node [n]`, reproduce its exact mathematical output,
  and cite the node table's current implementation, wiring, registration, and
  kernel-check cells;
- name every corresponding manuscript-label row in the paper-fact table and
  cite its current Lean declaration, partial-match assessment, ledger write,
  wiring, legality, and hardcoded-fact cells;
- state the first exact proposition or witness that Lean does not currently
  establish.  Write its complete mathematical formula and all objects it is
  quantified over; never report only a node range, umbrella theorem, generic
  dependency, or downstream symptom;
- classify the defect precisely as one of: mathematical proof absent,
  mathematical statement weakened/strengthened, fact proved but not published,
  fact published under the wrong schema, fact published but not wired, illegal
  read/write or carrier, wrong branch ancestry, or downstream interface
  mismatch.  Do not conflate these categories;
- distinguish the first failing audit row from later facts that merely cannot
  be derived because of it.  A compiler error at a later line is not the first
  mathematical gap when an earlier table row is absent or incorrectly
  implemented;
- if the two tables disagree with the inspected Lean source, update both table
  rows from fresh evidence before using them to answer.  Never silently replace
  the tables with an informal diagnosis.

The final answer for any audit or failure question must lead with this exact
row-and-fact identification.  It may then explain prerequisites and downstream
effects, but those effects must not be presented as additional missing facts
unless their own table rows independently fail.

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

Add no other proof-specific declaration. Within the selected label, replace
only the illegal carrier, callback, transport helper, routing helper, or
compatibility wrapper directly used to move that label's mathematical facts.
Repair those facts onto the canonical ledger before removing their illegal
transport. Do not delete or generalize unrelated declarations in a transitive
slice, and do not retain a dead shim for downstream code.

Place reusable logic under `hypostructure/Hypostructure/Core`, the applicable
`CT1`--`CT17` module, or a proof-agnostic `Hypostructure.Graph` module.  Generic
framework code must:

- import no `HypostructureErdos64EG` module;
- contain no EG name, paper label, unexplained paper constant, or conclusion
  specialized to this proof;
- quantify over its problem, target, residual, semantic fact keys, and
  mathematical data;
- derive its conclusion from the incoming residual, accumulated ledger, CT
  output, or generic hypotheses already owned by the framework;
- avoid a registration field whose value merely supplies the desired theorem.

If the catalog lacks an operation apparently needed by a proposed design,
reject that design and return to the manuscript proof and permitted Type A
forms. Do not add a generic framework operation while implementing a paper
label. This skill never changes or adds a proof-data interface.

## Enforce one canonical history

`Core.Residual.ExactLedger` is the only proof-history and residual carrier.
The accepted execution boundary consists only of `RefinementSystem`, the
residual domain's sole `FactSystem`, `FactManifest`, sealed `FactInputs`, and
`AtomicCT.run`.  Reject any other history, lookup, stage, store, flow, query,
product, sigma, custom record, callback, or route payload that transports a
fact.  Never use a producer path, predecessor depth, row number, display name,
or execution order as a fact lookup key.

Every CT and Strategy must declare a nonempty-output `FactManifest`.  Its
executor receives only sealed `FactInputs`, reads prerequisites with
`FactInputs.get`, returns exactly `manifest.Produces`, and commits through the
framework-owned atomic runner.  CT and Strategy outputs are the same indexed
`ExactLedger` type: the output index is definitionally `Produces ++ known`.
There is no payload, terminal, query, or audit-metadata channel for
mathematical information.  A branch decision needed downstream is a fact.

`AtomicCT` and its `AtomicStrategy` alias have no predecessor type parameter.
Define one executor once and run that same value after any canonical branch
cursor for which all declared requirements are available.  Never specialize a
CT to a producer, row, predecessor shape, or authored execution position.
Both names use the one `AtomicCT.run`; there is no Strategy wrapper, duplicate
runner, conversion, or second output type.

Every named, semantically meaningful, or reusable theorem, certificate,
witness, bound, classification, and branch decision proved by a CT or Strategy
belongs in `Produces`, including facts used only by another output proof.  The
exact heterogeneous result type must make omission or an undeclared output
fail to elaborate.  An anonymous tactic subterm used solely to construct one
declared fact is part of that fact rather than an independent ledger entry;
this is the only local-proof exception.

Residual changes must supply `RefinementSystem.Refines next current`.  Each
residual domain has one closed, decidable `FactSystem.Key` vocabulary; that
system assigns every key exactly one value schema, one injective audit name,
and one refinement transport.  This is the formal reason same-named schema
spoofing is impossible and every upstream fact remains applicable on a
descendant.  A fact that is not refinement-stable cannot be a ledger fact.

Adding a key to `Graph.Strategy.Spine.Key` means six entries, all in
`SpineVocabulary.lean`: the `Holds` branch, `label`, `idx`, `ofIdx`, `name`, and
a `LabelPins` line.  Omitting any one is a compile error, never a silent gap.
Give `idx` the next unused number and never renumber an existing key, including
when the new constructor is inserted mid-list: the audit name carries the index,
so renumbering rewrites the emitted names of unrelated facts.  `label` is the
constructor's own name, which is what its `LabelPins` line pins.  Keep `name`
written out as a literal `.num (.str ... "label") idx`; spelling it out is what
lets a downstream audit proof unfold it once instead of three times, and
`name_eq` is what ties the spelling back to `label` and `idx`.

Injectivity of the audit names comes from the index, through `ofIdx_idx`,
`idx_injective`, and `name_eq`.  A duplicated or missing index fails to
elaborate.  Never prove `name_injective` by case analysis over pairs of keys: it
is quadratic in the vocabulary size and will not survive the rows still to come.

Name a fact in an audit assertion as `(name .key)`, never as a `Lean.Name`
literal, so the assertion is indifferent to how a name is spelled.  Rule names
passed to `factOnly` stay literal -- those are strategy labels, not facts.

The sole exception is framework-owned first-scope initialization: it accepts
only an `ExactLedger ... []`, publishes the first nonempty fact bundle, and is
therefore impossible after any fact or commit exists.  It is used for the
initial minimal-counterexample object selection, not for routing or later
residual replacement.  Never archive, deactivate, reset, or rebase an existing
fact.  After initialization, every residual transition is a proved refinement
and every earlier key remains in the exact output index.

Branches commit against one immutable prefix.  Facts on the shared prefix are
visible to every descendant; a sibling-only fact is absent from the sibling's
type-level key index.  Never merge sibling histories or flatten them into a
global store.  Use `RoutedTask.selectFor` or `RoutedTask.dispatchFor`; these
compare exact keys, while names are diagnostics only.  A contradiction or
certified empty residual appends the domain's distinguished closure key, after
which the canonical dispatcher must return `closed`.

Use `ExactLedger.audit` for audit output.  It exposes only exact fact names and
the chronological, append-only `CommitRecord`s forced by literal ancestry; it
does not expose proof bundles, predecessor cursors, or positional lookup.
`ExactLedger.audit_complete`, `ExactLedger.audit_facts_unique`, and
`ExactLedger.audit_commits_nonempty` certify respectively that the audit
accounts for the whole branch fact index, no semantic fact was committed
twice, and no empty commit exists.
Retrieve mathematical facts only with `FactInputs.get` inside an executor or
`ExactLedger.get` at a framework-owned closure boundary.

The catalog checker scans the entire EG proof tree for every noncanonical
history, query, carrier, wrapper, routing, and construction path, and applies
the stricter declaration boundary to the two application-owned files.
`StrategyDag.lean` may contain only the sealed
topology syntax/macro, the final `strategyDag` endpoint, and calls from the
allowlist: it may not declare any helper
definition, theorem, instance, structure, class, inductive, or opaque
constant.  `Problem.lean` is checked against its closed presentation-declaration
allowlist and remains limited to the problem and target presentation described
above.  Opening a framework construction namespace is rejected as an
unqualified-call bypass.  Direct entry projections, key-index inspection,
raw readiness functions, products/sigmas used as fact channels, and every
non-`ExactLedger` type ending in `Ledger` are rejected.

## Implement through the framework

### Use the Type A branch as the closed programming-pattern allowlist

For implementation shape, the ported Type A receiver-and-exit chain is the
only precedent.  Copy its patterns from `Graph/Strategy/SpineRows.lean`,
`Graph/Strategy/TypeAExitRun.lean`, and `Graph/Strategy/SpineAssembly.lean`.
The mathematical content still comes only from the manuscript; Type A is an
authority for program structure, not for theorem statements.

New or repaired rows may use only these Type A forms:

- A deterministic fact step is an `@[reducible] noncomputable def` returning
  `AtomicStrategy`, built with `factOnly`, a literal `FactManifest`, and a
  sealed executor.  The executor reads `inputs.current` and
  `inputs.get key`, and returns the exact heterogeneous `.cons ... .nil`
  production bundle.  Execution is the resulting row's `.run`/
  `AtomicCT.run` on the literal incoming `ExactLedger`, with an explicit
  freshness proof.
- An exhaustive binary paper alternative is a `noncomputable def` returning
  `Decision yesKey noKey previous`, implemented directly by
  `Decision.run previous yesKey noKey` and a proof of exactly one sum arm.
  Its inputs are the literal incoming ledger and `FactKeys.Has` constraints;
  it reads prerequisites with `ExactLedger.get` only at this framework-owned
  decision boundary.  The unchosen key must be absent from the chosen arm.
- A terminal contradiction uses an existing generic framework closure such as
  `closeIncompatible` on the literal branch ledger.  It may append only the
  distinguished closure key and may not encode a terminal in a custom result.
- Composition is a straight-line sequence of typed `have after... := ...`
  bindings, passing each exact output ledger to the next Type A-form row.  A
  real split remains a `Decision`; continuation selects its typed arm and does
  not merge siblings.  Routing uses only `RoutedTask.selectFor` or
  `RoutedTask.dispatchFor` when key-directed dispatch is actually required.
- Vocabulary installation is a thin specialization of generic rows at
  `Spine.K`; key-list aliases are literal cons-lists matching the ledger output
  index.  Freshness and key distinctness are discharged from the closed
  vocabulary, following the Type A `K_eq_iff`/finite-key pattern.

No other programming pattern is permitted, even if it is proof-agnostic or
could be added to the API catalog.  In particular, do not introduce a custom
runner, recursive interpreter, state machine, callback-driven executor,
continuation object, branch payload, result wrapper, bespoke inductive
control type, alternate ledger, reconstructed cursor, sibling merge, direct
`ExactLedger` mutation, or a helper that hides any of those operations.  Do
not imitate legacy, quarantined, Type B, or unfinished route-8 plumbing.

Before accepting an edit, identify the concrete Type A declaration whose
program shape it follows and record that declaration in the private
implementation checklist.  If no Type A declaration exhibits the required
shape, stop: the shape is forbidden under this skill.  Do not expand the
allowlist by adding a new generic API.  The API catalog remains an additional
closed name allowlist; a symbol must be both catalogued and used in one of the
Type A forms above.

- Consume the literal active predecessor passed to the node.  Never reconstruct
  a cursor, restart from the root input, or re-quantify a branch fact from the
  ambient graph.
- Obtain the current object and state from `FactInputs.current`.  Obtain every
  upstream mathematical fact by semantic key through `FactInputs.get`; never
  name its producer or reconstruct it.
- Put every new externally usable fact in the exact production bundle.  The
  framework runner appends that bundle while retaining the literal ancestry
  and indexing all earlier facts in the result type.  Proof-specific code may not call
  `ExactLedger.root`, `ExactLedger.append`, `ExactLedger.publishFact`,
  `ExactLedger.refine`, `ExactLedger.initializeScope`, or `FactInputs.ofLedger`;
  restarting or rescoping an active residual is history loss.
- Change the residual only through a generic atomic Strategy/CT whose
  `refines` proof certifies the restriction.  Equality is the ordinary choice
  for a fact-only step.
- Use the applicable CT specification, capability, execution, certificate,
  continuation, and work theorems.  Never duplicate its enumeration,
  classification, certification, accounting, or terminal logic.
- Use sealed Strategy DAG combinators for topology and canonical ledger routing
  for readiness and closure.  Never write an EG function that transports or
  routes branch payloads.
- Prove exactly the paper fact.  Do not smuggle it through an axiom, `sorry`,
  `admit`, an opaque assumption, a supplied callback, or a stronger surrogate.
  Do not prove it first as a detached universal theorem and call that theorem
  from the executor. The executor itself must derive the produced value from
  the incoming residual facts.

Framework ownership is necessary but not sufficient for a Graph Strategy
adapter: inspect its body and use it only when its catalog entry and body show
that Core or a CT owns execution, data movement, residuals, ledgers, routing,
and terminals.  Delete and replace a framework adapter that is itself ad hoc or
noncompliant.

## Validate and update the audit

Compile the canonical API and all positive and negative enforcement fixtures
before any row-specific target:

```bash
cd hypostructure
lake build Hypostructure.Core.Residual.ExactLedger \
  Hypostructure.Core.Strategy.FactManifest \
  Hypostructure.Core.Strategy.ExactExecution \
  Hypostructure.Fixtures.ExactLedger \
  Hypostructure.Fixtures.ExactExecution \
  Hypostructure.Fixtures.AutomaticLedgerClosure \
  Hypostructure.Fixtures.BranchScopedExactLedger \
  Hypostructure.Fixtures.DerivedFactPublication \
  Hypostructure.Fixtures.ExactExecutionDroppedFact \
  Hypostructure.Fixtures.ExactExecutionMissingRequirement \
  Hypostructure.Fixtures.ExactLedgerDuplicateFact \
  Hypostructure.Fixtures.ExactLedgerEmptinessClosure \
  Hypostructure.Fixtures.ExactLedgerMissingFact \
  Hypostructure.Fixtures.ExactLedgerOpacity \
  Hypostructure.Fixtures.LedgerAutorouting
```

The negative fixtures must compile because their forbidden examples are inside
`#guard_msgs`; deleting or weakening a guard is a failure.  Then compile each
changed generic module and its row-specific generic fixture.  Finally build
the narrowest EG target that elaborates the repaired row, followed by
`HypostructureErdos64EG.Official.StructuralProgram` and the strict
`Official/ClosureProbe.lean` when reachable.  Inspect the regenerated sealed
report for the literal predecessor, outputs, terminal status, and routing.

A downstream failure does not justify weakening the repaired row. Correct the
affected downstream label and node table cells from the observed failure, and
do not repair that node unless requested.

Whenever a fact is implemented, repaired, weakened, strengthened, rerouted, or
invalidated, update its paper-label row and every corresponding diagram-node
row in the same change. Rewrite all affected cells from the current Lean
types, bodies, exact ledger indices, call graph, and build results; do not only
flip a status icon. Keep shared labels and shared nodes synchronized in both
directions. Blank implementation cells remain blank when nothing implements
the object.

Do not add a changelog, progress entry, gap narrative, dated snapshot,
executive-status paragraph, or per-row prose section to
`Assembly_node_audit.md`. Live status belongs only in the two tables. Update
the stable rubrics only when a column's meaning changes.

After the code and both tables agree, run the table checker again. Report
changed generic APIs, deleted ad hoc declarations, validation commands, and
deliberately unfixed downstream failures in the final handoff.

## API catalog maintenance

Run the non-mutating drift, canonical-boundary, and table-synchronization
checks before starting and before finishing:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .
python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check --repo-root .
```

Do not refresh the catalog to legalize a new proof-data operation. This skill
does not add or change the proof-data interface.
