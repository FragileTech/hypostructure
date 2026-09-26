---
name: eg-proof-expansion
description: Implement or review controlled textbook-mathematics benchmark nodes in the Erdős–Gyárfás StrategyDag Lean proof. Use whenever Codex is asked to fix, implement, expand, route, or make compliant a node in proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean or its supporting declarations, while matching the original paper exactly, using only the canonical ExactLedger and sealed Strategy/CT APIs, and removing proof-specific plumbing.
---

# EG proof expansion

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the retained objects, match the hypotheses of the relevant textbook result, execute the deduction, and check the requested output. Give routine steps concise, sufficient justification. Reuse accepted prerequisites at their stated types and domains. A review objection identifies a concrete missing hypothesis, invalid inference, domain mismatch, or unmet task contract and its local repair. Preserve the assigned objectives, stage boundaries, mathematical statements, and required checks.

Implement one requested EG StrategyDag row as an exact instance of the paper's
strategy and of Hypostructure's generic execution model.  Repair the requested
row completely even when the correction exposes a downstream break.

## Keep the task to one requested label

This is the controlling workflow. Apply every broader audit, dependency,
cleanup, and framework instruction below only inside this scope.

1. Identify the single manuscript label explicitly requested by the user. If
   the user names a node, take its open leaf from the manuscript diagram and
   identify, from the live Lean source and a build, the single first
   manuscript label that Lean does not establish on that leaf's ledger. Do
   not begin a second label in the same turn. First classify the split that
   produced the leaf as a dichotomy (see "Classify every split as a
   dichotomy"): the leaf's residual is exactly its arm's defining fact plus
   the retained ledger.
2. Copy that label's exact proposition, inherited hypotheses, alternatives,
   and proof strategy from the manuscript. Do not infer a stronger
   prerequisite, global version, replacement theorem, or different strategy.
3. Identify only the facts already present on the literal incoming residual
   that the manuscript proof consumes. Read them only through
   `FactInputs.current` and `FactInputs.get` inside the executor. Never request
   a sibling fact, ambient theorem parameter, callback, side carrier, or
   supplied certificate.
4. Translate that one proof into Lean. Prove it as a contract lemma in the
   proof-agnostic library (see "Reusable mathematics lives in contract
   lemmas"), or reuse an existing one. Publish each externally usable
   conclusion prescribed for that label in one literal `FactManifest`, whose
   thin adapter executor discharges the lemma's hypotheses from the ledger,
   and append it with `AtomicCT.run` to the same `ExactLedger`.
5. Delete an illegal wrapper, callback, side carrier, or compatibility shim
   only while repairing the valid mathematical proof it transported to use
   the canonical ledger API. Never delete, weaken, broaden, or replace a
   correct paper fact merely because its current transport is illegal.
6. Build the narrow target and report the first downstream failure.
7. Refresh the web explorer's data for the touched nodes (see "Keep the web
   explorer current"). Stop there unless the user explicitly requests the
   next label.

Dependency tracing is diagnostic and read-only. It never expands the edit
scope. A missing downstream interface, inconvenient schema, or compiler error
does not authorize a new API, mathematical certificate, carrier, strategy, or
repair of another label. Do not speculate about such designs. State the exact
requested formula that remains unproved and implement it with a permitted
Type A pattern.

### Reusable mathematics lives in contract lemmas; the ledger wires them

Reusable mathematics and the EG proof are kept separate. Every paper fact is
proved as a **contract lemma**. The ExactLedger machinery wires those lemmas
into the paper's topology.

- A contract lemma is a `theorem` in a proof-agnostic library module under
  `hypostructure/Hypostructure/Graph/` (or `Core/`). It is stated over a
  Mathlib `SimpleGraph` or `Graph.FiniteObject`, and every paper assumption is
  an explicit hypothesis. Paper constants such as the minimum degree, the
  window order, the target length predicate and the scales are parameters.
  Its conclusion is exactly the paper's statement, neither weaker nor
  stronger.
- A contract lemma never mentions keys, `Holds`, `ExactLedger`, `FactInputs`,
  `Spine.Data`, branches, or node numbers. It never imports
  `SpineVocabulary` or any row module, directly or transitively, so adding a
  key never rebuilds it.
- The definitions it uses belong in the same library, not in the vocabulary.
  Each key's `Holds` is the library predicate instantiated at the branch's
  object and presentation.
- A row executor is a thin adapter. It reads `inputs.current` and each
  prerequisite with `inputs.get`, discharges every hypothesis of the lemma
  from those facts, and returns the lemma's conclusion under the declared key.
  A hypothesis may come only from `inputs.get` or `inputs.current`, never from
  an ambient parameter, a callback, a supplied certificate, or a theorem
  argument threaded from outside the ledger.
- One argument, one lemma. When several rows or lanes use the same argument
  under different hypotheses, they call one parameterized lemma. Never keep
  copies of the argument.
- Contract lemmas are tested on their own, with fixtures on concrete graphs,
  and their statements are what the paper-fidelity audit checks.

Before compiling, inspect the diff. Mathematics inside an executor that could
be a contract lemma belongs in the library. A library declaration that
mentions ledger machinery belongs in the adapter. A duplicated argument is a
defect.

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
repair the proof as far as the canonical ledger permits, and report the first
unresolved Lean obligation or downstream compilation failure precisely.

Do not delete valid mathematics when deleting illegal transport. Reconstruct
and publish the same paper fact through the ledger. Do not replace it with a
surrogate, a stronger fact that bypasses the manuscript argument, or a lemma
whose hypotheses are met by anything other than ledger facts.

This section overrides every broader paragraph below. In particular, “repair
the row completely”, “transitive implementation slice”, “follow referenced
proofs”, and “inspect every theorem” do not authorize edits outside the
selected label or changes to the manuscript's proof strategy.

## Establish the authorities

Work from the repository root.  Require these live sources:

- `to_formalize/erdos_64_proof.tex`: sole authority for mathematical
  statements, hypotheses, alternatives, order, and terminal behavior.
- Actual Lean declaration types, bodies, fields, call sites, and imports:
  sole authority for what the implementation does.

Use comments as locators only; never rely on a status report or audit table.
Check the actual declaration type
and the application required for this label. Reuse accepted inputs at their
exact statements; revisit an input only for a concrete mismatch. Correct a
misleading comment within the selected label when needed for the edit.

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

1. Locate the diagram node and its manuscript label in
   `to_formalize/erdos_64_proof.tex`, and the Lean declarations that implement
   them by searching the live source.
2. Read the manuscript around every label consumed by the row.  Record the
   exact statement, inherited hypotheses, exhaustive alternatives, branch
   order, continuation, and terminals.  Read accepted prerequisite statements far enough to
   bind their hypotheses to the selected row; keep upstream proofs accepted.
3. Inspect the actual Lean types and bodies of the registration, generic
   strategy and CT execution. Match each invoked theorem at its actual type to
   the call-site arguments. Inspect a prerequisite body only to resolve a
   specific statement or application discrepancy.
4. Trace the literal incoming `ExactLedger`, its immutable ancestry, indexed
   active residual, complete exact-key list, CT/Strategy manifests, commits,
   routing, and closure facts.  Inspect the composed branch reached from
   `Assembly/Final.lean` when topology or branch status matters.
5. Write a private checklist. At the label level cover tactic, Lean
   declaration, partial match, kernel check,
   residual locality, ledger reads/writes, wiring, legality, and hardcoded
   facts. At the node level cover implementation, combinator, CT ownership,
   reachability, wiring, locality, registration, illegal carriers,
   manuscript difference, kernel check, manuscript labels, and dichotomy
   classification of every split on the path. Collect fresh evidence for each
   item.

### Refactor, never reinvent; the ledger grows monotonically about G

A refactor carries the SAME argument into a new structure. It never changes
the proof:

- Every fact is about G, the single selected counterexample (`K .selection`),
  and about objects of G already fixed on the ledger. Each new fact is
  computed from the incoming residual and appended.
- The `ExactLedger` only grows. Nothing fixed upstream is ever re-chosen,
  reset, or restated away.
- Keep the argument path: each node consumes the same facts and splits on the
  same witness as before (the paper's path). A refactor must never:
  - merge per-candidate decisions into "some candidate / every candidate"
    forms;
  - replace per-lane or per-object facts by families over all objects of G;
  - substitute a different argument.
- A witness that an upstream fact only asserts with ∃ becomes a canonical
  object of G: `Classical.choose` of that upstream statement at G. Downstream
  facts then speak about exactly the object the upstream fact asserted.
- Every changed declaration must be justified against its pre-refactor
  counterpart: same argument path, now stated about G.

### Every fact is about the incoming residual

This is the purpose of Hypostructure and the `ExactLedger`, and it is not a
matter of style: it is the proof methodology itself. The argument works
throughout with ONE counterexample, the selected minimal G, and with the
objects fixed on G along the branch. A fact about generic pieces or
independently chosen witnesses cannot carry that argument. Every published
fact is a statement about the incoming residual, and it is computed from that
residual:

- Each key's `Holds` is evaluated at the branch's residual. It speaks about
  `inputs.current`: its object, its state, and the objects the ledger has
  already fixed on this branch (the canonical packing, the selected pieces,
  components, receivers, coordinates, tokens and witnesses).
- A fact may quantify only over the residual's own objects. It must not
  quantify over arbitrary graphs, arbitrary boundaried pieces, arbitrary
  contexts, or separately chosen witnesses that the residual does not
  determine. An existential over "some piece somewhere" is not a fact about
  the residual. Such facts can be vacuously true or never satisfiable, and
  they make branches trivial.
- Each executor computes its fact from `inputs.current` and `inputs.get`
  facts on the literal incoming ledger. The contract lemma receives the
  residual's objects as arguments.
- Every proof in the repository is ultimately applied to G. A contract lemma
  may be generic (∀ object, hypotheses → conclusion), and a more general or
  reusable version is welcome. For the proof, though, it is always
  instantiated at G and at the objects fixed on G, and every hypothesis is
  checked on G from G's ledger facts. The published `Holds` is that
  instantiation, never the generic statement and never an existential that
  re-chooses what G already fixed.
- A decision splits on a predicate about the residual. Both arms carry that
  predicate or its negation, about the same residual objects.
- Check satisfiability. A survivor or exclusion key that cannot hold on any
  counterexample makes its branch vacuous; that is a defect, not a closure.
  Never close a branch through such a fact.

### Classify every split as a dichotomy

Every branch point of the manuscript strategy is an exhaustive, exclusive
dichotomy: a predicate `P` and its exact complement `¬P`, possibly normalized
to a positive form the paper states (for example, "the homogeneous caps hold"
versus "some token carries a homogeneous pattern of size `L_geom`").  A
multi-way split is a sequence of nested binary dichotomies in paper order.

- Before auditing or editing, list every split on the path from the incoming
  ledger to the requested row. For each one, record the predicate, its
  complement, both arms, each arm's defining fact, and where each arm goes.
- In Lean, implement every split as a `Decision yesKey noKey previous` whose
  two keys' `Holds` are exactly the arm-defining predicate and its complement.
  The chosen arm's key goes on that arm's ledger. Never implement a paper
  split as an unconditional run, a route that silently assumes one arm, or an
  unkeyed disjunction. When the Lean topology hides a split, that is a
  topology difference from the paper, and it must be corrected.
- An arm's defining fact is part of its residual. Consequences derived only
  on the complementary arm are excluded from it by definition, not missing
  from it. An open leaf is exactly what its dichotomy left: attack it by
  structural exhaustion using the facts on its own arm. Never propose, cite
  as required, or report as a gap a lemma whose hypothesis is the other arm's
  defining fact.
- The two keys must be exact complements on the same object: the paper
  predicate and its negation, about the same pinned packing, component,
  receiver, or witness that the paper fixes. Two existentials over separately
  chosen witnesses do not count, and neither does an arm that drops the pin
  or re-quantifies it.
- Every terminal contradiction closes through the framework: `closeIncompatible`
  or `AtomicCT.runAndCloseIncompatible` with an `Incompatible` instance
  appends the distinguished closure key. Never encode a terminal as a key whose
  `Holds` is `False`, a hand-built `False` from `.get … .down`, `.down.elim`,
  or a caller-supplied closure option. The closed ledger that results is
  discharged at the end of its branch with `ExactLedger.elimClosed`, and never
  in any other way.

### Report failures by node and label

Every explanation of a missing fact, noncompliant node, compilation break, or
next repair must identify the node and label before drawing a conclusion:

- name the diagram node as `Node [n]`, reproduce its exact mathematical
  output, and cite its implementing Lean declaration, wiring, and build
  result;
- name every corresponding manuscript label and cite its Lean declaration,
  exact published key, and ledger reads and writes;
- state the first exact proposition or witness that Lean does not currently
  establish.  Write its complete mathematical formula and all objects it is
  quantified over; never report only a node range, umbrella theorem, generic
  dependency, or downstream symptom;
- classify the defect precisely as one of: mathematical proof absent,
  mathematical statement weakened/strengthened, fact proved but not published,
  fact published under the wrong schema, fact published but not wired, illegal
  read/write or carrier, wrong branch ancestry, or downstream interface
  mismatch.  Do not conflate these categories;
- distinguish the first failing label from later facts that merely cannot
  be derived because of it.  A compiler error at a later line is not the first
  mathematical gap when an earlier label is absent or incorrectly
  implemented.

The final answer for any failure question must lead with this exact
node-and-fact identification.  It may then explain prerequisites and downstream
effects, but those effects must not be presented as additional missing facts
unless they independently fail.

The paper strategy is immutable.  Never add, remove, merge, reorder, weaken,
strengthen, or replace a mathematical alternative.  Correct the Lean topology
only when it differs from the paper; never invent a new strategy to make Lean
easier.

(Superseded by the user's no-deviation rule below: from now on, even a strictly
better Lean argument is not substituted. Deviations already registered stay
documented, and new ones are not made.) Earlier exception: when the Lean argument is kernel-checked, weakens no
paper fact, closes the node the paper closes, and is better than the paper's
argument, the Lean prevails. Register that deviation in
`audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`, giving the node,
the paper argument with tex lines, the Lean argument with its declarations,
and the reason it is at least as strong. An unregistered deviation is a
defect.

Never repair and never deviate. Implement the paper exactly as written,
through the Hypostructure machinery as prescribed. When a step of the paper
does not hold, or is not proved by the paper's own argument, do not repair it,
do not substitute a different argument or definition, and do not widen an
outcome. Report it in `audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`
under "Paper errors" with: the node, the tex line, the paper's exact claim,
the faithful formal statement, why it fails, and a Lean-checked counterexample
where feasible. An unprovable paper step is represented as follows (user decision): state the
paper's claim exactly at its node, and make its proof `sorry` tagged
`-- PAPER-ERROR [node] tex:<line>`, pointing to the report. Use a PAPER-ERROR
sorry only for a genuine paper error, never as a placeholder for unfinished
work. `#print axioms` on the root then shows `sorryAx` exactly for these.

User decision (2026-09-26), node [144]: the residual left by the paper's
error at [144] is carried by the open leaf [144a]. Its retained content is the
handoff, or the unresolved same-label pattern-pair residual about G's
canonical pattern pair. The root keeps its six outcomes.

Repairs are quarantined, never deleted. Any repair lemma, alternative argument
or reverted repair goes to `hypostructure/Hypostructure/Quarantine/PaperRepairs/`
(listed in `hypostructure/quarantine.txt`, described in that folder's
README.md). No live module may import it; `hypostructure/scripts/check_quarantine.py`
enforces this. Quarantined modules listed in `quarantine.txt` are reference
only: never delete them, and never import them.


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

Place reusable logic under `hypostructure/Hypostructure/Core` or a
proof-agnostic `Hypostructure.Graph` module. Keep contract lemmas and the
definitions they use in library modules that do not import the vocabulary.
Keep rows and decisions in `Graph/Strategy` as thin adapters. Generic
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
  production bundle.  Each produced value is a contract lemma instantiated at
  `inputs.current.object`, with its hypotheses taken from the `inputs.get` facts.  Execution is the resulting row's `.run`/
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
use the canonical ExactLedger and sealed Strategy/CT interfaces.

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
- Use the applicable generic Core or Graph framework theorems.  Never
  duplicate their enumeration, classification, certification, accounting, or
  terminal logic.
- Use sealed Strategy DAG combinators for topology and canonical ledger routing
  for readiness and closure.  Never write an EG function that transports or
  routes branch payloads.
- Prove exactly the paper fact.  Do not smuggle it through an axiom, `sorry`,
  `admit`, an opaque assumption, a supplied callback, or a stronger surrogate.
  Prove it as a contract lemma whose conclusion is exactly the paper
  statement, and call that lemma from the executor. The executor supplies
  every hypothesis from the incoming residual's facts.

Framework ownership is necessary but not sufficient for a Graph Strategy
adapter: inspect its body and use it only when its catalog entry and body show
that Core or a CT owns execution, data movement, residuals, ledgers, routing,
and terminals.  Delete and replace a framework adapter that is itself ad hoc or
noncompliant.

## Validate

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
changed generic module and its row-specific generic fixture.  Finally build,
from `proofs/hypostructure_erdos_64_eg`, the narrowest EG target that
elaborates the repaired row, followed by the package default target
`HypostructureErdos64EG`, whose root reduction
`officialCounterexample_reaches_selectedLedgerBoundary` is in
`Assembly/Final.lean`.  Inspect the composed branch for the literal
predecessor, outputs, terminal status, and routing.

A downstream failure does not justify weakening the repaired row. Report it
at its exact statement, and do not repair that node unless requested.

Report
changed generic APIs, deleted ad hoc declarations, validation commands, and
deliberately unfixed downstream failures in the final handoff.

## Keep the web explorer current

The explorer reads two data sources: the manuscript, and the hand-maintained
node-status file `web/data/eg_node_audit.json`. Nothing regenerates that file
from Lean, so every change to a node goes stale unless this step updates it.
It is output only: never read it as evidence for this workflow.

After the build, rewrite the `nodes` entry of every diagram node whose Lean
producer, published fact, wiring, or build status changed. Take every field
from the live Lean source and the build you just ran:

- `producer`: the implementing declaration with its file and line;
- `fidelity`: one of `FAITHFUL`, `FAITHFUL-TRIVIAL`, `STRONGER`, `WEAKER`,
  `DIVERGENT`, `SURROGATE-TRIVIAL`, `PLUMBING`, `VACUOUS`, or `ABSENT`, judged
  against the manuscript statement;
- `fidelity_note`: the published `Holds` content compared with the paper;
- `complete`: `YES` when the node's own producer kernel-checks without an
  unfinished dependency, `YES <qualifier>` for partial, and otherwise `NO`;
- `local`, `api`, `difference`, `on_probed_closed_arm`, and `blocked_by` when
  it applies.

Also update the top-level `updated_at` field. Edit only this data file; never
edit web code. Then regenerate and test the explorer data from the manuscript
and the refreshed file:

```bash
make web-data
```

Report the refreshed node entries and the `make web-data` result in the
handoff.

## API catalog maintenance

Run the non-mutating drift and canonical-boundary check before starting and
before finishing:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .
```

Do not refresh the catalog to legalize a new proof-data operation. This skill
does not add or change the proof-data interface.
