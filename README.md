# Hypostructure

[![DOI](https://zenodo.org/badge/1322859158.svg)](https://doi.org/10.5281/zenodo.21813635)

Hypostructure is a Lean 4 framework for formalizing structural-exhaustion arguments:
proofs organized as a finite tree of branch states, in which each step performs a case
split, a local reduction, or a quantitative estimate, and either continues on a refined
residual problem or closes its branch by contradiction. The framework provides a single
typed representation of that structure, so that the bookkeeping such proofs depend on —
which hypotheses are available on which branch, which obligations remain, which case
splits are exhaustive — is checked by the elaborator rather than by inspection.

The repository contains the framework and its first application, a formalization of the
minimal-counterexample proof of the Erdős–Gyárfás power-of-two cycle problem (Erdős
problem 64). The manuscripts queued for subsequent formalization are in
[`to_formalize/`](to_formalize/).

## Design

The state of a branch is carried by one indexed type:

```
ExactLedger (Domain) (residual) (factKeys)
```

The active residual problem and the complete list of facts established on the branch
appear as type indices. This placement determines the framework's properties.

*Availability.* A step declares its hypotheses in a `FactManifest`, and those keys are
matched against the ledger's index at elaboration. Invoking a step on a branch that has
not established its hypotheses is a type error, not an omission a referee must detect.

*Retention.* Commits prepend to the index. Every predecessor fact remains present and
remains queryable at the refined residual, since each transition carries a
`RefinementSystem.Refines` proof supplying the transport.

*Absence of side channels.* Each residual domain has one `FactSystem`, and
`FactSystem.value_subsingleton` makes fact values proof-irrelevant. Data therefore
cannot travel between steps inside a fact; anything a later step uses must be an
observable of the object or a declared production of an earlier step.

*Position independence.* `AtomicCT` takes no predecessor parameter. A step runs after any
branch cursor whose ledger contains its declared requirements, so a proof cannot encode
an authored execution order and then rely on it.

*Auditability.* `ExactLedger.audit` reports the fact names and the chronological commits
without exposing proof bundles; `audit_complete` certifies that the two views account
for the same append-only history, `audit_facts_unique` excludes duplicate semantic
facts, and `audit_commits_nonempty` excludes empty entries.

`ExactLedger` is the only carrier of residual state, proof history, and facts. The
constraint is exclusive rather than preferential: no second carrier is permitted under
any name, and a repository gate enforces this.

## Components

### `Hypostructure/Core` — the domain-neutral kernel

`Problem.lean` fixes the problem data: an ambient type, a baseline predicate, a branch
state indexed by the ambient object, and optional typed presentation data. `Target` is
separate, so one problem registration serves several theorem statements; its two bridge
fields are formulation laws relating a target predicate to a public statement, and carry
no mathematical content of the proof.

`Residual/ExactLedger.lean` defines the ledger described above. Its construction
operations — `root`, `append`, `publishFact`, `refine`, `initializeScope` — require a
`FrameworkToken` whose constructor is private and whose value is emitted by a custom
elaborator only while compiling framework modules. Application modules cannot call them.

`Strategy/ExactExecution.lean` defines `AtomicCT`, the sealed executor. An executor
receives a `FactInputs` view consisting of the current residual and exactly the facts
named in `manifest.Requires`, and returns an `AtomicResult` committing exactly
`manifest.Produces`. `AtomicStrategy` is a definitional alias of `AtomicCT`: there is no
second executor, runner, conversion, or output type.

`Execution.lean` and `Budget/` supply the executable substrate. A `Spec` fixes the
input, outcome, and trace types of a computation; a `Capability` supplies a deterministic
reference machine together with soundness, exhaustiveness, and a polynomial check
budget agreeing with the machine's own count; the resulting `Result` has a private
constructor, so a caller cannot present an unverified outcome as a verified one.

`Strategy/FactManifest.lean` provides `RoutedTask.selectFor` and
`RoutedTask.dispatchFor`. Both schedule by exact keys in the branch index;
declaration names are used only for diagnostics. `Routing.lean` is a separate
execution-routing API: it defines stable `CTId`/`Edge` identities, registered
`Profile` and `Transition` values, semantic discovery, and framework-generated route
results.

Core also carries the finite mathematics the applications require: enumeration,
partitions and connected partitions, maximal selection, certified table aggregation and
bounds, finite entropy, dyadic length, and arithmetic transport.

### `Hypostructure/Graph` — the finite-graph instantiation

Finite graph objects and their isomorphisms; boundaried atoms, gluing, and boundary
overlap; deletion and deletion criticality; induced paths and maximal induced-path
packing; window curvature algebra, enumeration, and codes; receiver load and routing;
capacity-token accounting; and the Type A, Type B, cold-corridor, and route-8 machinery
of the Erdős–Gyárfás argument.

These modules are stated in problem-agnostic terms. No framework module names the
problem, and no constant of the manuscript — the window order 13, the label count 399,
the surplus threshold, the barrier rate — occurs in the framework; each enters as a
field of the registered presentation data. The order-generic curvature algebra remains
in `Graph/WindowCurvature`, while everything fixed to a particular window order lives in
the application.

`Graph/Strategy/` holds the reusable executable rows and their exact-ledger
compositions. `SpineVocabulary` defines the registered `Data`, the residual input, and
the closed semantic-key vocabulary. `SpineRows`, `SurplusRows`,
`HomogeneousBottleneckRows`, and `ColdCorridorRows` define atomic strategies and binary
decisions. `SpineAssembly`, `SpineContinuationRun`, `SurplusRun`, `TypeAExitRun`, and
`ColdCorridorRun` compose those rows over literal `ExactLedger` indices and expose audit
theorems. There is no `SpineRun` result carrier in the live API.

### `Hypostructure/Fixtures` — sealing tests

The fixture directory contains negative fixtures as well as positive ones: modules that
are required to fail elaboration. A dropped fact, a duplicate fact, a missing
requirement, and a breach of ledger opacity each have a fixture asserting rejection, so
the sealing properties above are tested rather than asserted.

### Gates

Three checks run under `make lint`: `check_total_execution.py`,
`check_quarantine.py`, and the generated API-catalog check. They reject partial outcomes
at the execution boundary, keep retired modules and noncanonical carriers outside the
build closure, and restrict the Erdős--Gyárfás application to the plumbing allowlist in
`.agents/skills/eg-proof-expansion/references/allowed-api.md`.

## Repository layout

```
hypostructure/                   the framework (Lean 4, Mathlib)
  Hypostructure/Core/              domain-neutral kernel
  Hypostructure/Graph/             finite-graph instantiation and the spine
  Hypostructure/Fixtures/          positive and negative sealing fixtures
  Hypostructure/PDE/               pre-rewrite PDE instantiation (see Roadmap;
                                   outside the live build closure)
  scripts/                         the gates
proofs/hypostructure_erdos_64_eg/  the Erdős–Gyárfás application
to_formalize/                      manuscripts queued for formalization
Assembly_node_audit.md              synchronized paper-label and diagram-node audit
LEGACY_REMOVAL_AUDIT.md            record of what the API rewrite retired
```

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is
`leanprover/lean4:v4.31.0`, with Mathlib pinned to the corresponding tag.

```bash
make mathlib-cache     # fetch prebuilt Mathlib artifacts
make framework-build   # build the Hypostructure package
make erdos-build       # build the Erdős–Gyárfás application package
make erdos             # check the final theorem and print its axioms
make build             # both
make lint              # total-execution, quarantine, and API-catalog gates
make test              # build and lint
```

## The Erdős–Gyárfás formalization

The statement is that every finite simple graph of minimum degree at least 3 contains a
cycle whose length is a power of two. The public statement in
`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Problem.lean` is pinned verbatim
against `Erdos64.erdos_64` of Google DeepMind's `formal-conjectures`.

The source is `to_formalize/original_erdos_64_proof.tex`, a minimal-counterexample proof
that uses the Hegde–Sandeep–Shashank $P_{13}$-free theorem as a black box. Replacing the
power-of-two-cycle predicate by the absence of edge-rooted Mersenne returns, minimality
together with a boundaried replacement principle makes every proper atom
target-uncompressible; the $P_{13}$-free theorem then forces a maximal packing of induced
$P_{13}$ windows of low density, leaving a large $P_{13}$-free remainder. The
curvature-rank branch routes rank loss to target defect, compression, or delocalization;
the whole-graph case is handled by exact closed response profiles; the final closure is
driven by two-budget entropy routing and a large-budget branch governed by a
surplus-adjusted comparison.

`Problem.lean` declares the public statement, one Core problem, one Core target, and the
registered data consumed by the generic graph strategies. Its problem-specific inputs
are supplied by `WindowAlgebra.lean` and `FiniteChecks/P13Barrier`. `StrategyDag.lean`
contains the thin authored root checks and imports the generic continuation surface;
it defines no application-local result carrier. `Assembly.lean` instantiates and
composes the generic rows over exact ledger indices and proves the selected-root closure
and the final public theorem. The package root imports `Problem` and `Assembly` and
exports `HypostructureErdos64EG.erdos_64 : OfficialStatement`.

### Status

Implementation coverage is tracked in the two synchronized tables of
[`Assembly_node_audit.md`](Assembly_node_audit.md): one row per labeled manuscript fact
and one row per Chapter 1 diagram node. The TeX remains the mathematical authority;
table cells are updated from live Lean types, bodies, exact ledgers, call-graph wiring,
and builds. A blank implementation cell means that nothing in the tree implements the
object.

The application currently assembles a selected-ledger contradiction and exposes the
end-to-end theorem `HypostructureErdos64EG.erdos_64`. `make erdos` checks that this
declaration has the pinned `OfficialStatement` type, prints its axioms, and rejects a
dependency on `sorryAx`.

Every ported row has been checked with `#print axioms` and depends on `propext`,
`Classical.choice`, and `Quot.sound` alone. There is no `sorryAx`, and no
`Lean.ofReduceBool`, so no `native_decide` result is load-bearing.

### The canonical-ledger rewrite

The framework was rewritten onto the single `ExactLedger` API, retiring the former
layered execution and registration surfaces in favor of `AtomicCT.run`, sealed
`FactInputs`, exact manifests, and framework-owned decisions and closures. Retired
modules are excluded from the build closure rather than imported through compatibility
wrappers. `LEGACY_REMOVAL_AUDIT.md` records that removal.

## Roadmap

The manuscripts in [`to_formalize/`](to_formalize/) fall into three groups.

**Methodology.** `branch_closure_methodology_extended.tex` (*Structural Exhaustion*) is
the reference manual: a typed library of proof tactics, a strategy manual for selecting
and parameterizing them, and an assurance layer for auditing their inputs, outputs, and
dependencies. `Hypostructure/Core` is an implementation of that specification.
`llm_auditable_proof_architecture_draft.tex` develops the same method for PDE, replacing
the search for a single decisive global estimate by iterated local closure, residual
promotion, and certified reduction to previously discharged obstructions.

**Combinatorics.** `original_erdos_64_proof.tex`, whose current Lean application exports
the end-to-end theorem described above.

**Navier–Stokes.** Three proof manuscripts form a dependency chain in which each
discharges a branch left by its predecessor. A separate entropy companion organizes
the state space supplied by that three-paper chain.

- `proof_setup.tex` establishes the local pointwise Type I reduction: Seregin
  extraction, the raw generated state space, and exclusion of the small-amplitude,
  stationary $L^3$, uniformly $L^3$-tight, and structure-and-decay classes. Its Type I
  contradiction rests on one named residual-class hypothesis, `p1:hyp:no-remainder`,
  which the paper states explicitly.
- `type_I_residual_closure.tex` proves that hypothesis. An ordered residual
  decomposition, centered angular-circulation absorption, a minimal mesoscopic-scale
  rigidity theorem, and an endpoint sequence-$L^3$ Liouville argument for bounded mild
  ancient solutions yield the refined residual closure; inserted into the setup paper's
  final assembly, this gives `cor:local-typeI-unconditional`, placing every
  finite-energy singular point in the local Type II alternative. No global critical-norm
  estimate and no global Liouville theorem for bounded centered profiles is used.
- `type_II_regularity.tex` establishes the local retained-branch exclusion criterion for
  the remaining alternative, by repaired-gauge representation for nondegenerate
  concentration cores, local Calderón–Zygmund pressure control, a Caccioppoli estimate
  on compact cylinders, multibubble and cascade reductions, and scale-collapse cost
  estimates, with the retained compact branch closed by routing into the scale-rigid
  discharge.
- `ns_perelman.tex` constructs a localized entropy functional $\mathcal{W}_{\mathrm{loc}}$
  on the singular-branch state space supplied by the preceding three. It is conditional
  on those companions by construction, and serves as an organizing quantity for the
  program rather than as one of its exclusions.

`overall_proof_architecture.tex` is the referee guide to the stratification, and
`stokes_appendix_body.tex` supplies supporting Stokes-system material.

Formalization order is governed by the framework rather than by the mathematics: a
target is queued once its branch structure — its case splits, residual promotions, and
retained obstructions — has been read off the manuscript and expressed as rows over the
canonical ledger. The immediate items are:

1. Maintain the Erdős–Gyárfás application against the manuscript, synchronized node
   audit, canonical-ledger gates, and pinned public statement.
2. Formalize the assurance layer of `branch_closure_methodology_extended.tex` as
   theorems about `ExactLedger`.
3. Rebuild `Hypostructure/PDE/`. It predates the canonical-ledger rewrite and lies
   outside the live build closure; its parabolic atlases, localization, vorticity, and
   Navier–Stokes model are porting reference, to be reconstructed on the canonical API
   as the Erdős–Gyárfás rows are, rather than re-imported.
4. Port the three-paper Navier–Stokes chain in dependency order: `proof_setup`,
   `type_I_residual_closure`, and `type_II_regularity`; treat `ns_perelman` afterward as
   the entropy companion. The proof chain is itself an instance of the structure the
   ledger records. The setup paper names a residual-class hypothesis and promotes it;
   Paper II discharges it and commits the corresponding fact; the final assembly reads
   that fact back. Under formalization the discharge becomes a key in the branch index,
   present or absent, and is checked at elaboration rather than traced by hand across
   manuscripts.

No schedule is claimed. What formalization adds is not qualification of the results but
a mechanical record of their use: which branch each theorem closes, and which facts were
available when it did.

## Citing

Archived on Zenodo at [`10.5281/zenodo.21813635`](https://doi.org/10.5281/zenodo.21813635).
The concept DOI above resolves to the most recent release; each release also receives a
version DOI.
