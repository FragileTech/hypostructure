# Hypostructure

[![DOI](https://zenodo.org/badge/1322859158.svg)](https://doi.org/10.5281/zenodo.21813635)

A Lean 4 framework for **machine-auditable structural-exhaustion proofs**, together
with its first application: a formalization of the minimal-counterexample proof of
the Erdős–Gyárfás power-of-two cycle problem (Erdős problem 64).

The framework's purpose is narrow and specific. Long, LLM-assisted mathematical
arguments fail in a characteristic way: a case split quietly loses a branch, a
hypothesis is used on a branch that never established it, a "fact" travels between
steps inside an ad-hoc record that nobody audits, or a lemma is supplied as an
assumption where the manuscript derives it. Hypostructure makes each of those
failures a *type error* rather than a review finding.

---

## The idea

A structural-exhaustion proof is a finite tree of branch states. Each step reads
some facts, refines the residual problem, commits new facts, and either continues
or closes its branch by contradiction. Hypostructure gives that shape one — and
only one — representation in Lean:

**Everything a proof step knows is in the type of its ledger.**

```
ExactLedger (Domain) (residual) (factKeys)
```

The active residual and the complete list of branch-local facts are *type indices*.
A step cannot read a fact that is not in the index, cannot drop one that is, and
cannot smuggle one past the index, because there is nowhere else to put it. The
consequences are enforced by construction:

| Discipline | How it is enforced |
|---|---|
| No fact is used before it is proved | Requirements are matched against the type-level key list; a missing key is an elaboration failure |
| No fact is silently dropped | Commits *prepend*; every predecessor key stays in the index and stays queryable |
| No side channel carries data | `FactSystem.value_subsingleton` makes a fact value proof-irrelevant — a payload cannot be smuggled in one |
| The residual only ever shrinks | Every transition ships a `RefinementSystem.Refines` proof |
| No step encodes its position | `AtomicCT` takes no predecessor: it runs after *any* branch cursor whose ledger carries its declared requirements |
| The history is complete | `ExactLedger.audit` is proof-free and `audit_complete` certifies it accounts for the whole append-only history |

There is exactly one carrier. A second one — however named, however reasonable —
is a bug, and a repository gate rejects it.

## Architecture

### Core — the domain-neutral kernel

`hypostructure/Hypostructure/Core/`

- **`Problem.lean`** — the universal problem kernel: an ambient type, a baseline
  predicate, a branch state, and optional typed presentation data. `Target` is kept
  separate, so one problem registration can serve several theorem statements; its
  two bridge fields are *formulation* laws, not the theorem.
- **`Residual/ExactLedger.lean`** — the canonical and only residual/history carrier,
  described above. Its construction operations (`root`, `append`, `publishFact`,
  `refine`, `initializeScope`) sit behind an unforgeable `FrameworkToken` that a
  custom elaborator emits only while compiling framework modules. Applications
  physically cannot call them.
- **`Strategy/ExactExecution.lean`** — `AtomicCT`, the sealed executor. It sees a
  `FactInputs` view (the current residual plus exactly its declared requirements)
  and returns an `AtomicResult` committing exactly its declared productions.
  `AtomicStrategy` is a definitional *alias* — there is no second executor, runner,
  or output type.
- **`Strategy/FactManifest.lean`** — each step's `Requires`/`Produces` contract.
  Production lists are nonempty and duplicate-free.
- **`Execution.lean`, `Budget/`** — the executable substrate: a `Spec`, a
  `Capability` (a deterministic reference machine with soundness, exhaustiveness,
  and a polynomial check budget), and a framework-generated `Result` whose private
  constructor prevents a caller from manufacturing a verified outcome.
- **`Routing.lean`** — `RoutedTask.selectFor` / `dispatchFor`, the only scheduling
  entry points. They match on exact keys in the branch index; names are diagnostics.
- Supporting finite mathematics: enumeration, partitions, certified table
  aggregation, entropy, dyadic scales, arithmetic transport.

### Graph — the combinatorial instantiation

`hypostructure/Hypostructure/Graph/`

Finite graph objects, boundaried atoms and gluing, deletion criticality, induced-path
packing, window curvature, receiver load and routing, capacity-token accounting, and
the Type A / Type B / cold-corridor / route-8 machinery the Erdős–Gyárfás argument
needs. All of it is stated in problem-agnostic terms: **no framework module names the
problem**, and no constant of the manuscript (window order 13, the count 399, the
surplus threshold) is hardcoded — each enters as a field of the registered
presentation data.

`Graph/Strategy/` holds the executable spine: `SpineVocabulary` (the `Data` record
and the semantic keys with their `Holds` clauses), `SpineRows` (the rows, each an
`AtomicStrategy` or a `Decision`), and `SpineRun` (the composition, its 21-exit
`Result`, and the audit theorems).

### Fixtures — the framework's own regression corpus

`hypostructure/Hypostructure/Fixtures/` contains positive *and negative* fixtures:
modules that must fail to elaborate. A dropped fact, a duplicate fact, a missing
requirement, an opacity breach — each has a fixture asserting the framework rejects
it. The sealing is tested, not asserted.

### Gates — what CI actually checks

```
make lint
```

- **total-execution gate** — rejects partial outcomes (`sorry`-shaped or
  unimplemented-branch constructs) at the execution boundary.
- **canonical-ledger gate** — rejects declarations grafted into the canonical
  ledger's namespace and structures that impersonate it without being a
  `FactSystem`; keeps quarantined legacy modules out of the build closure.
- **API-catalog boundary check** — the proof application may only use the generated
  plumbing allowlist in
  `.agents/skills/eg-proof-expansion/references/allowed-api.md`.

## Repository layout

```
hypostructure/          the reusable framework (Lean 4 + Mathlib)
  Hypostructure/Core/       domain-neutral kernel: problem, ledger, executor, budgets
  Hypostructure/Graph/      finite-graph instantiation and the executable spine
  Hypostructure/Fixtures/   positive and negative sealing fixtures
  Hypostructure/PDE/        pre-rewrite PDE instantiation (see roadmap; not in the
                            live build closure)
  scripts/                  the gates
proofs/
  hypostructure_erdos_64_eg/   the Erdős–Gyárfás application
to_formalize/           the manuscripts queued for formalization
EG_STRATEGYDAG_AUDIT.md      the live, row-by-row port tracker
LEGACY_REMOVAL_AUDIT.md      what the API rewrite retired, and why it is safe
```

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is
`leanprover/lean4:v4.31.0` with Mathlib pinned to the matching tag.

```bash
make mathlib-cache     # fetch prebuilt Mathlib artifacts (do this first)
make framework-build   # build the Hypostructure package
make erdos-build       # build the Erdős–Gyárfás application
make build             # both
make lint              # the three gates
make test              # build + lint
```

---

## The Erdős–Gyárfás formalization

**Statement.** Every finite simple graph of minimum degree at least 3 contains a cycle
whose length is a power of two. The public statement in
`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Problem.lean` is pinned
verbatim against `Erdos64.erdos_64` in Google DeepMind's `formal-conjectures`.

**Source of truth.** `to_formalize/original_erdos_64_proof.tex` — a
minimal-counterexample proof using the Hegde–Sandeep–Shashank $P_{13}$-free theorem as
a black box. Replacing the power-of-two-cycle predicate by the absence of edge-rooted
Mersenne returns makes every proper atom target-uncompressible; the $P_{13}$-free
theorem then forces a low-density maximal packing of induced $P_{13}$ windows, and the
argument proceeds by curvature-rank routing, exact closed response profiles, and
two-budget entropy routing.

**The application boundary is two modules.** `Problem.lean` declares the statement, the
Core problem, the Core target, and the one record of registered data — the
Hegde–Sandeep–Shashank theorem (via `WindowAlgebra.lean`) and an audited finite
curvature table (via `FiniteChecks/P13Barrier`). It contains no strategy, no executor,
no ledger operation. `StrategyDag.lean` is the authored topology.

### Port status

The proof is decomposed into **73 rows** across eight blocks, tracked row by row in
[`EG_STRATEGYDAG_AUDIT.md`](EG_STRATEGYDAG_AUDIT.md). Each row carries six evidence
bullets and a table mapping every manuscript `\label` it consumes to the Lean
declaration whose *type* states it — an empty cell means nothing implements the object,
and that emptiness is the point.

| Block | Rows | State |
|---|---|---|
| A. Entry spine | 1–10 | Ported and compiling on the canonical ledger |
| B. Type A receiver ladder | 11–19 | Row 11 ported; 12–19 being rebuilt |
| C. Type B fan | 20–29 | Rows 20–25 and 29 ported; 26–28 open |
| D. Non-near-cubic surplus | 30–36 | Groundwork started |
| E. Remainder, rank, net charge | 37–42 | Rows 37–38 ported; 39–42 in flight |
| F. Cold-window corridor | 43–61 | Rows 43–50 ported |
| G. Route-8 carrier closure | 62–67 | Being rebuilt |
| H. Rank-drop branch | 68–73 | Being rebuilt |

Two disciplines the audit exists to enforce. First, **the audit is not evidence** — a
status cell is a claim about code that may have moved since; only a live build settles
it. Second, docstrings, comments, and prior audit revisions are read as *intentionally
misleading*: the only admissible evidence for a row is the manuscript and the Lean type.

Every ported row has been checked with `#print axioms` and depends on `propext`,
`Classical.choice`, and `Quot.sound` alone. No `sorryAx`; no `Lean.ofReduceBool`, so no
`native_decide` result is load-bearing.

### The API rewrite

The framework was recently rewritten onto the single canonical `ExactLedger` API,
retiring a layered `CT*` stack of capability/certificate/search/automation modules that
`AtomicCT.run` now replaces outright. That rewrite is why several blocks read as "being
rebuilt": their mathematics is intact and quarantined on disk as porting reference, but
a quarantined module is **never** re-imported — each row is rebuilt against the live
framework. `LEGACY_REMOVAL_AUDIT.md` records the removal and proves it is a no-op for
the build closure.

---

## Roadmap: the rest of `to_formalize/`

The Erdős–Gyárfás port is the framework's proving ground. The larger goal is the body of
work in [`to_formalize/`](to_formalize/) — a program on three-dimensional Navier–Stokes
regularity, written in the same structural-exhaustion style, plus the two methodology
manuscripts that specify the style itself.

**Methodology (specifies the framework).**

- `branch_closure_methodology_extended.tex` — *Structural Exhaustion*: the reference
  manual. A typed library of proof tactics, a strategy manual for parameterizing them,
  and an assurance layer for auditing their inputs, outputs, and dependencies. This is
  the document `Hypostructure/Core` is an implementation of.
- `llm_auditable_proof_architecture_draft.tex` — *Constructing Repairable Architectures
  for AI-Assisted PDE Proofs*: the same method for PDE, replacing the search for one
  decisive global estimate by iterated local closure, residual promotion, and certified
  reduction to already-discharged obstructions.

**Combinatorics.**

- `original_erdos_64_proof.tex` — Erdős–Gyárfás. **In progress** (above).

**Navier–Stokes.** A chain in which each paper *discharges* the hypothesis the previous
one names. The dependencies are between the papers, not on anything left open.

- `proof_setup.tex` — the local pointwise Type I reduction: Seregin extraction,
  concentration and compactness, and the small-amplitude / stationary / uniformly
  $L^3$-tight / structure-and-decay class exclusions. Its Type I contradiction rests on
  one named residual-class hypothesis (`p1:hyp:no-remainder`), and the paper says so
  rather than claiming more than it proves.
- `paperIV_residual_branch.tex` — **proves that hypothesis.** Ordered residual
  decomposition, centered angular-circulation absorption, minimal mesoscopic-scale
  rigidity, and an endpoint sequence-$L^3$ Liouville argument for bounded mild ancient
  solutions yield the refined residual closure. Inserted into the setup paper's final
  assembly, the two-paper chain gives `cor:local-typeI-unconditional`: every
  finite-energy singular point belongs to the local Type II alternative. No global
  critical-norm estimate and no global Liouville theorem are used.
- `type_II_regularity.tex` — the local retained-branch exclusion criterion for the
  remaining alternative: repaired-gauge representation for nondegenerate concentration
  cores, local Calderón–Zygmund pressure control, a Caccioppoli estimate on compact
  cylinders, multibubble and cascade reductions, and scale-collapse cost estimates, with
  the retained compact branch closed by routing into the scale-rigid discharge.
- `ns_perelman.tex` — a localized entropy functional $\mathcal{W}_{\mathrm{loc}}$ on the
  singular-branch state space supplied by the three papers above. This one is
  conditional by design and by its own title: it is an organizing quantity for the
  program, not the load-bearing exclusion.
- `overall_proof_architecture.tex` — the referee guide tying the stratification together.
- `stokes_appendix_body.tex` — supporting Stokes-system material.

**Sequencing.** The order is deliberate and is a property of the framework, not of the
mathematics. Each formalization target must first be expressible as rows over the
canonical ledger; a paper is only queued once its branch structure — the case splits,
the residual promotions, the retained obstructions — has been read off the manuscript
and typed. The concrete next steps:

1. **Finish Erdős–Gyárfás.** Close the open rows, re-root `StrategyDag.lean` on
   `Spine.run`, and drive the whole proof to the pinned public statement. This is the
   only thing that establishes the framework carries a complete argument end to end.
2. **Formalize the methodology's own guarantees.** The audit and assurance layer of
   `branch_closure_methodology_extended.tex` should be theorems about `ExactLedger`,
   not prose about it.
3. **Rebuild the PDE instantiation.** `Hypostructure/PDE/` predates the canonical-ledger
   rewrite and sits outside the live build closure. It is real work — parabolic atlases,
   localization, vorticity, the Navier–Stokes model — and it is *reference*, to be
   rebuilt on the canonical API exactly as the EG rows are, never re-imported.
4. **Port the Navier–Stokes chain**, in dependency order: `proof_setup`, then
   `paperIV_residual_branch`, then `type_II_regularity`, then `ns_perelman`. The chain
   is exactly the residual-promotion structure the ledger is built to track. The setup
   paper names a residual-class hypothesis and promotes it; Paper IV discharges it and
   commits the fact; the final assembly reads that fact back. Formalized, the discharge
   stops being a cross-reference a referee has to chase and becomes a key in the branch
   index — present or absent, checked by the elaborator.

No timeline is claimed for any of this; the targets are large. What the framework adds
is not extra caution about the results but mechanical bookkeeping of where each one is
used: which branch a theorem closes, and which facts were on the ledger when it did.

---

## Citing

Archived on Zenodo — [`10.5281/zenodo.21813635`](https://doi.org/10.5281/zenodo.21813635).
The DOI above resolves to the latest release; each release also receives its own version
DOI.
