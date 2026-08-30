# Hypostructure

[![DOI](https://zenodo.org/badge/1322859158.svg)](https://doi.org/10.5281/zenodo.21813635)

## An interactive structural analysis of difficult mathematical problems

  This site presents an LLM-assisted, interactive analysis of the structures underlying difficult problems in combinatorics and partial differential equations. Each argument is decomposed into a
  case-by-case study of its structural alternatives, showing how established mathematical techniques interact and how individual results depend on one another. Navigable proof diagrams let
  readers inspect each step, trace its supporting results, and follow the subsequent branches of the argument.

  Hypostructure is an ongoing research project with two closely connected goals. The first is to build a detailed structural survey that exposes recurring mechanisms and hidden relationships,
  providing a foundation for developing new mathematical techniques. The second is to create a Lean library for formalizing and automating long structural-exhaustion arguments, so that their
  underlying strategies can be abstracted, reused, and eventually applied to new problems.

  The project is evolving, and its analyses and formalizations remain open to refinement. We warmly welcome mathematicians, formal-methods researchers, and other interested members of the
  community to explore the work, identify gaps, suggest improvements, and contribute new perspectives.

## The framework 
Hypostructure is an ongoing effort to make long *structural-exhaustion* proofs —
arguments organized as a finite tree of case splits, local reductions, and quantitative
estimates, each branch closing by contradiction — readable, auditable, and eventually
machine-checked. The repository contains three things:

1. **The manuscripts** ([`to_formalize/`](to_formalize/)): the methodology papers and the
   proofs written with it — the Erdős–Gyárfás power-of-two cycle problem (Erdős problem
   64) and a three-paper Navier–Stokes regularity chain.
2. **The proof explorer** ([`web/`](web/)): a static site that turns each manuscript's
   dependency diagram into a navigable graph, with the paper's own statements, proofs,
   tables and cross-references behind every step. Live at
   <https://fragiletech.github.io/hypostructure/>.
3. **The Lean 4 framework** ([`hypostructure/`](hypostructure/)) and its first application
   ([`proofs/hypostructure_erdos_64_eg/`](proofs/hypostructure_erdos_64_eg/)): a language
   for writing structural-exhaustion proofs in which the state of a branch — the residual
   problem still open and the facts established so far — is part of the type of every
   step. Steps declare what they read and what they establish, compose only where the
   branch actually supplies their hypotheses, and carry their constraints forward to the
   point of use; the elaborator checks all of it, so a completed assembly is a machine
   verification that the case analysis is exhaustive and every branch closes.

The mathematics lives in the manuscripts and the ongoing lean formalization. The tooling adds is a mechanical record
of *how each result is used*: which branch it closes and which facts were on hand when it did, and is meant to provide
a more comfortable interface for understanding and auditing the proofs and their formalization in Lean

## The method

*Structural Exhaustion* (`to_formalize/structural_exhaustion.tex`, with the reference
manual `branch_closure_methodology_extended.tex`) writes a proof as a diagram of numbered
steps. Every step is a case split, a local reduction, an estimate, or a closure; every
branch either continues on a refined residual problem or ends in contradiction; every
constraint the argument relies on is tracked in a ledger from where it is established
to where it is read. The landing page of the explorer gives a condensed account and a
table of the proof moves.

## The proof explorer

`make web` serves it locally; `make web-build` produces a static `web/frontend/dist/`.
There is no backend. Two proofs are published:

| Proof | Manuscripts | Size                           |
| --- | --- |--------------------------------|
| Erdős–Gyárfás | `erdos_64_proof.tex` | 184 diagram nodes, 12 panels  |
| Navier–Stokes | `proof_setup.tex`, `type_I_residual_closure.tex`, `type_II_regularity.tex` | 333 steps, 23 panels, 3 papers |

For each proof the site offers:

- **Explore** — the diagram as a canvas: select a step to see what it asserts, what it
  does, which branch it sends you down, and the verbatim statement and proof of every
  result behind it; trace a branch upstream or downstream; search across steps and
  results; filter by panel or paper.
- **Referee mode** — the same step re-read as evidence: a status strip (manuscript
  present, placed on a page, dependencies mapped, cases or closure recorded, Lean, kernel,
  wired, …), the constraints available before / read / established at the step with
  unsourced reads flagged, the closure of a leaf, and where each result sits in the PDF.
- **Tables** — the paper's own chapter-1 index (dependency table, constraint ledger,
  node-by-node audit, requirements) as written, with every step number and `\cref`
  linked into the diagram.
- **Notation** — the constants, glossary and macros of each paper.
- **Hypostructure docs** (`/#/lean`) — a reference for the Lean framework:
  the ledger, defining a problem, assembling a proof, and verbatim API signatures.

Everything except the introductions, panel names, methodology section, and Lean docs is
extracted from the LaTeX by `web/tools/extract_proof_graph.py` (standard library only)
and committed as JSON under `web/frontend/public/data/`. `make web-data` regenerates it
and runs structural checks (no numbering gaps, every arrow resolves, the diagram is
connected, every reference exists). Adding a proof is a paper description in
`web/tools/papers/` plus a registry entry; the explorer component under
`web/frontend/src/graph-explorer/` knows nothing about any particular paper and is
reusable on its own. See [`web/README.md`](web/README.md).

## The Lean framework

`Hypostructure/Core` is a domain-neutral kernel implementing the methodology's ledger:

- `ExactLedger Domain residual factKeys` — the single carrier of branch state. The
  active residual and the full list of established facts are *type indices*, so a step
  invoked on a branch lacking its hypotheses is a type error, commits are append-only,
  and fact values are proof-irrelevant (no data smuggled between steps).
- `AtomicCT` — the sealed executor. A step declares a `FactManifest` of exactly what it
  reads and produces; construction primitives require a `FrameworkToken` that only
  framework modules can obtain.
- `Problem` / `Target` — problem registration separated from the theorem statement.
- Finite mathematics the applications need (enumeration, partitions, certified table
  bounds, entropy, dyadic length) and an executable substrate with certified budgets.
- Negative fixtures (`Hypostructure/Fixtures`) that must *fail* to elaborate — a dropped
  fact, a duplicate, a missing requirement, a ledger-opacity breach — so the sealing
  properties are tested rather than asserted.

`Hypostructure/Graph` instantiates it for finite graphs and holds the reusable rows and
runs of the Erdős–Gyárfás argument, stated without naming the problem or its constants.
`Hypostructure/PDE` predates the current API and is outside the build closure; it is
porting reference for the Navier–Stokes work.

### Building

Requires [`elan`](https://github.com/leanprover/elan); toolchain `leanprover/lean4:v4.31.0`
with Mathlib pinned to the matching tag.

```bash
make mathlib-cache     # fetch prebuilt Mathlib artifacts
make framework-build   # build the Hypostructure package
make erdos-build       # build the Erdős–Gyárfás application
make erdos             # check the final theorem's type and axioms
make lint              # total-execution, quarantine, and API-catalog gates
make web-test          # extractor assertions, typecheck, frontend suite
```

## Implementation status

This is work in progress. Everything below was checked against the live source,
the synchronized audit tables, and bounded single-worker checks on 2026-08-30.

| Component | Status                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| --- |-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Manuscripts | Erdős–Gyárfás and the three Navier–Stokes papers are complete drafts with chapter-1 diagrams, ledgers and audit tables; the methodology papers are the reference.                                                                                                                                                                                                                                                                                                                   |
| Proof explorer | Both proofs published, all features above live. Referee mode's Lean and review dimensions are supplied for the Erdős–Gyárfás proof from the checked-in node audit (`web/data/eg_node_audit.json`, folded into the site data by `web/tools/lean_review.py`); the Navier–Stokes document carries no such side-car yet.                                                                                                                     |
| Framework core | Builds (`lake build Hypostructure`). `ExactLedger`, `AtomicCT`, problem registration and the fixtures are live and are the only API; ongoing deprecation of stale code — the quarantine lint gate (`make lint`) currently fails, flagging several previously-quarantined modules back in the build plus a handful of parallel ledger-shaped APIs still to retire. Implementing the high level API of problem-independent proof moves is pending.                                                                                                                                                                                                                                                           |
| Erdős–Gyárfás in Lean | Advanced, not closed. The live code implements the low-entropy route `[49]`–`[52]`, the exact Type-B local chain `[79]`–`[85]`, node `[123]` with its full incoming ledger and exact `[124]`/`[181]` outcomes, routing-only `[125]`, `[153]`, `[157]`, `[168]`, `[170]`–`[171]`, and the covered arms of `[173]`–`[180]`. ExactLedger ancestry is repaired at `[64]`, `[144]`, and `[177]`: `[64]` and `[177]` consume `[75]`–`[77]` through branch-kill and Part IX, while strict-surplus `[144]` returns the manuscript's exact Type-B handoff rather than importing the incompatible low-surplus estimate. `[172a]` has no graph-derived overlap producer, `[181]` and `[182]` remain explicit open residuals, and the final `StrategyDag.lean` topology endpoint is absent. The aggregate Assembly check elaborates these repairs and next stops at a later generic cold-route freshness boundary. See [`Assembly_node_audit.md`](Assembly_node_audit.md), [`EG_LEAN_COMPLIANCE_REMAINING.md`](EG_LEAN_COMPLIANCE_REMAINING.md), and [`EG_incomplete_nodes_repair_plan.md`](EG_incomplete_nodes_repair_plan.md). |
| Navier–Stokes in Lean | Not started; queued after the Erdős–Gyárfás application, in manuscript dependency order.                                                                                                                                                                                                                                                                                                                                                                                            |

The authoritative per-fact and per-node record is
[`Assembly_node_audit.md`](Assembly_node_audit.md): one row per labeled manuscript
result and one per diagram node, each cell updated only from live Lean types, bodies,
and builds. Read it, not this table, for what is done today.

## Repository layout

```
to_formalize/                      manuscripts (methodology, Erdős–Gyárfás, Navier–Stokes)
web/                               proof explorer: tools/ (extractor), frontend/ (site)
hypostructure/                     Lean 4 framework
  Hypostructure/Core/                domain-neutral kernel
  Hypostructure/Graph/               finite-graph instantiation and reusable rows
  Hypostructure/Fixtures/            positive and negative sealing fixtures
  scripts/                           the gates
proofs/hypostructure_erdos_64_eg/  the Erdős–Gyárfás application
Assembly_node_audit.md             implementation status, per fact and per node
audits/erdos-64-red-team/          live red-team reports, summary, and coverage ledger
```

## Citing

Archived on Zenodo at [`10.5281/zenodo.21813635`](https://doi.org/10.5281/zenodo.21813635);
the concept DOI resolves to the latest release.
