# Hypostructure

[![DOI](https://zenodo.org/badge/1322859158.svg)](https://doi.org/10.5281/zenodo.21813635)

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
   ([`proofs/hypostructure_erdos_64_eg/`](proofs/hypostructure_erdos_64_eg/)): a typed
   representation of branch state in which the elaborator, not a referee, checks which
   facts are available on which branch and which obligations remain.

The mathematics lives in the manuscripts; nothing here qualifies or replaces them. What
the tooling adds is a mechanical record of *how each result is used*: which branch it
closes and which facts were on hand when it did.

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

| Proof | Manuscripts | Size |
| --- | --- | --- |
| Erdős–Gyárfás | `original_erdos_64_proof.tex` | 157 steps, 11 panels |
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
- **Hypostructure docs** (`/#/lean`) — a hand-written reference for the Lean framework:
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

This is work in progress. As of this writing:

| Component | Status |
| --- | --- |
| Manuscripts | Erdős–Gyárfás and the three Navier–Stokes papers are complete drafts with chapter-1 diagrams, ledgers and audit tables; the methodology papers are the reference. |
| Proof explorer | Both proofs published, all features above live; the referee mode's Lean/review dimensions read a side-car that no host supplies yet. |
| Framework core | `ExactLedger`, `AtomicCT`, problem registration, fixtures and gates are live and are the only API; the legacy layered API has been removed (`LEGACY_REMOVAL_AUDIT.md`). |
| Erdős–Gyárfás in Lean | Partial. Rows are ported one diagram node at a time onto exact ledgers; the entry spine, surplus dichotomy, Type-B normal-form and degree-four blocks are kernel-checked and wired, later blocks are in progress, and per the audit the full `Assembly` build does not yet close end to end. Every ported row depends only on `propext`, `Classical.choice`, `Quot.sound`. |
| Navier–Stokes in Lean | Not started; queued after the Erdős–Gyárfás application, in manuscript dependency order. |

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
LEGACY_REMOVAL_AUDIT.md            what the canonical-ledger rewrite retired
```

## Citing

Archived on Zenodo at [`10.5281/zenodo.21813635`](https://doi.org/10.5281/zenodo.21813635);
the concept DOI resolves to the latest release.
