# Proof explorer

A static site for reading long proofs interactively. Each paper it hosts draws
its own argument as a dependency diagram of numbered steps; here those diagrams
are navigable. Select a step and you get what it asserts, what it does, which
branch it sends you down, and the statement — and proof — of every theorem,
lemma and definition behind it, as the paper writes them.

Two proofs are published:

| Proof | Source | Size |
| --- | --- | --- |
| **Erdős–Gyárfás** — does every graph of minimum degree three contain a cycle of length a power of two? | `original_erdos_64_proof.tex` | 157 steps, 11 panels |
| **Navier–Stokes** — can a finite-energy solution develop a local singularity? | `proof_setup.tex`, `type_I_residual_closure.tex`, `type_II_regularity.tex` | 333 steps, 23 panels, 3 papers |

The Navier–Stokes argument is written across three manuscripts, each numbering
its own diagram from `[1]`. They are shown as one connected graph whose steps
carry a paper prefix — `S12`, `I12`, `II12` — with a **Paper** filter beside the
panel filter. The detail panel still quotes each paper's own number.

The divider between the diagram and the detail column can be dragged to resize
it; double-clicking it, or pressing `Home` while it has focus, restores the
default, and the width is remembered.

The left rail on the Hypostructure section and on the tables — the table of
contents — folds away behind its **Contents** button, leaving the article the
whole width; the button stays in the gutter to bring it back, and the choice is
remembered per section. Below 900px the same button opens the rail as a drawer
over the article instead, which closes on the backdrop, on `Escape`, and as soon
as an entry is chosen. Both are `SidebarRail` (`frontend/src/components/`) over
the `useSidebar` hook (`frontend/src/hooks/`); the rail is hidden in CSS rather
than unmounted, so every page of it stays addressable.

Nothing on the site is hand-written mathematics, with four stated exceptions:
each proof's introduction, in `frontend/src/proofs/registry.ts`; the panel
names and Erdős panel summaries in `web/tools/papers/`; the landing page's
*The methodology* section, `frontend/src/components/MethodologySection.tsx`, a
condensed reading of `to_formalize/structural_exhaustion.tex` — the account of
Structural Exhaustion, the method both proofs were built with — together with
a table of the proof moves, drawn from the tactic library of
`branch_closure_methodology_extended.tex` and each proof's chapter 1, and an
account of red-teaming and repair built on three repairs read from the
manuscripts' history; and the *Hypostructure*
documentation under `frontend/src/docs/`, described below. The
Navier–Stokes panel summaries are the manuscripts' own — they live in each
paper's *Diagram map*, so improving them there improves both the paper and this
site.

## The Hypostructure section

`/#/lean` is the reference for formalizing structural exhaustion proofs with
the Hypostructure Lean framework (`hypostructure/Hypostructure/Core/`). It is
reached from the header on every page. The section has its own left rail and
is written by hand as TSX, since its source is the Lean code rather than a
manuscript:

```
frontend/src/docs/
  registry.ts          the pages, in reading order, and their rail groups
  DocsLayout.tsx       the rail and the content column
  DocsHomePage.tsx     the section's front page
  DocsPage.tsx         one page by slug, with the previous/next pager
  LeanCode.tsx         <LeanCode> blocks and <L> inline code
  lean-highlight.ts    the small Lean tokenizer behind them
  content/*.tsx        one file per page
```

Today it documents four groups, in reading order: **The ledger**
(`ExactLedger`, reading facts, writing facts, closing a branch), **Defining a
problem** (`Core.Problem`, `Target`, `Progress`, the `ProblemInput` residual,
the fact vocabulary, opening the minimal-counterexample scope), **Assembling a
proof** (how steps, decisions and closures compose into the public statement,
and the interface-replacement exclusion), and **Reference** (verbatim
signatures for the ledger/execution, problem, semantics/replacement and utility
modules). Only live, current-API code is documented, and always in a
problem-agnostic way; when a framework signature changes, the reference pages
under `content/*Api.tsx` are the place to update.

To add a page: write `content/YourPage.tsx` exporting a component whose first
element is a `.docs-header` with the page's `<h1>`, then add an entry to
`DOCS_PAGES` in `registry.ts` (slug, title, summary, group). The rail, the
front-page cards, the pager and the tests pick it up from the registry.

## Running it

```sh
make web             # installs, regenerates stale data, serves on :5173
```

or directly:

```sh
cd web/frontend && npm install && npm run dev
```

There is no backend. `make web-build` produces a static `frontend/dist/`.

## Deploying

`.github/workflows/deploy-web.yml` publishes the site to GitHub Pages on
every update of `main` — a direct push or a merged pull request — and can
also be run by hand from the Actions tab. It installs from
`frontend/package-lock.json`, runs the typecheck and the test suite, builds,
and deploys `frontend/dist/` with the official Pages actions; no `gh-pages`
branch is involved. The site is served at
`https://fragiletech.github.io/hypostructure/`; the hash router and the
relative asset base mean nothing in the code depends on that path.

One-time repository setting: *Settings → Pages → Build and deployment →
Source* must be **GitHub Actions**, or the deploy job fails.

## Regenerating the data

Each proof is one committed JSON file under `frontend/public/data/`. Rebuild
after a manuscript changes:

```sh
make web-data                                          # both, plus the checks
python web/tools/extract_proof_graph.py --proof navier-stokes
```

The extractor uses only the Python standard library. From each manuscript it
reads:

| From the paper | What it yields |
| --- | --- |
| The `tikzpicture` panels | every numbered step, its shape, and each arrow with its branch label |
| Dangling arrows (`continue at [14]`, `from [16]`) | the joins between panels |
| Dashed `route` ellipses | collapsed onto the terminal they re-draw, not counted twice |
| Figure captions | the detail each panel adds, with the drawing legend removed |
| The diagram map (`Part / Nodes / Branch resolved / …`) | what each panel of the argument does |
| The node-by-node audit table | what each step is, the results behind it, and its successor |
| The constraint / retained-fact ledger | the standing constraints and where each is tracked |
| The branch-closure audit | how each terminal closes |
| Every `\begin{lemma}…\label{…}` and friends | the verbatim statement, and the proof that follows it |
| Every labelled display equation | so that `\eqref` in a statement or proof can show the mathematics |
| The constants or glossary table | the numerical constants and symbols |
| Every table of the paper's chapter 1 | published as written, as the **Tables** section |
| The preamble `\newcommand`s | a macro table, so each paper's notation renders |

**The paper's own index is a section of its own.** Chapter 1 of each manuscript
tabulates the argument — a dependency table, a constraint ledger, per-result
requirements, node-by-node audits — and *Tables* shows all of them as written,
one at a time, with a row filter. Every bracketed step number and every `\cref`
in a cell links into the diagram, so the proof can be navigated from the index
as well as from the canvas. Sixteen tables for Erdős, four per Navier–Stokes
paper.

**References are navigable.** A `\cref`, `\ref` or `\eqref` inside a statement
or a proof is resolved against the paper it was written in. One naming a result
some step uses jumps to that step; one naming a numbered display, or an
auxiliary result no step claims, unfolds the mathematics where it stands rather
than moving the reader mid-sentence. Every labelled result is carried for this
reason, not only the ones a step cites.

**Every panel says what its part of the proof does.** That summary is what the
overview cards show, and what the explorer shows when no step is selected — for
the panel in view, or the paper, or the whole proof, whichever is narrowest. The
figure caption is kept separately, for the node-level detail it adds.

**A step shows only its own results.** Where a paper's table attributes results
to a *range* of steps rather than to one, those are kept apart as block context
and listed separately, so a single step never claims everything its block uses.

`make web-data` also runs the structural checks: numbering without gaps in each
paper, every arrow resolving, the whole diagram connected, every cross-reference
pointing at a result that exists, and each proof's expected shape.

## Layout

```
web/
  tools/
    latex_source.py              generic LaTeX reading helpers
    proof_graph.py               the conventions: panels, tables, statements
    papers/erdos64.py            one paper, described as data
    papers/navier_stokes.py      three papers, and how they join
    extract_proof_graph.py       the CLI over those descriptions
    test_extract_proof_graph.py  structural assertions, over every proof
  frontend/
    public/data/*.json           generated, committed
    public/papers/*.pdf          the manuscripts, for the header's download link
    src/
      graph-explorer/            the reusable explorer (see below)
      proofs/                    the registry, the loader and their tests
      docs/                      the Hypostructure documentation section
      pages/ components/ styles/ the site around it
```

## Adding a proof

Two steps.

1. Describe the manuscripts in `web/tools/papers/`. A `ChapterSpec` names the
   source file, the headings that bound its diagrams, and a `TableSpec` for each
   cross-reference table — its column count, and which column carries the node
   numbers, the prose and the `\cref`s. A `ProofSpec` collects the chapters and
   any joins between them. Register it in `papers/__init__.py`.
2. Add an entry to `frontend/src/proofs/registry.ts` with the question the paper
   answers, a few paragraphs of introduction, and its `papers` — the compiled
   PDFs, copied into `frontend/public/papers/`, which the header offers for
   download (one link for a single manuscript, a small menu for several). After
   a manuscript changes, recompile it (`latexmk -pdf` in `to_formalize/`) and
   copy the PDF over again; a test checks every listed file is really there.

Nothing else changes: the routes, the switcher and the explorer are driven by
the registry and the document.

## Reusing the explorer elsewhere

`src/graph-explorer/` knows nothing about any paper. It takes a
`ProofGraphDocument` — steps, arrows, and the results behind each step — and
gives you the canvas, the branch tracing, the search, and the detail panel:

```tsx
<GraphExplorer document={yourDocument} state={state} onChange={setState} />
```

The document type is in `src/graph-explorer/types.ts`; the chapter layer is
optional, so a single-manuscript proof simply omits it. The pieces are also
usable on their own:

| Export | What it does |
| --- | --- |
| `GraphExplorer` | the whole workbench; view state is yours to own, so it can live in the URL |
| `NodeDetailPanel` | the display unit for one step, on its own |
| `indexDocument` | lookup tables for steps, results, panels, papers, constraints and arrows |
| `traceFrom` | walk a branch upstream, downstream or both |
| `buildGraph` / `boundsOf` | lay the document out for the canvas, and frame part of it |
| `layoutGraph` | rank any set of boxes and links |
| `buildSearchIndex` / `matchNodes` | search across steps and the results behind them |
| `useDetailWidth` / `clampDetailWidth` | the resizable detail column, remembered per document |
| `Latex` / `MathProvider` / `parseLatex` | render LaTeX fragments with KaTeX, including the source's own macros |
| `createReferenceResolver` | decide what a `\cref`/`\eqref` names, and whether it jumps or unfolds |

`src/graph-explorer/test-document.ts` holds a six-step toy proof, in two
chapters, used to test the module without reference to any real paper — the
check that it really is reusable.

## Checks

```sh
make web-test        # the extractor's assertions, then typecheck and the suite
```
