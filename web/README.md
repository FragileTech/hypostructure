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

Nothing on the site is hand-written mathematics, with two stated exceptions:
each proof's introduction, in `frontend/src/proofs/registry.ts`, and the panel
names and Erdős panel summaries in `web/tools/papers/`. The Navier–Stokes panel
summaries are the manuscripts' own — they live in each paper's *Diagram map*, so
improving them there improves both the paper and this site.

## Running it

```sh
make web             # installs, regenerates stale data, serves on :5173
```

or directly:

```sh
cd web/frontend && npm install && npm run dev
```

There is no backend. `make web-build` produces a static `frontend/dist/`.

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
| The preamble `\newcommand`s | a macro table, so each paper's notation renders |

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
    src/
      graph-explorer/            the reusable explorer (see below)
      proofs/                    the registry, the loader and their tests
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
   answers and a few paragraphs of introduction.

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
