Agreed. Here is the **actual final-pass list**. It assumes the manuscript, theorem order, Parts I–VIII, all proofs, and the LPN presentation remain intact. No appendicizing, no paper splitting, no companion repository, and no “nonclaims” section.

## Required arXiv preparation

1. **Create a clean submission folder.**

   Use something like:

   ```text
   arxiv_submission/
   ├── main.tex
   └── references.bib
   ```

   Since your figures are generated inside LaTeX with TikZ/PGFPlots, you may not need a figures directory at all.

2. **Rename the main source to `main.tex`.**

   The current filename is `task_space_structural_complexity (11).tex`.  Spaces and parentheses are not accepted in arXiv filenames; arXiv permits only letters, digits, `_ + - . , =`. ([arXiv][1])

3. **Rename the bibliography file to `references.bib` and update the final command.**

   Change:

   ```latex
   \bibliography{task_space_structural_complexity}
   ```

   to:

   ```latex
   \bibliography{references}
   ```

   The current bibliography command is at the end of the source. 

   Upload either `references.bib` or a generated `main.bbl`. If you upload the `.bbl`, its basename must match `main.tex`. arXiv otherwise processes ordinary BibTeX automatically, but it blocks submission when a required `.bib` file is missing. ([arXiv][2])

4. **Do not upload compilation debris.**

   Leave these out:

   ```text
   main.aux
   main.log
   main.out
   main.toc
   main.pdf
   main.synctex.gz
   backup files
   old manuscript versions
   hidden directories such as .git/
   ```

   The zip should contain only what arXiv needs to reproduce the paper. arXiv specifically asks submitters to omit unused figures, backups, intermediate output, and unrelated files. ([arXiv][2])

5. **Compile once from that clean folder rather than from your working directory.**

   Run:

   ```bash
   pdflatex main
   bibtex main
   pdflatex main
   pdflatex main
   ```

   This catches dependencies that were accidentally being loaded from another local directory.

6. **Clear every compilation warning that affects the document.**

   In particular, search the final log for:

   ```text
   Citation ... undefined
   Reference ... undefined
   There were undefined references
   Label ... multiply defined
   File ... not found
   Missing character
   ```

   A practical command is:

   ```bash
   grep -Ei "undefined|multiply defined|not found|missing character" main.log
   ```

   Ordinary harmless box warnings can remain, but inspect every `Overfull \hbox` that could clip an equation, theorem heading, table, or URL.

7. **Shorten the arXiv metadata abstract to below 1,920 characters.**

   The current PDF abstract is approximately **2,130 characters after whitespace normalization**, so it needs a cut of roughly 250–350 characters. Its content and LPN paragraph can remain substantively unchanged. 

   The easiest cuts are purely verbal:

   * compress the long list of covered fields;
   * remove repeated adjectives such as “represented,” “complete,” or “declared” where the sentence already establishes the scope;
   * combine the two sentences describing architecture independence;
   * shorten “including architectures and runtime-generated representations not anticipated in advance” to something like “including unanticipated architectures and runtime-generated representations.”

   Aim for **1,750–1,850 characters**, not 1,919, so minor later edits do not exceed the limit. arXiv rejects metadata abstracts above 1,920 characters. ([arXiv][3])

   > **Validation findings — 2026-08-12 — RESOLVED.** The revised LaTeX
   > abstract gives **1,836 characters** after `detex` extraction and whitespace
   > normalization.  It is below the stated 1,920-character metadata limit and
   > inside the recommended 1,750–1,850-character buffer.  The revision retains
   > the universal capability claim, source-resolved learning and noise
   > results, inverse capability theory, architecture-independent AI scope,
   > and the proof-producing LPN specialization.

8. **Keep a plain metadata version of the title and abstract.**

   The PDF may retain all your ordinary LaTeX. In the arXiv web form:

   * paste an ASCII title;
   * avoid opaque custom macros;
   * avoid Unicode punctuation copied from the PDF;
   * use ordinary hyphens and keyboard quotation marks;
   * do not include the word “Abstract” in the abstract field.

   arXiv metadata fields accept ASCII and only limited TeX/MathJax syntax. ([arXiv][3])

9. **Keep the current title unless you personally want to change it.**

   There is no upload-related reason to rename:

   > *Presentation-Relative Structural Complexity: Quantitative Limits for General Intelligent Computation*

   The current title accurately describes the manuscript.  A title change is not part of the required polish.

   > **Validation findings — 2026-08-12 — PASS.** The source title and PDF
   > metadata title are both exactly *Presentation-Relative Structural
   > Complexity: Quantitative Limits for General Intelligent Computation*.
   > No stale or competing title was found in the manuscript source.

10. **Add one concise LLM-use sentence in the acknowledgments.**

This is the only disclosure addition I would treat as practically necessary because you described significant text-to-text LLM assistance. A restrained sentence is enough:

> Text-to-text generative AI tools were used to accelerate drafting and editorial revision; the author verified and takes full responsibility for all definitions, proofs, calculations, citations, and claims.

arXiv’s current policy says significant text-to-text generative-AI use should be reported according to subject-area methodological norms, that human authors remain responsible, and that the tool should not be listed as an author. ([arXiv][4])

> **Validation findings — 2026-08-12 — OPEN.** The manuscript contains no
> acknowledgments section and no occurrence of “generative AI,” “LLM,” or an
> equivalent tool-use disclosure.  The recommended disclosure has therefore
> not yet been added.

11. **Fill the arXiv comments field with only useful bibliographic information.**

Use the final numbers after compilation:

```text
N pages, M figures. Monograph.
```

You may add “Primary category: cs.AI” only if useful, although the category is already shown separately. arXiv recommends including page and figure counts in the comments field. ([arXiv][3])

12. **Leave journal reference and DOI blank.**

They are not placeholders for “unpublished” or “submitted.” They should remain empty until an actual journal or proceedings reference or DOI exists.

13. **Select `cs.AI` and proceed.**

Do not distort the manuscript to make it appear artificially narrower. The learning, active acquisition, Bayesian, control/RL, attention, and general intelligent computation results already make `cs.AI` a legitimate primary category.

## Small reader-facing polish

14. **Implement option 39 in a minimal form: add a short synopsis, not a new paper inside the paper.**

Make it approximately **2–4 pages**, placed after the abstract and before the full table of contents. Do not add proofs, move theorems, or rewrite the eight Parts.

It should contain only:

* one paragraph describing the presented task and saturated closure;
* the exact universal capability/accountability inequality;
* a compact eight-row map showing what each Part contributes;
* a list of perhaps eight principal theorem references;
* one short paragraph explaining how the empirical certificate construction works.

Much of this is already written. The universal capability box is ready to reuse.  The existing “What this paper introduces” subsection already supplies the prose summary of the presented object, generator decomposition, cost filtration, hitting-time theorem, learning, control, attention, meta-complexity, and LPN application. 

This is primarily a **copy, condense, and cross-reference task**, not new mathematical writing.

> **Validation findings — 2026-08-12 — OPEN.** There is no synopsis between
> `\end{abstract}` and `\tableofcontents`; the only intervening material is the
> schematic “Universal capability bound” box.  Reusable components do exist
> later in Part I: “What this paper introduces,” the eight-Part reading guide,
> the one-page executive theorem map, and the certificate discussion.  They
> have not been condensed into the requested 2–4-page pre-TOC synopsis.

15. **Give the synopsis a straightforward title.**

For example:

```latex
\section*{Synopsis and Principal Results}
\addcontentsline{toc}{section}{Synopsis and Principal Results}
```

Avoid calling it an “executive summary,” “reader warning,” or “scope statement.” It is simply a compact technical map of the monograph.

> **Validation findings — 2026-08-12 — OPEN.** No section titled “Synopsis and
> Principal Results,” or any other pre-TOC synopsis title, occurs in the
> source.  The existing “Executive theorem map” is a later Part I subsection
> on PDF page 26 and is not a substitute for the requested synopsis heading.

16. **Include the exact theorem rather than only the schematic version.**

Keep your existing schematic box, but in the synopsis place the exact central form:

[
\operatorname{Succ}*{\mathfrak M,n}(B)
\le
eH_B(n),
m*{\mathfrak M,n}^{\mathrm{sat}}!\bigl(\Psi(B,n)\bigr).
]

Follow it with one sentence saying that the left-hand side is already optimized over the complete represented computation class at budget (B).

> **Validation findings — 2026-08-12 — PARTIAL.** The pre-TOC box contains
> only the schematic performance/profile inequality.  The exact formula
> appears later as Eq. `eq-architecture-independent-capability-envelope` and
> again in the conclusion, together with the statement that the left-hand
> side is the supremum over all admissible computations.  Because no synopsis
> exists, the exact theorem and optimization sentence are not present at the
> location required by this item.

17. **Add a compact “Principal results by Part” list.**

One or two sentences per Part are enough:

* **Part I:** task presentations, observable structure, saturated derivability, temporal typing.
* **Part II:** arbitrary computation as a transcript generator and exhaustive channel decomposition.
* **Part III:** saturated extraction, first-hit accounting, prospective selector accountability, universal capability bounds.
* **Part IV:** algorithm-agnostic learning, noisy generalization, learned structure and attainable-risk bounds.
* **Part V:** controlled systems, POMDPs, optimal active acquisition, Bellman and implementation certificates.
* **Part VI:** attention as a charged normalized selector within the existing source theory.
* **Part VII:** inverse capability and structural meta-complexity.
* **Part VIII:** LPN specialization and proof-producing finite-to-asymptotic certification.

This adds navigation without changing any existing result.

> **Validation findings — 2026-08-12 — PARTIAL.** Subsection “How to read this
> paper” gives a substantive Part I–VIII description, and Figure 2 maps all
> eight Parts.  Both occur after the full table of contents, and the reading
> guide is substantially longer than the requested compact eight-row synopsis
> list.  The mathematical coverage is present; the requested placement and
> compression are not.

18. **Add a short reading-path paragraph.**

Four lines are sufficient:

* Foundations and complexity: Parts I–III and VII.
* Learning and noise: Parts I, III, and IV.
* RL/control/Bayesian acquisition/attention: Parts I–III and V–VI.
* LPN application: Parts I–III and VIII.

Your individual “Part contract” paragraphs already handle local navigation well.  This merely gives readers the global route once.

> **Validation findings — 2026-08-12 — PARTIAL.** The reading guide contains
> global routes for the framework, LPN, learning, controlled dynamics,
> black-box classifiers, attention/active acquisition, and structural
> metacomplexity.  These routes are accurate and hyperlinked, but they occupy
> seven detailed bullets after the Part-by-Part guide rather than the four-line
> pre-TOC paragraph requested here.

19. **Add a one-page principal-theorem map, not a new contribution section.**

Use three columns:

```text
Result | What it establishes | Location
```

Include only load-bearing results such as:

* saturated derivability closure;
* operational computation embedding;
* structural channel exhaustion;
* exact affordable first-hit quotient;
* prospective selector accountability;
* universal saturated-profile accountability;
* source-resolved learning compilation;
* optimal active/Bayesian/control construction;
* empirical implementation certificate;
* finite-to-asymptotic certificate theorem.

No status taxonomy or “nonclaims” column is necessary.

> **Validation findings — 2026-08-12 — PARTIAL.** The “Executive theorem map”
> occupies exactly PDF page 26 and gives eleven load-bearing nodes, each with
> one sentence, one equation, and one theorem hyperlink.  It is a numbered
> list rather than the requested three-column table, and it omits a dedicated
> active/Bayesian/control construction row.  The structural spine,
> source-resolved learning, inverse frontier, empirical discharge, and LPN
> specialization are covered.

20. **Consider reducing only the global TOC depth from 3 to 2.**

The preamble currently uses:

```latex
\setcounter{tocdepth}{3}
```



Changing it to:

```latex
\setcounter{tocdepth}{2}
```

would preserve all headings and numbering while making the initial table of contents less overwhelming. This is optional; leave it at 3 if you prefer the complete detailed TOC.

> **Validation findings — 2026-08-12 — OPEN (OPTIONAL).** The preamble still
> sets `\setcounter{tocdepth}{3}`.  In the current PDF the detailed table of
> contents runs from pages 2 through 12 before Part I begins on page 13.  No
> technical defect follows from this choice, but the optional reduction has
> not been applied.

21. **Standardize the first-use wording of the five or six core terms.**

In the synopsis and opening pages, consistently use the same short formulations for:

* task presentation;
* represented derivation;
* saturated cost;
* prospective source;
* retrospective accounting;
* saturated profile.

Do not rewrite their definitions. The goal is simply to avoid using two slightly different informal glosses before the reader reaches the formal definition.

> **Validation findings — 2026-08-12 — PARTIAL.** “Task presentation,”
> “prospective source,” and “saturated profile” receive stable explanations in
> the opening pages.  “Represented derivation” first appears in the temporal
> discussion without a short first-use gloss, while the abstract says
> “retrospective explanations” and the exact phrase “retrospective accounting”
> first appears later in the contributions/accounting material.  “Saturated
> cost” is also used in the abstract before the Part I cost-filtration gloss.
> The formal definitions are consistent; the requested uniform first-use layer
> cannot be completed until the synopsis exists.

22. **Check the first twenty pages for accidental repetition.**

Do not delete substantive material. Only remove or tighten sentences that repeat nearly verbatim across:

* the abstract;
* the universal capability box;
* the new synopsis;
* the opening of Part I.

The synopsis should point forward rather than reproduce entire paragraphs.

> **Validation findings — 2026-08-12 — PARTIAL.** A manual comparison of the
> abstract, the page-1 capability box, and the opening of Part I found repeated
> subject matter but no nearly verbatim duplicated sentence: the abstract
> states scope, the box states the schematic envelope, and Part I motivates
> the reversal from algorithm-first to presentation-first analysis.  The
> four-way repetition check remains incomplete because the proposed synopsis
> is absent.

23. **Check every displayed box and table in the front matter at ordinary laptop zoom.**

Specifically verify:

* font size remains readable;
* no table extends beyond the margin;
* hyperlinks work;
* figure captions are not stranded on another page;
* the universal capability equation is legible;
* the channel dictionary does not become too small.

> **Validation findings — 2026-08-12 — PASS WITH MINOR LAYOUT NOTES.** The
> compiled pages containing the front-facing boxes, tables, and maps (PDF
> pages 1, 13, 16–19, 22, 26, and 29) were inspected at a 120-dpi
> laptop-scale rendering.  Nothing crosses a margin; the capability equation
> and channel dictionary are legible; captions remain with their figures; and
> the log contains no overfull box or missing-destination warning.  The
> feature matrix and executive theorem map are dense but readable.  Page 16
> has a large unused lower half after the learning-consequences box, which is
> a pagination inefficiency rather than clipping or loss of content.

24. **Do one mechanical terminology pass.**

Search for inconsistent variants such as:

```text
cost saturated / cost-saturated
source resolved / source-resolved
first hit / first-hit
runtime generated / runtime-generated
family uniform / family-uniform
finite horizon / finite-horizon
target aligned / target-aligned
```

Choose one form and apply it globally. This is exactly the kind of polish readers notice in a large monograph.

> **Validation findings — 2026-08-12 — PASS.** The mechanical count is
> consistent: `source-resolved` 226/`source resolved` 0,
> `runtime-generated` 6/`runtime generated` 0, and `target-aligned`
> 86/`target aligned` 0.  The dominant forms are `first-hit` (328),
> `family-uniform` (193), and `finite-horizon` (141).  The few unhyphenated
> hits are grammatical noun phrases such as “family uniformity,” “a finite
> horizon,” or “first hitting time,” not inconsistent attributive variants.
> The apparent `cost saturated` hit is the unrelated phrase “least-cost
> saturated reclassification.”

25. **Do one theorem-reference pass through the synopsis and introduction.**

Every large claim in those opening pages should point to a specific theorem, corollary, or definition. Avoid generic references such as “proved later” when an exact `\cref{...}` can be used.

> **Validation findings — 2026-08-12 — PARTIAL.** The existing Part I overview,
> contribution hierarchy, architecture-independent capability section,
> executive theorem map, and reading guide attach their load-bearing claims to
> exact definitions, theorems, corollaries, equations, or hyperlinks.  No
> “proved later”/“shown later” placeholder was found in the audited opening
> source.  The page-1 schematic box itself has no theorem link, although its
> exact form is linked later.  A synopsis reference pass is necessarily still
> open because the synopsis has not been created.

26. **Do not alter Part VIII substantively.**

For LPN, perform only mechanical checks:

* all citations resolve;
* every equation and theorem reference points correctly;
* no figure floats past the section it explains;
* the terminology used in the abstract matches the terminology used in Part VIII.

No new qualifications, restructuring, or rewritten claims are part of this pass.

> **Validation findings — 2026-08-12 — PARTIAL; MECHANICAL FLOAT FIXES
> REMAIN.** The current build has no unresolved citation, equation reference,
> theorem reference, multiply defined label, missing character, missing file,
> overfull box, or missing PDF destination warning.  The abstract and Part VIII
> use the same residual-ancestry, deterministic finite-to-asymptotic
> certificate, and conditional-instantiation terminology.  Four figures do,
> however, appear after the next section has begun: Figure 120 (source section
> VIII.3) is on page 575 after VIII.4 begins on page 574; Figures 130–131
> (source section VIII.13) are on page 639 after VIII.14 begins on page 638;
> and Figure 135 (source section VIII.15) is on page 667 after VIII.16 begins
> on page 666.  Figures 121, 129, 134, and 139 share a page with the following
> section but occur before its heading and therefore do not cross it.  No Part
> VIII source was edited during this audit.

## Final packaging and upload

27. **Build the upload archive with `main.tex` at its root.**

From inside the clean folder:

```bash
cd arxiv_submission
zip -r ../submission.zip .
```

arXiv accepts zip or tar archives and compiles the submission from the archive root. ([arXiv][1])

28. **Upload the zip and select PDFLaTeX when prompted.**

Your source uses ordinary PDFLaTeX-compatible packages and TikZ/PGFPlots. Do not upload your locally compiled PDF alongside the TeX source.

29. **Inspect the arXiv-generated PDF rather than assuming the local build is identical.**

Check:

* title and author;
* total page count;
* table of contents;
* first and last theorem numbers;
* bibliography;
* internal hyperlinks;
* TikZ figures;
* wide tables;
* the final notation index;
* the final page.

arXiv requires the submitter to view the generated PDF before completing submission precisely because automated processing can produce unexpected output. ([arXiv][2])

30. **Copy the final metadata from a plain-text file, not from the PDF viewer.**

Prepare:

```text
title.txt
abstract.txt
comments.txt
```

locally, then paste those into the arXiv form. This avoids accidentally introducing Unicode ligatures, curly quotes, or en/em dashes that arXiv metadata rejects.

That is the full realistic pass: **clean folder, valid filenames, complete bibliography, shortened metadata abstract, clean compilation, a compact synopsis using material you already wrote, small navigation improvements, and upload verification.** No changes to the theorem architecture or the LPN argument.

[1]: https://info.arxiv.org/help/submit/index.html "Submission Overview - arXiv info"
[2]: https://info.arxiv.org/help/submit_tex.html "Submit TeX/LaTeX - arXiv info"
[3]: https://info.arxiv.org/help/prep.html "Metadata for Required and Optional Fields - arXiv info"
[4]: https://info.arxiv.org/help/moderation/index.html "Content Moderation - arXiv info"
