# Remaining Airtight Repairs for `type_II_regularity.tex`

## Purpose and audit standard

This document is an edit specification for the repairs that remain in the
current consolidated Type II manuscript.  Packages already implemented in the
manuscript have been removed.  The remaining edits preserve the proof strategy
actually used by the manuscript:

\[
\boxed{
\text{localize}
\;\longrightarrow\;
\text{close the component covered by the available theorem}
\;\longrightarrow\;
\text{promote every residual or failed hypothesis}
\;\longrightarrow\;
\text{recenter, rescale, quotient, or decompose}
\;\longrightarrow\;
\text{repeat}
}
\]

The global no-Type-II conclusion is **not** expected to come from any single global bound. It is an assembly contradiction after every local structural branch has either:

1. been contradicted on its retained local obstruction;
2. been routed to a named adjacent state;
3. been reduced, with an explicit obstruction-transfer map, to an earlier closed state; or
4. been discharged by an imported theorem whose exact hypotheses match the state.

Accordingly, this blueprint does **not** ask a local theorem to prove a global property. It asks that every capsule have an exact local input contract, a correct local calculation, an exact topology and pressure representative, a transported obstruction, and explicit failure routes.

The manuscript already states this philosophy in its abstract and introduction.
The remaining corrections below put cost validation in a strict phase order,
record imported-output ownership, and consolidate duplicated proof-bearing
conventions.

---

## Remaining repair packages

The manuscript already contains the coordinate, domain-buffer, gauge,
pressure, bounded-window, parameter-chart, dependency-direction, and
upper-estimate repairs formerly listed as R1--R10.  The remaining work is:

| Package | Nature | Severity | New deep PDE theorem? |
|---|---|---:|---:|
| R11 | Cost well-posedness and validation phase order | Medium acyclicity | No |
| R12 | Imported-output provenance ledger | High auditability | No |
| R13 | Remove superseded duplicate conventions and add static checks | High consolidation | No |

These are interface, dependency, provenance, and consolidation repairs.  They
do not call for a new global analytic theorem.

---

# Part I. Nonnegotiable architectural invariants

Every edit should preserve the following rules.

## A1. A local theorem closes only its declared local component

If a theorem consumes data on a working cylinder \(Q_R\), its conclusion must be on a strictly smaller core cylinder \(Q_r\Subset Q_R\), unless the statement explicitly carries boundary data. No proof may infer whole-space vanishing from compact-window convergence.

## A2. The pressure is always an atlas, not an unnamed scalar

Every pressure step must specify one of:

- spatial mean subtraction on a fixed ball;
- a localized Calderón--Zygmund pressure plus a harmonic remainder;
- a whole-space Leray/Riesz representative under a declared global input;
- a quotient modulo functions of time;
- a pressure-reconstruction failure or exterior-pressure state.

A local velocity limit never silently determines the harmonic pressure tail.

## A3. Missing hypotheses are outputs

When a coordinate, topology, representative, annular smallness condition, or compactness input is missing, the current capsule must output the corresponding named state. It must not strengthen the hypothesis silently.

## A4. A named state is not closure

A state is closed only when the edge records:

- the closing theorem or imported theorem;
- the exact matching input contract;
- the retained obstruction transported to the target;
- the pressure and topology compatibility;
- and an acyclicity or strict-rank witness when the edge reduces to a previous state.

## A5. The global contradiction is an assembly statement

The final theorem may conclude that no physical Type II branch survives only after the graph has exhausted:

- compact single core;
- bounded-window exit;
- rough core;
- multibubble and cascade;
- gauge degeneracy;
- compact and noncompact scale-collapse states;
- fixed and moving carriers;
- exterior, diffuse, pressure, and critical-tail states;
- terminal retained and residual profile states;
- every remaining named adjacent exit.

The repairs below therefore never replace the state-space proof by a global estimate.

---

# Part II. Detailed repair packages

# R11. Put cost well-posedness, carrier routing, and validation in a strict phase order

## Current source anchors

- local cost well-posedness currently near line 9798;
- `paper7:lem:local-state-data-local-l2`, currently near line 9908;
- cost validation and carrier package immediately following that block;
- the explicit cost-divergence dependency-order lemma currently near line 17343.

## Problem

The manuscript's intended order is largely correct, but some theorem statements and cross-references make it look as though:

- a validation theorem supplies data needed to define the cost;
- a local \(L^2\) lemma assumes and concludes the same fact;
- carrier closure and cost divergence justify one another.

This should be eliminated syntactically.

## Define explicit phases

Assign every cost/carrier theorem a `CostPhase`.

### Phase 0. Retained local data

Inputs already produced upstream:

- represented suitable equation;
- local \(L^\infty L^2\) and \(L^2H^1\);
- pressure representative;
- modulation \(L^1\) or stronger local control;
- working/core cutoffs and buffers.

### Phase 1. Cost well-posedness

Prove every integrand is measurable and locally integrable. No cost divergence or carrier theorem is invoked.

### Phase 2. Canonical identity cost

Define the canonical signed and absolute costs and prove elementary comparisons.

### Phase 3. Fixed and moving cutoff identities

Derive the exact local energy/cost identity and decompose the error into canonical components \(J_1,\dots,J_7\).

### Phase 4. Finite-error or normalized occupation routing

For each component:

- summable error: perturbative closure;
- nonsummable error: normalize blocks and produce the corresponding occupation state.

### Phase 5. Carrier certificates

Route \(J_1\), \(J_6\), \(J_7\) and the other components to their already declared local states.

### Phase 6. Divergent validated cost contradiction

Only now may the cost-divergence theorem use the prior carrier closures.

### Phase 7. Final validation ledger

The validation theorem checks that the candidate used the canonical cost and that all prior phases were satisfied. It does not prove any Phase 0--6 input.

## Specific edit to `paper7:lem:local-state-data-local-l2`

Delete it as a theorem if it is tautological. Replace it by either:

- a definition of `LocalStateData` collecting Phase 0 inputs; or
- a proposition citing `paper5:prop:selected-window-suitable-estimates` as the
  actual producer of local \(L^2\) data.

It must not cite a later no-unrecorded-exit or cost-divergence theorem.

## Acyclicity table

Add a table:

| Theorem label | Phase | May use | Must not use |
|---|---:|---|---|
| cost measurability | 1 | Phase 0 | carrier or divergence |
| moving identity | 3 | 0--2 | carrier closure |
| normalized carrier extraction | 4 | 0--3 | final cost contradiction |
| carrier routing | 5 | 0--4 and earlier state closures | cost divergence |
| cost divergence exclusion | 6 | 0--5 | final assembly |
| validation ledger | 7 | 0--6 | itself |

## Acceptance tests

1. Automatic dependency graph has no cycle.
2. No theorem invokes a theorem with an equal or later phase except an explicitly rank-decreasing reduction.
3. The local energy identity is valid before any conclusion about divergence.

---

# R12. Add a precise imported-output provenance ledger

## Why this is essential

Several statements previously classified as “missing theorems” are not supposed to be proved in this manuscript. They are inputs inherited from the companion papers or are positive contracts defining the retained admissible branch. The paper becomes airtight only if this ownership is visible at every use.

The local architecture permits imports. It does not permit an import to be represented as though its hypotheses were proved by a definition in the current paper.

## Required ledger columns

Add near the beginning of the paper a longtable with:

1. interface name;
2. source file;
3. exact source theorem/lemma label;
4. exact output tuple;
5. target theorem label in the Type II paper;
6. local working and core windows;
7. convergence topology;
8. pressure representative;
9. retained obstruction;
10. named failure output if the import is unavailable;
11. status: imported, proved here, or admissible-branch input.

## Required imported interfaces

At minimum list:

### Concentration entry

Output:

\[
C((x_0,T),r_n)\ge\eta_v>0
\]

along shrinking physical cylinders, plus the physical Type I/Type II dichotomy.

Target:

- physical Type II entry;
- selected retained-core construction;
- retained velocity-floor statements.

### Raw AC concentration chart

Output:

\[
(x_c,\lambda,\rho,U,Q)
\]

with exact AC and distributional chain-rule data.

Failure output:

- chart extraction;
- scale route;
- profile completeness;
- domain failure.

### AC repaired-gauge solve

Output:

\[
(\mu,q,\tau,V,P)
\]

with \(\rho_\tau=\mu^2\), gauge constraints, and corrected Jacobian transversality.

Failure output:

- gauge degeneracy;
- multibubble;
- cascade;
- scale rigidity;
- annular core loss.

### Pressure atlas

Output:

- localized Calderón--Zygmund part;
- harmonic remainder;
- mean/time gauge;
- compactness topology.

Failure output:

- pressure reconstruction;
- exterior pressure;
- pressure-only retained state.

### Terminal active-profile decomposition

Output:

- retained nonlinear component \(U_n\);
- residual \(S_n\);
- parameter orthogonality/grouping data;
- topology in which the residual is small or visible;
- ancestry of each terminal descendant.

Failure output:

- hidden profile;
- diffuse tail;
- exterior;
- profile completeness.

## Replace circular-looking “assumptions supply assumptions” statements

A statement of the form

> the admissible assumptions assign the four representation assumptions, hence the representation assumptions hold

is logically valid only as a class definition, not as an analytic theorem. Label it explicitly as:

- a definition of the admissible represented class; or
- an import discharge proposition whose proof is a list of source labels.

Do not give it the rhetorical status of a new analytic theorem.

## Acceptance tests

1. Every imported noun in a theorem proof has a source label.
2. Every target input is literally contained in the source output, including topology and pressure gauge.
3. Every missing import has a named outgoing state.
4. No final theorem depends on an interface marked merely “assumed” unless the theorem is explicitly conditional on the admissible class.

---

# R13. Consolidate the paper and eliminate superseded duplicate proof-bearing blocks

## Problem

The manuscript contains an early repaired-chart/gauge package and a later AC
package.  Their principal coefficient formulas now agree, but both remain
proof-bearing.  Keeping both active creates:

- duplicated theorem labels or roles;
- ambiguous downstream citations;
- difficulty determining which theorem is canonical;
- risk of future formula drift;
- and false dependency cycles.

## Canonical notation dictionary

Place this table near the beginning:

| Symbol | Meaning |
|---|---|
| \(t\) | physical time |
| \(\rho\) | raw renormalized time |
| \(\tau\) | final repaired time |
| \(x_c(t),\lambda(t)\) | raw concentration center and scale |
| \(U(y,\rho),Q(y,\rho)\) | raw profile and pressure |
| \(\mu(\tau),q(\tau)\) | repaired-gauge scale and translation |
| \(\Lambda=\lambda\mu\) | final physical scale |
| \(X=x_c+\lambda q\) | final physical center |
| \(V(Y,\tau),P(Y,\tau)\) | final repaired profile and pressure |
| \(a=\partial_\tau\log\Lambda\) | final logarithmic scale velocity |
| \(b=\Lambda^{-1}X_\tau\) | final normalized center velocity |

## Consolidation action

1. Make the later AC chart section canonical.
2. Replace the early exact-change section by either:
   - a short forward reference to the canonical section; or
   - a corrected duplicate whose formulas are generated from one macro/definition.
3. Point every local energy, pressure, compactness, cost, and carrier theorem to the same canonical represented equation.
4. Keep only one canonical Caccioppoli theorem. The later version using a genuine temporal buffer is preferable.
5. Keep only one canonical local pressure decomposition statement; all stronger pressure-stability conclusions should be separate conditional corollaries.
6. Keep a single final state ledger and derive summary ledgers from it rather than manually repeating rows.

## Static checks to add to the build process

Run automated searches for forbidden strings or patterns:

```text
a(\tau):=-\Lambda'(\tau)
b(\tau):=-X'(\tau)
d\tau=\Lambda^2 dt
\nabla_Y V=\Lambda\nabla_x u
```

Also check:

- every theorem label is unique;
- every `\cref` resolves;
- every state marked closed has a source theorem or reduction edge;
- every reduction edge decreases the declared rank;
- every pressure convergence statement records the harmonic component;
- every global-looking norm is either an explicit input or replaced by a local/tail split.

---

# Part III. Recommended edit order

## Stage 1. Order cost validation

1. Apply R11 phase numbering.
2. Delete or reclassify tautological local-data lemmas.
3. Topologically sort the cost and carrier subgraphs.

## Stage 2. Record ownership of imported outputs

1. Complete the R12 provenance ledger.
2. Check that each source output matches its target input in window, topology,
   pressure gauge, and retained obstruction.
3. Give every unavailable import a named outgoing state.

## Stage 3. Consolidate and run static checks

1. Apply R13 to remove superseded duplicate proof-bearing blocks.
2. Point downstream theorems to the canonical chart, Caccioppoli, pressure, and
   state-ledger declarations.
3. Run the label, cross-reference, rank, pressure, and forbidden-string checks.

---

# Part IV. Airtightness checklist

A referee should be able to answer **yes** to every item below.

## Profiles and tails

- [ ] Every terminal profile is inherited or constructed by a named theorem.
- [ ] Ancestry and retained obstruction are recorded for every descendant.

## Dependency order

- [ ] Cost well-posedness precedes carrier routing and cost divergence.
- [ ] The closure dependency graph is acyclic or has an explicit strict rank.
- [ ] Final assembly is not used in any theorem that supplies its own hypotheses.

## Imports and final closure

- [ ] Every import has a source label and exact output tuple.
- [ ] Every source output matches the target input in domain, topology, pressure gauge, and obstruction.
- [ ] Every failed import becomes a named state.
- [ ] Every state marked closed cites a direct closure, imported theorem, or valid reduction edge.
- [ ] There are no reachable open terminals in the claimed final theorem.

---

# Part VI. What this repair does and does not claim

These remaining edits preserve the paper's central idea: the proof is a
repeated local operation, not a search for one miraculous global estimate.
They make parameter escape explicit, orient the remaining dependencies, expose
the ownership of imported data, and consolidate duplicated proof-bearing
interfaces.

After the edits, the main proof should read as follows:

\[
\text{physical Type II germ}
\longrightarrow
\text{retained local core or named first failure}
\]

\[
\longrightarrow
\text{correct repaired chart and local suitable equation}
\]

\[
\longrightarrow
\text{compact core / bounded window / rough core / profile or tail split}
\]

\[
\longrightarrow
\text{cost and carrier local routing}
\]

\[
\longrightarrow
\text{terminal retained, exterior, diffuse, pressure, or critical-tail states}
\]

\[
\longrightarrow
\text{local contradiction or reduction for every state}
\]

\[
\longrightarrow
\text{global contradiction by exhaustive assembly}.
\]

This blueprint does not by itself certify every source line.  It records only
the repairs still outstanding after the current manuscript changes.  Once they
are implemented, the manuscript should be re-audited with a mechanically
generated theorem dependency graph and an independent specialist review of the
proof-bearing local capsules.
