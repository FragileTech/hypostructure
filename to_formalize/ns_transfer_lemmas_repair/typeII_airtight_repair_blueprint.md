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
The remaining correction below consolidates duplicated proof-bearing
conventions.

---

## Remaining repair packages

The manuscript already contains the coordinate, domain-buffer, gauge,
pressure, bounded-window, parameter-chart, dependency-direction,
upper-estimate, cost-phase, and imported-output provenance repairs formerly
listed as R1--R12.  The remaining work is:

| Package | Nature | Severity | New deep PDE theorem? |
|---|---|---:|---:|
| R13 | Remove superseded duplicate conventions and add static checks | High consolidation | No |

This is a consolidation repair.  It does not call for a new global analytic
theorem.

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

## Stage 1. Consolidate and run static checks

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
They expose the ownership of imported data and consolidate duplicated
proof-bearing interfaces.

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
