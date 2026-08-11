# Airtight Repair Audit for `type_II_regularity.tex`

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
All enumerated repair packages have now been incorporated.

---

## Remaining repair packages

The manuscript contains the coordinate, domain-buffer, gauge, pressure,
bounded-window, parameter-chart, dependency-direction, upper-estimate,
cost-phase, imported-output provenance, and consolidation repairs formerly
listed as R1--R13.  There is no remaining repair package in this blueprint.

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

There are no outstanding detailed repair packages.  The R13 consolidation is
enforced by `to_formalize/check_type_II_regularity.py`, available through
`make typeii-paper-check` and also included in `make lint`.

---

# Part III. Continuing audit

Run `make typeii-paper-check` after every manuscript edit.  It checks the
canonical chart, pressure, Caccioppoli, and final-ledger interfaces together
with labels, references, ranks, pressure components, norm scope, and forbidden
formula patterns.

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

The completed edits preserve the paper's central idea: the proof is a
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

This audit file does not by itself certify every source line.  It records that
the specified R1--R13 repairs are implemented; continuing verification should
include the static check above, a mechanically generated theorem dependency
graph, and independent specialist review of the proof-bearing local capsules.
