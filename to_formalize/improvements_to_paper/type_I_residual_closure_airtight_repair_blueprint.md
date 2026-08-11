# Airtight Repair Blueprint for `type_I_residual_closure.tex`

## Purpose and audit standard

This document is an edit specification for making the residual-branch paper
airtight without changing its proof architecture, weakening any theorem, or
replacing any endpoint argument.  The manuscript already has the correct
global strategy.  The required work is to make its interfaces, ancestry,
pressure representatives, local estimates, and dependency order explicit.

The governing rule is

\[
\boxed{
\text{one ancestral ledger}
\quad+\quad
\text{one residual monotonically reduced by local estimates}
}
\]

Every descendant, defect measure, terminal profile, and compactified state is
a restriction, pushforward, limit, or normalization of the object carried by
that ledger.  None begins an independent classification.  A local estimate
either removes a declared component, passes the surviving residual to the next
row, or produces a named failure state with the same recorded ancestry.

The global contradiction is therefore an assembly statement:

\[
\text{Type I entry profile}
\longrightarrow
\text{normalized residual}
\longrightarrow
\text{successive local reductions}
\longrightarrow
\text{terminal exhaustion}
\longrightarrow
\text{endpoint contradiction}.
\]

The repairs below do not ask any local lemma to prove more than its hypotheses
support.  They require each lemma to expose its exact input, core conclusion,
pressure gauge, retained obstruction, residual output, and place in the single
ledger.

---

## Repair packages

| Package | Subject | Severity | New proof strategy? |
|---|---|---:|---:|
| R1 | Canonical residual ledger and rank | Foundational | No |
| R2 | Imported-output provenance | High | No |
| R3 | Observer action, windows, and coordinate transport | High | No |
| R4 | Pressure atlas and pressure-only routing | High | No |
| R5 | Thresholds, energies, and residual measures | High | No |
| R6 | Descendant ancestry and retained obstructions | High | No |
| R7 | Local class interfaces | High | No |
| R8 | Terminal decomposition and mixed mass | High | No |
| R9 | Critical-tail compactification | High | No |
| R10 | R3 dependency linearization | Critical | No |
| R11 | Deferred claims, theorem roles, and labels | Medium | No |
| R12 | Generator/pressure consolidation | Medium | No |
| R13 | Derived summaries, static checks, and final assembly | High | No |

No package introduces a new global PDE theorem.  Some packages require
splitting a statement into its local construction and its later closure, or
moving a proof-bearing assertion to the point where all of its inputs are
available.

---

# Part I. Nonnegotiable architectural invariants

## A1. The proof carries one residual

Fix a single ordered ledger

\[
R_0=\mathcal R_{\mathrm{pre}},
\qquad
R_{k+1}=R_k\setminus \mathcal C_k.
\]

Affine normalization is performed once, producing the quotient representative
\(\mathcal R^\#\).  The symbols \(\mathcal R\), \(\mathcal R^\#\), and the
terminal residual may denote different stages or representations only when the
transition between them is recorded in the ledger.

The classes

\[
\mathcal C_{\mathrm{ax}},\quad
\mathcal C_{\mathrm{rot}},\quad
\mathcal C_{\mathrm{stat}},\quad
\mathcal C_{\mathrm{aff}},\quad
\mathcal C_{\mathrm{logdiff}},\quad
\mathcal C_{\mathrm{young}},\quad
\mathcal C_{\mathrm{homcrit}},\quad
\mathcal C_{\mathrm{logper}},\quad
\mathcal C_{\mathrm{apcrit}},\quad
\mathcal C_{\mathrm{gen}}
\]

are ledger rows, not parallel proofs.  The affine row is a quotient or routing
step.  The general row is the final survivor after the preceding rows have been
removed; it is not an independently initialized residual.

## A2. A local theorem closes only its declared component

Every proof-bearing interface must distinguish:

- the working cylinder or tube on which the hypotheses hold;
- the compactly contained core on which the conclusion is obtained;
- the coordinate frame and equation used there;
- the obstruction retained on the core;
- the component removed from the current residual;
- the residual or named failure output that remains.

Compact-window convergence never yields a whole-space conclusion unless a
separate expanding-window or tail argument supplies it.

## A3. Pressure data form an atlas

Every pressure occurrence must identify one of the following representatives:

- a localized Riesz pressure plus a harmonic remainder;
- a spatial-mean-normalized pressure on a fixed ball;
- a whole-space Riesz pressure under a declared global hypothesis;
- a quotient modulo functions of time;
- an affine-pressure quotient coordinate;
- a named pressure-compactness or exterior-pressure failure.

The local energy inequality uses the actual, unsubtracted pressure.  Affine or
harmonic subtraction belongs to the compactness and quotient interfaces and
must be restored or accounted for before an energy argument is invoked.

## A4. Positive mass and retained velocity are different outputs

The manuscript uses several lower bounds with different meanings:

- retained velocity \(\mathrm{Vel}_r\);
- quotient CKN energy \(E_r\);
- a raw pressure-atlas quantity \(\mu_n\), which depends on its gauge;
- spatial or logarithmic oscillation;
- normalized source-defect mass.

Their thresholds are fixed once.  No proof may silently replace one by another
or decrease a threshold.  A normalized support profile may inherit positive
source-defect mass without inheriting a positive velocity obstruction.

## A5. A named state is not a closure

A row is closed only when the ledger records:

1. the closing theorem or exact imported theorem;
2. the complete matching input tuple;
3. the pressure and topology compatibility;
4. the transported obstruction or positive source mass;
5. the residual output, if any;
6. a strict rank decrease for a reduction to an earlier row.

## A6. The endpoint order is fixed

The final branch must retain the order already used by the paper:

\[
\text{indecomposability}
\longrightarrow
L^3\text{ control along a sequence}
\longrightarrow
\text{exact bounded mild representative}
\longrightarrow
\text{Albritton--Barker input}
\longrightarrow
\text{contradiction}.
\]

Affine and pressure failures exit through their named rows before this
endpoint.  The sequence-level \(L^3\) statement must not be promoted to a
uniform-in-time bound.

---

# Part II. Canonical ledger and interface schema

## R1. Install the single residual ledger

### Problem

The paper currently contains an early architecture summary, a dependency table
(`tab:typeI-dependency-order`), decision diagrams, a classification table
(`tab:decision-tree-classification`), a glossary, a terminal dependency table
(`tab:terminal-dependency-table`), and a final assembly chain.  These displays
encode overlapping versions of the state order.  Their independent maintenance
makes it possible for a class to appear closed in one display and merely routed
in another.

### Required repair

Add one canonical proof ledger near the initial residual decomposition.  Each
row must contain the following fields:

| Field | Required content |
|---|---|
| Phase/rank | A well-founded stage and the strict direction of every reduction |
| Current residual | The subset or represented residual entering the row |
| Ancestor | The physical or normalized object from which it descends |
| Working/core windows | The domain of the hypotheses and the smaller domain of the conclusion |
| Equation/frame | Physical, parabolically recentered, or covariantly centered equation |
| Pressure | Exact representative, gauge, harmonic part, and affine coordinate |
| Retained obstruction | Velocity, quotient energy, oscillation, or source-defect mass |
| Local estimate | The lemma or proposition applied at this row |
| Removed component | The class discharged by that estimate |
| Failure/survivor | The named state or next restricted residual |
| Status | Constructed, routed, reduced, or closed, with its proof label |

Define every later residual notation by reference to a row of this ledger.
State explicitly that restriction, recentering, weak limiting, and defect
normalization preserve the ledger identifier and add an ancestry edge.

### Acceptance condition

Every state in the final theorem occurs in exactly one canonical row.  Every
other diagram and table is explicitly described as a projection of this
ledger.  The residual diagram contains no return arrow that can be read as
reinitializing or enlarging the residual.

## R2. Replace descriptive imports by exact output provenance

### Problem

The setup dictionary records source labels and displayed numbers, but several
numbers are stale and one source label does not exist in `proof_setup.tex`.
Descriptive phrases such as “terminal concentration theorem” do not specify the
output tuple consumed by Paper II.

### Required repair

Correct the setup dictionary as follows:

| Current entry | Canonical source entry |
|---|---|
| `p0:prop:terminal-concentration` | `p0:prop:concentration-package`, Proposition 5.9 |
| `p0:thm:local-weak-serrin-typeI`, Theorem 8.3 | `p0:thm:local-weak-serrin-typeI`, Theorem 8.4 |
| `p0:cor:paper0-local-typeI-admissible`, Corollary 8.4 | `p0:cor:paper0-local-typeI-admissible`, Corollary 8.5 |
| `p0:lem:local-seregin-extraction`, Lemma 8.6 | `p0:lem:local-seregin-extraction`, Lemma 8.7 |
| `p1:thm:classical-classes`, Theorem 15.8 | `p1:thm:classical-classes`, Theorem 15.7 |
| `p1:thm:known-structure-decay-liouville`, Theorem 15.10 | `p1:thm:known-structure-decay-liouville`, Theorem 15.9 |

Retain the source label as the authoritative identifier and treat the displayed
number as checked metadata.  For every imported result, add a provenance row
with:

- source file and exact producer label;
- exact hypotheses used in the source theorem;
- complete output tuple, including domain and time interval;
- convergence topology on working and core windows;
- pressure representative and gauge;
- retained velocity or concentration output;
- Paper II consumer labels;
- named Paper II output when an import hypothesis fails.

The Type I entry package must produce exactly the Seregin profile supplied by
the imported results.  Later residual classification belongs to Paper II and
must not be attributed to the import.

### Acceptance condition

Every imported assertion in the proof can be checked from one provenance row.
No target theorem consumes stronger convergence, a larger domain, a different
pressure representative, or a stronger obstruction than its producer supplies.

---

# Part III. Local analytic interfaces

## R3. Consolidate the observer action and domain transport

### Problem

The actions denoted by `\mathscr T_{(x,\sigma)}` and `\mathcal R_z` implement
the same covariant observer transformation in separate proof-bearing
definitions.  The duplication obscures when the paper uses an ordinary
first-generation parabolic recentering and when it uses a centered covariant
recentring of an existing descendant.

### Required repair

Choose one canonical covariant action and express the second notation as an
alias or specialization.  Preserve the translation action, the dilation
action, and their semidirect product law.  State in the canonical definition:

- the transformed velocity and pressure, including scaling exponents;
- the transformed space-time point and time interval;
- the Jacobian for every norm and defect measure used later;
- the image and preimage of cylinders and tubes;
- the working/core buffer after transformation;
- the pressure gauge transported by the action;
- the composition law needed for descendant ancestry.

Introduce separate terminology for:

1. the first parabolic extraction from the physical solution; and
2. a centered covariant transformation applied to a recorded descendant.

All later recentering lemmas must cite this definition instead of recomputing
the transformation locally.

### Acceptance condition

Every transformed local estimate can be checked from the canonical Jacobian
and domain formulas.  No two active definitions assign different meanings to
the same observer action.

## R4. Make every pressure transition representative-aware

### Problem

The manuscript has the correct pressure ingredients, including
`lem:local-pressure-decomposition`,
`prop:normalized-pressure-representation`,
`lem:scaled-pressure-compactness-affine`,
`lem:first-bad-pressure-compactness`, and
`lem:actual-pressure-minimal-scale-energy`.  Their interfaces need a single
declared pressure atlas.  In particular, pressure compactness, affine
subtraction, and the actual pressure in the local energy inequality must remain
distinct.

### Required repair

For every pressure-bearing row, record

\[
p=p_{\mathrm{loc}}+h+c(t),
\]

or the corresponding normalized/scaled formula, with the domain of the local
Riesz term, the harmonic remainder, and the time gauge stated explicitly.
Whole-space Riesz reconstruction may be used only where the setup package
supplies the necessary global integrability or finite-energy input.

In blowdown statements, display the coefficient \(\kappa\): it equals the
natural-scale value before blowdown and tends to zero for the scaled
non-affine component in the relevant limit.  Record the affine coefficient as
a separate ledger coordinate.

Use `lem:no-pressure-only-retained-profile` as a routing lemma.  A pressure
lower bound by itself produces one of:

- a pressure/noncompact state;
- a retained affine-pressure coordinate;
- a neighboring velocity lower bound proved through the local Riesz
  decomposition and a finite cover.

It does not certify a nonzero velocity profile without the third argument.

Before applying the local energy inequality, restore the actual pressure and
invoke `lem:actual-pressure-minimal-scale-energy` with its full hypotheses.

### Acceptance condition

Every pressure convergence statement includes the harmonic and affine data.
Every use of a pressure lower bound points to an explicit routing alternative.
Every local energy inequality uses the actual pressure on its declared working
window.

## R5. Freeze thresholds and relate all measures to the residual

### Problem

Velocity retention, CKN energy, pressure-atlas mass, oscillation, and defect
mass appear at different stages.  Similar notation and repeated
normalizations can make them look interchangeable or make a newly normalized
measure look like a new residual.

### Required repair

Add a threshold dictionary near the canonical ledger.  For each quantity,
record its formula, gauge dependence, scaling, fixed threshold, and permitted
implications.  In particular:

- `Vel_r` is the retained velocity obstruction;
- `E_r` is the quotient CKN quantity;
- `mu_n` is interpreted only in its declared pressure atlas;
- spatial and logarithmic oscillations retain their own thresholds;
- a normalized defect measure has unit or fixed source mass by construction,
  not a velocity lower bound.

Whenever a measure is introduced, specify whether it is a restriction,
pushforward, weak limit, Radon--Nikodym component, or normalization of the
current ledger measure.  State the normalization constant and prove it is
positive before division.

### Acceptance condition

No implication between two lower bounds is used without a cited estimate.
Every measure has a visible ancestry chain to the same current residual.

## R6. Split global ancestry into local transfer lemmas and assembly

### Problem

`thm:ancestor-realization-inheritance` appears before many of the local
recentring, pressure, and terminal lemmas that supply its content.  As written,
it functions as a global interface while depending on later cases.  The paper
also needs a precise distinction between retained descendants and normalized
support profiles.

### Required repair

For each descendant operation, provide a local transfer lemma with the same
fields as a ledger transition:

- parent and child ledger identifiers;
- exact coordinate map;
- working/core windows;
- convergence topology;
- pressure representative;
- transported obstruction or source mass;
- failure output.

Cover time shifts, spatial recenterings, tail limits, diagonal lifts, defect
normalizations, and mesoscopic blowdowns.  A retained descendant must carry a
proved positive velocity obstruction.  A normalized support profile need only
carry the positive mass of the source defect used to normalize it.

Move the proof-bearing content of `thm:ancestor-realization-inheritance` after
these local transfer lemmas, or restate the early occurrence as a roadmap and
place the theorem itself at assembly.  The final theorem then concatenates the
local ancestry edges; it does not supply missing local compactness.

### Acceptance condition

Every descendant in the terminal theorem has a finite ancestry chain.  Each
edge states exactly which positive quantity survives.

## R7. Give every structural class a local contract

### Axisymmetric row

The circulation estimate closes only the declared axisymmetric component.  Its
output must enter the already closed no-swirl result with matching coordinates,
pressure representative, core cylinder, and retained obstruction.

### Rotating row

The Coriolis-flux estimate removes the declared rotating component or routes
the survivor to a lower-ranked or terminal row.  The local reduction itself
must not cite the later global closure.

### Stationary row

Scale reselection must record the parent profile, selected scales, centered
coordinates, pressure gauges, and retained obstruction.  The stationary hull
is constructed locally and closed only after the terminal alternatives have
been excluded.

### Affine row

The affine class is a quotient and routing interface.  It records the affine
pressure coordinate and the representative of the non-affine residual; it is
not treated as an ordinary PDE symmetry class.

### Logarithmic, Young-measure, homogeneous-critical, periodic, and almost-periodic rows

For each row, state the local estimate that removes the class, the topology in
which the estimate is stable, and the precise named failure output.  A failure
must remain in the current ledger and pass to the next row with its ancestry
unchanged.

### General row

Define `Cgen` as the residual left after all preceding class rows.  Its theorem
is a terminal exhaustion statement and must not assume an independent copy of
the original residual.

### Acceptance condition

Every local class theorem has one input row and one of two outputs: removal of
that component or a named lower-ranked survivor.  No row concludes global
emptiness by itself.

---

# Part IV. Terminal and critical-tail interfaces

## R8. Keep the active locus paired with the same restricted measure

### Problem

The terminal analysis uses compact, diffuse, noncompact, pressure, and critical
objects, sometimes with separate measure notation.  The proof requires these
objects to be complementary pieces of one residual, not unrelated measures.

### Required repair

Define each terminal state as a pair

\[
(\text{active locus},\;\text{restriction of the current residual measure}).
\]

The compact subthreshold component is closed by CKN through
`lem:compact-subthreshold-regular-residual` before terminal stratification.
Remove the sentence in its proof that invokes `thm:terminal-stratification`;
the latter consumes the lemma and cannot justify it.

Keep a mixed compact--diffuse pair intact until
`thm:no-mixed-compact-diffuse` applies.  Diffuse, escaping noncompact, pressure,
affine, and critical-tail components remain named ledger rows until their own
closure or reduction theorem is invoked.

Make `lem:retained-recentering-alternatives` and
`lem:compact-window-expanding-region-protocol` explicit constructions with
working/core windows and output measures.  Their current theorem-environment
roles are corrected under R11.

### Acceptance condition

`thm:terminal-stratification` is an exhaustion of the residual delivered to
it.  Its alternatives are disjoint or paired exactly as stated, collectively
exhaust that residual, and cite only upstream constructions.

## R9. Carry the full critical-tail tuple until coordinates vanish

### Problem

The critical-tail compactification is naturally a tuple containing the
velocity state, auxiliary state, scale, pressure defects, viscous defects,
affine coordinate, virial coordinate, and support data.  Later statements
sometimes abbreviate this tuple before the suppressed coordinates have been
proved to vanish.

### Required repair

Choose one ordered state tuple, for example

\[
(\overline W,Y,\Lambda;
\Pi_{\mathrm{def}},D_{\mathrm{visc}},A_{\mathrm{aff}},
V_{\mathrm{vir}},S_{\mathrm{supp}}),
\]

using the manuscript's final notation.  State:

- compactness and metrizability of the state space;
- the continuous observer action;
- uniform bounds for every coordinate;
- the positive source mass used in normalization;
- support transfer under convergence;
- the lemma that sets each dispensable coordinate to zero.

All proof-bearing interfaces carry the complete tuple until the cited
vanishing lemmas apply.  Abbreviated notation may then be introduced as a
projection.

### Acceptance condition

No compactness or support theorem depends on an omitted coordinate.  Every
coordinate discarded from the notation has already been proved zero or
irrelevant by a stated projection lemma.

---

# Part V. Dependency and consolidation repairs

## R10. Linearize the R3 closure

### Problem

The current R3 block contains closure backedges:

- `thm:R3-no-attainable-degenerate-family` points forward to
  `cor:R3-closure`;
- `prop:R3-stationary-hull-reduction` uses the no-degenerate-family statement;
- `cor:R3-closure` then cites both;
- `prop:R3S-R3-terminal-reduction` refers to `cor:R3-closure`, while the closure
  cites that reduction.

This makes the logical order circular even if the intended proof is a deferred
post-terminal assembly.

### Required repair

Use the following one-way order:

1. Construct the R3 stationary hull and record its retained obstruction.
2. Reduce every R3 survivor to a named R3S terminal alternative without citing
   R3 closure.
3. Apply the independently proved terminal stratification and its closure
   lemmas.
4. Prove one post-terminal R3 closure theorem.
5. Derive the no-active-stationary-carrier and no-attainable-degenerate-family
   assertions as corollaries of that closure.

Earlier occurrences of the later consequences may remain only as roadmap
statements with no proof-bearing use.  The main entry theorem must invoke the
completed post-terminal closure, not serve simultaneously as an input to it.

### Acceptance condition

The role-aware dependency graph for the R3 block is acyclic.  Removing
`cor:R3-closure` from the file leaves all constructions and reductions
well-formed and only removes the final consequences.

## R11. Give every deferred assertion one proof and a matching role

### Problem

Several labels encode a theorem role different from their LaTeX environment:

| Label | Current role mismatch |
|---|---|
| `hyp:base-seregin-hypotheses` | theorem carrying imported output |
| `hyp:previous-nonresidual` | definition of the previously closed region |
| `thm:R3-no-attainable-degenerate-family` | proposition |
| `thm:R3S-terminal-theorem` | proposition |
| `thm:R3S-no-active-stationary-carrier` | remark |
| `cor:R3S-no-active-degenerate-family` | remark |
| `lem:retained-recentering-alternatives` | corollary |
| `lem:compact-window-expanding-region-protocol` | theorem |

The early architecture section also states conclusions whose proofs are
deferred to terminal sections.  These statements need a unique proof-bearing
location.

### Required repair

Choose canonical labels whose prefixes match their environments and update all
internal references.  Where an external or durable reference may rely on an
old label, add a same-location compatibility alias rather than retaining two
proof-bearing statements.

For each deferred assertion, record:

- the early roadmap occurrence;
- the unique later proof-bearing environment;
- the prerequisites that become available there;
- the canonical label used by downstream results.

An early roadmap must use prospective language and cannot be cited as if the
deferred proof had already been established.

### Acceptance condition

Every formal claim has exactly one proof-bearing occurrence.  Label prefixes
match theorem roles, and compatibility aliases do not create duplicate
statements or dependency nodes.

## R12. Consolidate the generator/pressure calculus

### Problem

`lem:recurrent-core-pressure-gauges` contains a spectral or generator pressure
calculation, while the appendix lemma `lem:generator-pressure-identity`
repeats related proof-bearing calculus.  Maintaining both obscures the exact
operator domain and the handling of the zero mode and gauge quotient.

### Required repair

Select one canonical generator-pressure lemma.  Its statement must specify:

- the operator and its domain;
- the cylinder or compact core on which the identity is tested;
- the resolvent or spectral approximation used;
- the treatment of the zero mode;
- the quotient by functions of time;
- the relation to `lem:local-pressure-decomposition`;
- the topology in which the identity passes to limits.

Replace the other proof by a short application of the canonical lemma, with
only the specialization needed at that location.

### Acceptance condition

There is one proof of the generator calculus and one declared pressure-gauge
convention.  All downstream recurrence and appendix arguments cite that same
interface.

## R13. Derive summaries and final assembly from the ledger

### Problem

The paper's diagrams, classification tables, dependency tables, glossary, and
final proof currently restate portions of the architecture.  Independent
restatement invites rank drift and makes a routed state look closed before its
closure theorem appears.

### Required repair

After R1--R12, rewrite each secondary summary as a projection of the canonical
ledger:

- the early dependency table shows phase order and contains no closure detail;
- the decision-tree table shows local estimate and failure output;
- the glossary points to canonical row definitions;
- the terminal dependency table contains only terminal inputs and closures;
- the final assembly cites every row once in monotone order.

Mark each row with one of four statuses: constructed, routed, reduced, or
closed.  “Assigned,” “removed,” “deferred,” and “previously closed” may be used
only when followed by the relevant ledger row and proof label.

The final assembly must visibly establish:

1. the Type I import and nontrivial normalized profile;
2. affine normalization and the start of the residual ledger;
3. local removal or routing of every structural class;
4. terminal exhaustion of the surviving residual;
5. post-terminal R3 closure;
6. final endpoint closure in the fixed order of A6;
7. emptiness of the original residual by monotonicity.

### Acceptance condition

A reader can reconstruct the proof dependency graph from the canonical ledger
and the imported-output table alone.  All other summaries agree with those two
sources.

---

# Part VI. Recommended implementation order

## Stage 1. Freeze interfaces

1. Correct the imported-label dictionary and add exact output provenance.
2. Install the canonical residual ledger, phase/rank, and threshold dictionary.
3. Declare the canonical observer action and pressure atlas.

## Stage 2. Repair local transfers

4. Add working/core windows and exact residual outputs to each class lemma.
5. Split descendant inheritance into local transfer lemmas.
6. Make every pressure and defect normalization representative-aware.
7. Record all measure restrictions, pushforwards, limits, and normalizations.

## Stage 3. Repair terminal interfaces

8. Pair terminal active loci with restrictions of the current residual.
9. Close compact subthreshold mass before terminal stratification.
10. Carry the full critical-tail tuple through compactness and support transfer.
11. Keep mixed compact--diffuse mass paired until its exclusion theorem.

## Stage 4. Linearize closure

12. Reorder the R3 construction, terminal reduction, terminal exhaustion, and
    post-terminal closure.
13. Give each deferred assertion one proof-bearing location.
14. Correct theorem roles and install same-location legacy aliases only where
    required.

## Stage 5. Consolidate and assemble

15. Consolidate the generator/pressure calculus.
16. Regenerate the diagrams, tables, glossary, and final proof from the ledger.
17. Run the mechanical and referee-facing audits below.

---

# Part VII. Mechanical audit

## Labels and imports

- [ ] Every theorem, proposition, corollary, lemma, definition, and remark label
      is unique.
- [ ] Every `\ref`, `\eqref`, `\Cref`, citation, and setup label resolves.
- [ ] The setup dictionary agrees with the auxiliary file generated from
      `proof_setup.tex`.
- [ ] Every imported output has one exact producer and a complete output tuple.
- [ ] Every theorem-environment role agrees with its canonical label prefix.

## Dependency direction

- [ ] The role-aware graph
      `input -> construction -> local estimate -> reduction -> support transfer
      -> closure -> assembly` is acyclic.
- [ ] No local reduction cites a closure theorem that consumes that reduction.
- [ ] Every deferred claim has one later proof-bearing occurrence.
- [ ] Every edge to an earlier row strictly decreases the declared rank.

## Residual and ancestry

- [ ] Every class is removed from or retained in the current residual exactly
      once.
- [ ] Every descendant has a finite ancestry chain to the Type I entry profile.
- [ ] Every auxiliary measure is a declared operation on the current residual.
- [ ] Every normalization divides by a proved positive source mass.
- [ ] Every retained descendant carries the stated velocity obstruction; every
      support profile carries only the mass actually inherited.

## Pressure and local estimates

- [ ] Every pressure limit records the local Riesz part, harmonic remainder,
      time gauge, and affine coordinate when present.
- [ ] Whole-space pressure reconstruction is used only under its declared
      global input.
- [ ] Every local energy inequality uses the actual pressure.
- [ ] Every pressure-only lower bound routes through
      `lem:no-pressure-only-retained-profile`.
- [ ] Every local theorem distinguishes its working and core windows.

## Build checks

Run three LaTeX passes in a temporary build directory and check:

```text
undefined references
undefined citations
duplicate labels
multiply defined labels
overfull boxes
```

Then run `git diff --check`.  Classify any remaining layout warning and confirm
that the generated PDF contains the corrected setup dictionary, canonical
ledger, and derived terminal table.

---

# Part VIII. Referee checklist

A referee should be able to answer **yes** to every item.

## Architecture

- [ ] The proof uses one residual ledger from the normalized Type I entry to the
      final contradiction.
- [ ] Each local estimate monotonically removes a component or produces a named
      survivor.
- [ ] The general class is the final survivor, not a new residual.
- [ ] No repair changes the proof strategy or weakens a claim.

## Interfaces

- [ ] Every import matches its consumer in hypotheses, domain, topology,
      pressure gauge, and retained obstruction.
- [ ] Every recentering or blowdown records its parent and coordinate map.
- [ ] Every pressure statement uses a declared representative.
- [ ] Every threshold and positive-mass assertion has one fixed meaning.

## Terminal closure

- [ ] Compact subthreshold mass is removed before terminal stratification.
- [ ] Mixed compact--diffuse mass remains paired until its exclusion theorem.
- [ ] The full critical-tail tuple is carried until its extra coordinates are
      proved to vanish.
- [ ] R3 closure occurs after, and only after, terminal exhaustion.
- [ ] The endpoint uses indecomposability, sequential \(L^3\) control, the exact
      mild representative, and the Albritton--Barker theorem in that order.

## Final assembly

- [ ] Every state marked closed cites a direct theorem, an exact import, or a
      strict-rank reduction to an already closed row.
- [ ] Every failed hypothesis becomes a named output.
- [ ] There are no reachable open terminal states.
- [ ] Emptiness of the original residual follows from the monotone ledger and
      exhaustive closure of its final survivor.

---

# Part IX. Intended final reading of the proof

After these repairs, the manuscript should read as one continuous argument:

\[
\text{singular physical germ}
\longrightarrow
\text{exact imported Type I profile}
\longrightarrow
\text{affine-normalized residual}
\]

\[
\longrightarrow
\text{local structural estimate}
\longrightarrow
\text{removed component or named survivor}
\longrightarrow
\text{same residual at lower rank}
\]

\[
\longrightarrow
\text{terminal restriction of that residual}
\longrightarrow
\text{compact/diffuse/pressure/critical-tail exhaustion}
\]

\[
\longrightarrow
\text{post-terminal R3 closure}
\longrightarrow
\text{bounded mild endpoint contradiction}
\longrightarrow
\text{empty residual}.
\]

The result is the existing proof with its logical ownership exposed: one
ledger, one residual, local estimates at every transition, and a final
contradiction assembled only after all named survivors have been closed.
