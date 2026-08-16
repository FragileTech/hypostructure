# Type I Residual Closure: Interface and Exposition Blueprint

## Purpose

This document specifies presentation and interface edits for
`to_formalize/type_I_residual_closure.tex`.  The proof is mathematically
airtight.  The edits preserve its theorem statements, hypotheses, conclusions,
local estimates, dependency order, and contradiction strategy.

The objective is to make the existing proof easy to audit as one fixed-profile
routing argument.  A reader should be able to identify, at every stage,

1. the current residual state;
2. the local data available in that state;
3. the theorem or estimate applied there;
4. the component closed by that theorem;
5. the descendant or defect state produced when a local hypothesis fails;
6. the obstruction transported to that descendant; and
7. the terminal theorem that closes the resulting route.

The intended editing standard is the one already used for
`type_II_regularity.tex`: keep the original proof architecture, expose every
local input and output contract, synchronize all views of the routing graph,
and make the final contradiction visibly follow from the local closures.

Throughout this blueprint, **local** means attached to the fixed candidate
singular point and to the singularity-generated profile currently carried by
its ancestry ledger.  Coordinate domains such as \(\mathbb R^3\), ancient-time
intervals, centered hulls, and expanding terminal regions describe the chart
in which that current profile is analyzed.  Their analytic role is confined to
that profile and its fixed ledger.  Each norm,
compactness statement, pressure representative, symmetry criterion, and
Liouville input must therefore be recorded with its local owner: the incoming
profile, a realized descendant, a normalized measure on a selected defect
window, a support point produced from that measure by a named theorem, or a
finite-shift pullback of the terminal profile.

### Non-negotiable editorial scope

This blueprint authorizes exposition and interface edits only.  It does not
authorize a change of theorem hypotheses, conclusions, proof strategy, or
dependency order.  An implementation may clarify a bridge, state the exact
input and output of a routing lemma, add a directory or table, or correct a
minor mismatch between the prose and the proof-bearing source.  It may not
replace a proof-bearing construction by a different argument.

Before any item is implemented, it must pass all three checks below.

1. **Proof check.**  The proposed wording is a direct restatement of existing
   definitions, lemmas, and theorem dependencies.
2. **Owner check.**  Each datum belongs to the fixed singular point, the
   selected rescaling sequence, the extracted centered profile, or a named
   realized descendant or selected defect window in that profile's ledger.
3. **Dependency check.**  A routing or assembly theorem appears as a premise
   only after its hypotheses have been produced; later closures appear only as
   downstream consumers.

The following requests are prohibited throughout the blueprint.

1. Replacing the fixed raw hull by a newly defined residual state space.
2. Assuming that a residual profile exists.  Residual existence is used only
   through the contrapositive: surviving positive mass on the selected windows
   produces the next realized datum by the cited compactness or support
   theorem.
3. Assigning the mild identity outside the selected mild branch, or
   transporting mildness without the named inheritance theorem.
4. Assigning retained velocity mass to a descendant without the applicable
   realization, semicontinuity, and heredity statements.
5. Transporting one pressure representative through unrelated recenterings or
   blow-downs.  Each local window uses its own compatible representative and
   gauge.
6. Treating the R2 or R3 sequence-\(L^3\) subcases as entry assumptions.  They
   are conditional routes used only after verification for the current
   realized profile.
7. Using the setup residual theorem or the final assembly as a premise of the
   residual closure that supplies them.

Local concentration remains attached to the fixed singular point.  Extraction
and no-escape remain attached to the selected rescaling sequence.  Boundedness
and suitability belong to the extracted centered profile.  Mildness,
sequence-\(L^3\), and finite-shift mildness enter only when their named local
producer has established them for the realized profile under consideration.

---

## Sources of truth

The implementation must be checked against the following sources, in this
order.

1. **The proof-bearing source:** `to_formalize/type_I_residual_closure.tex`.
   Its mathematical statements and proofs determine the actual routes.
2. **The Navier--Stokes assembly guide:**
   `to_formalize/overall_proof_architecture.tex`.  Its Type I branch, closure
   ledger, dependency tables, and capsules R0--R7 give the end-to-end view of
   the paper inside the three-paper regularity argument.
3. **The proof-architecture protocol:**
   `to_formalize/llm_auditable_proof_architecture_draft.tex`.  It supplies the
   vocabulary of local states, coordinate packages, analytic capsules,
   residual promotion, route edges, reduction edges, and backward
   contradiction.
4. **The completed Type II editing pattern:**
   `to_formalize/ns_transfer_lemmas_repair/typeII_airtight_repair_blueprint.md`.
   It supplies the practical standard for local domains, pressure atlases,
   retained obstructions, named exits, imported-output provenance, and static
   checks.

If a summary table or diagram differs from a proof-bearing theorem, the theorem
and its proof control.  The summary is then synchronized to the theorem.

---

# Part I. The proof architecture that every edit must preserve

## A1. One ancestral ledger and one improving residual obligation

Assume a local pointwise Type I singularity and fix the normalized raw Seregin
profile produced by the setup extraction, together with its ancestry and
normalization ledger.  The profile carries positive compact local velocity
concentration.  The setup decomposition either routes it to a direct class,
which closes locally, or places it in the raw residual class.  Only in the
second alternative does the residual paper begin its refinement.

The ledger records the successive local states through which that obstruction
is routed.  At each state, a local theorem closes the component covered by its
hypotheses.  Any surviving obstruction is promoted to a realized descendant,
quotient state, diffuse defect, critical-tail state, separated-profile state,
or terminal indecomposable state.

Thus the phrase **one residual** refers to one continuing proof obligation with
one inherited ancestry.  It does not require every descendant to be the same
function, to use the same coordinates, or to retain the same representative.
The invariant is the transported obstruction and its realized connection to
the original singularity-generated branch.

The ledger is consequently a routing ledger for the fixed
singularity-generated profile, rather than a nested-set subtraction scheme.
The manuscript must preserve this profile-by-profile routing.

## A2. Each theorem is local to its state

A local theorem consumes only properties already proved for the current
singularity-generated profile or produced at its current node.  A structural
criterion such as axisymmetry, relative equilibrium, or stationary-hull
occurrence selects a state for that profile and belongs only to that state
interface.  The theorem closes only the selected component.  Its conclusion is
one of:

- a direct contradiction with the retained obstruction;
- a realized descendant state;
- a named defect or tail state;
- a quotient or normalization route;
- a reduction to an already closed lower state; or
- a terminal state whose hypotheses have now been produced.

The entry data are exactly the profile-local outputs of the setup extraction:
the centered equation, local suitability, the pressure atlas, normalization
data, ancestry, and positive compact velocity concentration.  Later norms or
mildness properties belong only to the realized profile for which they are
proved.  In particular, sequence-\(L^3\) is manufactured for a terminally
indecomposable realized profile after the preceding local alternatives have
been removed; it is not propagated backward as an entry datum.

## A3. Classification, routing, reduction, and closure are distinct

- A **classification statement** selects a local state or alternative.
- A **route edge** constructs the descendant or defect state used next.
- A **reduction edge** transports the current obstruction to a previously
  discharged state or to a later terminal assembly whose hypotheses are
  explicitly produced.
- A **closure statement** supplies the contradiction for that state.
- An **assembly statement** combines already established local closures.

The early R2 and R3 propositions are reductions, not terminal closures.  Their
class-closure corollaries occur only after the terminal stratification theorem
has been proved.  The revised exposition must keep this distinction visible.

## A4. Descendants carry ancestry through changes of local coordinates

Recenterings, time translates, hull limits, blow-downs, normalized defect
windows, support points produced by named theorems, and terminal profiles may
change:

- center and scale;
- spacetime window;
- centered or physical representative;
- velocity and pressure gauge;
- affine quotient;
- compactness topology;
- and the form in which the obstruction is recorded.

Every proof-relevant descendant must nevertheless satisfy the applicable
realization or support-transfer theorem.  This is the logical link that returns
its terminal contradiction to the original singularity-generated raw profile
along the residual branch.

## A5. Retained velocity and normalized defect support are different interfaces

A retained descendant carries an inherited positive unit velocity
concentration bound only after the named realization and retention statements
have proved it.  A normalized restriction of a selected defect measure carries
positive defect mass on that window.  A support point becomes available only
after the cited weak compactness and support-transfer statement has produced
one from those normalized restrictions.  Positive velocity retention is then
available only when a separate local realization theorem proves it.

Every diagram, table, and local lemma must identify the interface actually
produced at that node.  Positive defect support alone does not imply inherited
positive velocity concentration, and retained velocity concentration alone
does not supply defect support.  When both have been proved for the same
realized datum, both remain available for downstream routing and backward
contradiction.

## A6. Pressure data form a local atlas

Every pressure-dependent capsule uses the representative valid in its own
coordinates and window.  The possible data include:

- the setup-paper pressure atlas;
- a local Calder\'on--Zygmund/Riesz component;
- a harmonic remainder on a smaller interior cylinder;
- a quotient modulo functions of time;
- an affine pressure quotient;
- the normalized pressure arising in a mesoscopic blow-down; and
- a named pressure-atlas-loss or noncompact alternative.

Velocity convergence alone does not identify a harmonic pressure tail.  Every
passage to the limit must cite the local pressure statement that makes the
pressure--velocity product or local energy inequality legitimate.

## A7. The final contradiction is backward assembly

The endpoint contradiction is obtained at a realized local profile.  Its force
returns through every applicable descendant-heredity and defect-support
interface, through the terminal stratification, and finally to the original
singularity-generated raw Seregin profile and its fixed ledger.

The Type I exclusion is then obtained by inserting the companion
residual-closure theorem into the setup paper's local assembly.  The outer
argument fixes the candidate singular profile and its ledger.  Inside that
fixed ledger, the residual statement has the explicit pointwise form
\[
   V\in\calR_{\rm setup}(\calS)\Longrightarrow\bot
\]
for an arbitrary incoming profile \(V\).  Thus residual membership is an
antecedent, not an existence premise: if the antecedent is false the
implication is already satisfied, and if it is true the existing routing
closes the selected row.

---

# Part II. Canonical capsule map

The following map is the backbone of the edited exposition.  It is adapted from
the Type I capsule register in `overall_proof_architecture.tex` and must be
checked against the current theorem bodies before manuscript edits are made.

| Capsule | Mathematical role | Principal source labels | Output or closure |
|---|---|---|---|
| R0 | Fix the normalized raw Seregin profile produced from the candidate singular point; enter the residual branch only after the direct setup classes close | `thm:imported-setup-results`, `hyp:base-seregin-hypotheses`, `hyp:previous-nonresidual` | Fixed setup profile with retained compact velocity concentration, pressure compatibility, normalization data, and ancestry |
| R0b | Realize descendants and transfer support | `def:sequence-realized-residual-object`, `def:retained-vs-support-profile-descendant`, `thm:ancestor-realization-inheritance`, `thm:descendant-heredity` | Proof-relevant descendants remain connected to the original branch |
| R1 | Close the axisymmetric bounded-circulation state selected for the current profile | `thm:R1-exclusion` | The centered circulation equation and axis absorption place that profile in the previously closed no-swirl state |
| R2 | Reduce the rotational state selected for the current profile through compact annular Coriolis-flux windows | `prop:R2-reduction-to-terminal`, `cor:R2-closure` | Previously closed local state or realized terminal concentration profile; deferred closure after terminal assembly |
| R3 | Reduce a retained stationary-hull occurrence of the current profile by scale reselection | `prop:R3-stationary-hull-reduction`, `prop:R3S-R3-terminal-reduction`, `cor:R3-closure` | Previously closed local state or realized stationary terminal profile with the inherited ledger; deferred closure after terminal assembly |
| R4 | Covariant observer and affine/parasitic quotient | `thm:covariant-observer-calculus`, `thm:affine-normalization-dichotomy`, `thm:oscillatory-entry-normalization` | Affine mode routed to the lower quotient stratum or positive non-affine activity retained |
| R5a | Recurrent tail-core rigidity | `thm:recurrent-tail-core-rigidity` | Recurrent tail core closed or routed into the terminal alternatives |
| R5b | Log-diffuse critical tail | `thm:log-diffuse-from-hidden-scale`, `cor:log-diffuse-branch-exclusion` | Selected log-window defect datum routed through its named support-transfer, hidden-scale, and coherent-tail interfaces |
| R5c | Young/variance critical-tail defect | `thm:first-bad-mesoscopic-reduction`, `thm:no-hidden-scale-variance-realized-defects`, `cor:young-branch-exclusion` | Variance defect eliminated by minimal mesoscopic reduction |
| R5d | Coherent homogeneous, log-periodic, or aperiodic tail | `thm:bounded-origin-realization-coherent-tails`, `cor:coherent-critical-tail-branch-closure` | Coherent tail excluded by bounded-origin realization and log-hull rigidity |
| R6a | Paired terminal concentration extraction | `thm:terminal-exhaustion-main` | Realized compact profiles and concentration-deleted residual measures produced from the same selected terminal sequence and diagonal protocol |
| R6b | Inactive and nonconcentrating terminal alternatives | `thm:terminal-inactive-exclusion` | Pure local vanishing and pure exterior escape cannot carry the retained obstruction |
| R6c | Diffuse and mixed compact--diffuse alternatives | `thm:diffuse-defect-compactness`, `thm:diffuse-defect-trichotomy`, `thm:no-mixed-compact-diffuse` | Active, affine, or critical-tail route; mixed remainder excluded |
| R6d | Separated profiles and descendant chains | `thm:active-path-space-recurrence`, `thm:compact-active-descendant`, `thm:no-finite-separated-profile-family` | Infinite chains and finite separated families excluded |
| R7 | Terminal indecomposable endpoint for the realized profile | `lem:atomic-sequence-L3`, `thm:mildness-inheritance-main`, `thm:AB-main`, `thm:R4-final-closure` | Terminally produced sequence-\(L^3\), finite-shift mild pullback, and contradiction with that profile's retained local obstruction |
| Assembly | Fix the setup ledger and an arbitrary incoming \(V\); under the antecedent \(V\in\calR_{\rm setup}(\calS)\), close the affine or retained route selected for this same \(V\) | `prop:setup-residual-handoff-complete`, `thm:typeI-residual-closure`, `cor:setup-residual-hypothesis-proof` | The implication \(V\in\calR_{\rm setup}(\calS)\Rightarrow\bot\) establishes raw-residual closure for the fixed ledger; no residual element is postulated |

The capsule identifiers are audit names.  They need not replace the paper's
class notation or theorem names.

---

# Part III. Interface and exposition packages

## I1. Make the setup export a single public handoff

**Implementation status:** complete.

The manuscript now contains `tab:setup-export-interface`, which records the
exact setup-paper producers, exported data, Paper II consumers, and transport
rules.  The setup-label dictionary and public number map have been synchronized
with `proof_setup.tex`.  The exact-handoff definition identifies
\(\calS\) with the same raw generated hull and normalization data used by the
setup theorem, and the handoff proposition separates the affine quotient row
from the retained residual row without replacing the raw set.  The import convention now distinguishes
the compactness and pressure properties of every raw setup state from the mild
identity available on the setup mild stratum.  Descendant mildness, affine
normalization, realization, and terminal sequence-\(L^3\) remain named local
interfaces in Paper II.

### Source anchors

- `thm:imported-setup-results`
- `def:exact-setup-residual-handoff`
- `prop:setup-residual-handoff-complete`
- `hyp:base-seregin-hypotheses`
- `hyp:previous-nonresidual`
- `def:coarse-residual`
- `cor:paperI-residual-input`
- Appendix `app:setup-label-dictionary`

### Existing route

At the fixed local singular point, the setup paper produces a normalized
centered Seregin profile, local suitability, an admissible pressure atlas,
positive compact local velocity concentration, the mild identity on the
profile's mild stratum, and the closure of the earlier states selected for that
profile.  For an arbitrary incoming profile \(V\) with this ledger, Paper II
assumes only the antecedent \(V\in\calR_{\rm setup}(\calS)\) and closes the
affine routing row or retained residual row selected for this same \(V\).  The
resulting implication proves the raw-residual closure for the fixed ledger
without postulating a residual element.

### Expository edit

Add or complete one compact handoff table near the imported setup theorem.  For
each imported output, record:

- its setup-paper source label;
- the exact object exported;
- the topology or representative convention attached to it;
- the first local result in Paper II that consumes it; and
- whether the item remains invariant or is transported by a named theorem.

The table must distinguish the setup export from results reproved locally in
the Type I implication section.  The local implication may verify that a
physical local pointwise Type I singularity reaches the exported setting, while
the residual proof itself begins from the export.

The dependency boundary is acyclic.  Local concentration, extraction,
pressure, raw-hull, mild-stratum, and already closed lower-class results are
imported premises.  The setup raw-residual closure theorem and the setup final
regularity assembly are downstream consumers.  They must appear only in the
return row of the interface table and must never be listed as premises of
`thm:imported-setup-results` or invoked inside the proof of the companion
residual closure.

### Mathematics preserved

- The preliminary setup theorem package remains an import; the setup
  raw-residual theorem and final assembly remain downstream consumers.
- The setup residual theorem remains the raw-residual closure for the same
  fixed singular-profile ledger; the canonical affine row and retained
  \(\calR^\#(\calS;I,J)\) row are its two exhaustive local routes, not a
  replacement target.
- The setup-paper labels and the existing public theorem labels remain stable.

### Acceptance checks

- Every imported item has one named producer and at least one named consumer.
- No locally proved pressure, compactness, or mildness statement is described as
  an unproved setup assumption.
- No setup result is silently strengthened in Paper II.
- Neither the setup raw-residual theorem nor the setup final assembly is used as
  an imported premise of the residual proof.

## I2. Synchronize the entry map, refined decomposition, and reader guide

**Implementation status:** complete.

The manuscript now distinguishes the physical entry, coarse analytic, refined
terminal, theorem-dependency, and closure views.  The compact routing table
`tab:typeI-residual-routing-interface` supplies the common state interface.
The residual diagram uses a dashed classification-only return edge, and its
caption states that the edge is neither a theorem dependency nor a descendant
construction.  The introduction, figure captions, detailed classification
table, dependency table, reading guide, and final assembly now use the same
resolution and route terminology.

### Source anchors

- `subsec:proof-architecture`
- `def:refined-decomposition`
- `fig:typeI-state-stratification-tree`
- `fig:rendered-entry-tree`
- `fig:rendered-residual-tree`
- `tab:decision-tree-classification`
- `tab:typeI-dependency-order`
- `subsec:reading-guide`
- `sec:final-assembly`

### Existing route

The paper first separates the four principal analytic classes
\(\Cax,\Crot,\Cstat,\Cgen\).  The terminal generic analysis then exposes the
affine, log-diffuse, Young, coherent-tail, and final generic alternatives.  The
ten-way list is the complete refined decomposition.

### Expository edit

Make each visual or tabular view identify its resolution:

- **entry view:** physical local Type I \(\to\) Seregin export;
- **coarse analytic view:** \(\Cax,\Crot,\Cstat,\Cgen\);
- **refined terminal view:** affine, diffuse, Young, coherent-tail, active,
  separated, recurrent, and indecomposable routes;
- **dependency view:** theorem production order;
- **closure view:** direct closure, deferred reduction, or terminal assembly.

Render the backward arrow in the residual classification diagram as a dashed
classification-only edge, or replace it by a textual “continue with the next
criterion” marker.  Its caption must say that it records ordered state
selection and is not a theorem dependency or a recurrence of the proof.

Add a compact route table with the columns:

`state | entry criterion | local producer | transported obstruction | next state or closure`.

The existing classification table may supply this role if its columns are
expanded consistently.

### Mathematics preserved

- The ordered definition of the residual classes remains unchanged.
- The classes need not be intrinsically disjoint outside the stated priority
  convention.
- The final generic residual remains the ordered complement after lower
  alternatives are removed.

### Acceptance checks

- Every state shown in a figure appears in the classification table.
- Every terminal row cites the theorem that closes or routes it.
- No arrow can be read as an unproved logical cycle.
- The introduction, reading guide, dependency table, and final assembly use the
  same class names and route order.

## I3. Expose the lower structural capsule contracts

### Source anchors

- `thm:R1-exclusion`
- `prop:R2-reduction-to-terminal`
- `prop:R2-integrable-subcase`
- `cor:R2-closure`
- `prop:R3-stationary-hull-reduction`
- `prop:R3-L3-subcase`
- `prop:R3S-R3-terminal-reduction`
- `cor:R3-closure`

### Existing route

- If the current incoming profile is selected into R1, its centered
  angular-circulation equation and axis condition give the axis-absorption
  conclusion and route that profile to the previously closed no-swirl state.
- If it is selected into R2, compactly supported annular Coriolis-flux
  functionals produce either a previously closed state or a terminal
  concentration profile realized from the same singular branch.
- If it is selected into R3, stationary-hull realization and scale reselection
  produce either a previously closed state or a realized stationary terminal
  profile carrying the same local ancestry and retained concentration.

### Expository edit

Place a short interface paragraph immediately before or after each principal
reduction theorem.  Record:

- the fixed incoming singular profile and the state currently selected for it;
- the centered, physical, hull, or recentered representative used at that
  state;
- the working and core windows of each estimate;
- the selecting property supplied by membership in that state;
- the retained concentration carried by the ledger, distinguishing whether it
  is analytically consumed at that step or transported for the later
  contradiction;
- the exact output alternatives;
- the theorem that realizes the descendant;
- and the later theorem that closes the terminal output.

For R1, bounded centered circulation is the selecting property of the current
R1 profile.  The circulation equation and the axis condition are the analytic
inputs; the retained compact velocity obstruction remains attached to the
fixed profile but is not consumed by the axis-absorption calculation.  The
contradiction is that the no-swirl output places this same profile in a
structured state removed before residual entry.  This is a direct local
closure and creates no descendant.

For R2, the Coriolis term is used only through the compact annular functional
in `lem:R2-coriolis-flux-localization` and the unit-cylinder concentration
alternative in `lem:R2-annular-flux-active-concentration`.  A co-rotating
profile that satisfies the integrable subcase is routed to the setup closure
because that property has been verified for this profile.  The R2 entry
contract itself consists of the rotational state and the inherited local
profile data.  Otherwise the realized retained output is passed to terminal
stratification.

For R3, the stationary profile must be a hull element realized by scale
reselection from the fixed singular branch and must carry the retained local
velocity interface.  The closure consumes this combined realization,
stationary-hull, and retention contract.  The integrable stationary subcase is
a verified lower-state route for the selected profile.

For R2 and R3, use the words **reduction** and **deferred closure** consistently.
The early propositions must not be summarized as though they already used the
terminal theorem.  The later corollaries should point backward to the reduction
and to the now-available terminal assembly.

### Mathematics preserved

- R1 remains a direct local closure.
- R2 consumes only the localized Coriolis-flux identities and the local
  compactness and concentration data produced for the selected profile.
- R3 is closed only for stationary-hull elements realized from the original
  branch and carrying the stated concentration interface.

### Acceptance checks

- Every R1, R2, and R3 interface names the fixed singular-profile ledger to
  which its current representative belongs.
- State-selection criteria are not restated as assumptions on the incoming
  physical solution or on the rest of the setup hull.
- Every estimate names its local representative and working region.
- The R2 and R3 reduction statements do not cite their own closure corollaries.
- The R2 and R3 terminal outputs satisfy the input contract of
  `thm:terminal-stratification`.
- The lower integrable subcases are conditional routes for the selected
  profile and cite only already available setup closures.

## I4. Consolidate the coordinate, observer, affine, and pressure directories

**Implementation status:** complete.

The manuscript now contains the consolidated local directory
`tab:local-coordinate-pressure-directory`. Its rows distinguish the root
centered chart, ordinary local pressure charts, exact covariant observers,
first-generation physical recenterings, realized normalized descendants,
affine-normalized representatives, and minimal mesoscopic blow-downs. Each
row specifies its local owner, domain, velocity map, pressure representative
or quotient, convergence topology, enabled local input, and named output or
failure route. The paragraph following the table also types every threshold
by its domain and records that compactness, retained mass, mildness, and
sequence-\(L^3\) enter only through their cited local interfaces.

### Source anchors

- `sec:shared-notation`
- `thm:covariant-observer-calculus`
- `lem:typeI-pressure-atlas-compatibility`
- `def:pressure-gauge-affine-quotient`
- `thm:affine-normalization-dichotomy`
- `thm:oscillatory-entry-normalization`
- `lem:local-pressure-decomposition`
- the minimal-scale pressure lemmas preceding
  `thm:first-bad-mesoscopic-reduction`

### Existing route

The paper uses several legitimate local coordinate packages: centered
translations, covariant spacetime observers, first-generation physical
recenterings, descendant recenterings, affine-normalized representatives, and
mesoscopic blow-downs.  Their pressure data form a compatible atlas rather than
a single representative transported through every change of local chart.

### Expository edit

Complete the existing notation, threshold, and gauge directories with one row
for each coordinate package.  Each row must state:

- domain and working/core windows;
- velocity transformation;
- pressure transformation and remaining gauge freedom;
- quotient applied, if any;
- compactness topology;
- local energy or pressure estimate enabled by the package;
- named failure route.

Repeated formulas may be cross-referenced when they define the same action on
the same domain.  Formulas serving different generations or different domains
must remain separate and be labeled by role.

### Mathematics preserved

- First-generation local-window compactness and descendant covariant
  compactness remain distinct interfaces.
- The affine/parasitic stratum remains a quotient/routing state.
- Minimal-scale pressure uses the actual rescaled pressure in the local energy
  inequality, with the harmonic and affine components treated as proved.

### Acceptance checks

- Every pressure--velocity product limit cites a compatible pressure theorem.
- Every local estimate identifies its core and working domains.
- Every gauge change is compatible with the affine quotient used at that node.
- Failure of pressure compactness routes to a named pressure/noncompact or
  affine state.

## I5. Make the paired terminal extraction interface explicit

**Implementation status:** complete.

The manuscript now contains
`tab:selected-terminal-output-directory` immediately after the proof of
`thm:terminal-exhaustion-main`.  The directory is instantiated to the terminal
sequence and diagonal subsequence selected from the fixed singular-profile
ledger.  It distinguishes the realized compact profile, vanishing residual,
diffuse measure data, pressure/noncompact route, and selected critical-tail
window.  Only the compact row produces a profile, and that row cites the
velocity, compactness, realization, semicontinuity, and heredity interfaces
that certify it.  The final column records downstream consumers and supplies no
premise to the paired decomposition.

### Source anchors

- `def:terminal-measures`
- `thm:maximal-active-family`
- `def:active-removed-residual-measure`
- `lem:compact-window-expanding-region-protocol`
- `lem:compact-subthreshold-regular-residual`
- `lem:gauge-compatibility`
- `lem:no-pressure-only-retained-profile`
- `lem:first-generation-local-window-compactness`
- `lem:ancient-profile-covariant-compactness`
- `lem:retained-recentering-alternatives`
- `thm:terminal-exhaustion-main`

The following labels are downstream consumers, not premises of the paired
decomposition:

- `thm:terminal-inactive-exclusion`
- `thm:diffuse-defect-compactness`
- `thm:diffuse-defect-trichotomy`
- `thm:no-mixed-compact-diffuse`
- the named pressure/noncompact and critical-tail routing theorems

### Existing route

Fix the terminal sequence selected from the singular-profile ledger.  The
local concentration-set extraction and expanding-region protocol choose one
diagonal subsequence.  On that subsequence, the active loci
\(A_{n,m}^{\eta}\) and the concentration-deleted restrictions

\[
\mu_n\lfloor
\bigl(E_n^{(j)}\setminus U_\rho(A_{n,m}^{\eta})\bigr)
\]

are formed from the same chartwise raw measure, threshold, deletion radius,
and selected terminal region.  A compact profile exists only when positive
velocity concentration and the applicable local compactness theorem produce
it.  A residual restriction is measure data; it is not declared to be an
ancient profile.

### Expository edit

After `thm:terminal-exhaustion-main`, add a terminal-output directory for this
selected terminal sequence.  Its final column lists later consumers and is not
used in the proof of the paired decomposition.

| Selected output datum | Exact local certification | Object produced at this stage | Downstream route only |
|---|---|---|---|
| compact retained profile | a selected observer sequence has a positive unit velocity threshold and satisfies the applicable first-generation local-window or descendant covariant compactness contract | a realized bounded suitable profile with the pressure gauges attached to its local charts; descendant retention additionally cites realization, semicontinuity, and heredity | descendant, separated-family, chain, or atomic analysis |
| vanishing residual | the concentration-deleted restrictions tend to zero in the selected compact-window and expanding-region protocol | no residual profile | `thm:terminal-inactive-exclusion` may later use this only as a sole-carrier exclusion for the selected extraction |
| diffuse residual measure | positive concentration-deleted mass escapes the compact observer exhaustion while every selected unit window is subthreshold | normalized restrictions and, after subsequence extraction, a weak-* probability measure on the fixed observer compactification \(\overline Z\); no ancient solution is asserted | diffuse routing; compact--diffuse coexistence remains recorded until `thm:no-mixed-compact-diffuse` is available |
| pressure/noncompact alternative | a selected residual recentering loses the local Seregin compactness or the chartwise pressure-gauge control required on its own windows | a named failure alternative, not a retained profile | the named pressure, affine, diffuse, or critical-tail routing theorem |
| critical-tail window | no selected unit observer carries the retained velocity threshold, no local compactness failure occurs, and positive residual mass first appears on a selected annular or logarithmic scale | a normalized selected window or defect datum; no Young, log-diffuse, or coherent profile is asserted at this stage | critical-tail extraction followed by the dependency order recorded in I6 |

Record separately that the compact subthreshold regular residual is removed by
`lem:compact-subthreshold-regular-residual` before the surviving output rows
are used.  Each pressure entry names the representative and time gauge valid
on its selected local window.  No pressure representative is transported to a
different recentering or blow-down without the corresponding chartwise
compatibility statement.

### Mathematics preserved

- The table is an interface summary of the existing paired decomposition; it
  introduces no new object, hypothesis, compactness assertion, or route.
- Local vanishing and exterior escape are used only as sole-carrier exclusions
  for the retained compact obstruction of the selected extraction.
- A diffuse remainder may coexist with a compact retained profile at the
  decomposition stage.  That particular coexistence is handled only later by
  `thm:no-mixed-compact-diffuse`.
- Pressure-only activity never substitutes for retained velocity concentration.
- Mildness, sequence-\(L^3\), finite-shift mildness, the setup residual theorem,
  and final assembly do not occur among the inputs to this interface.

### Acceptance checks

- Every output of `thm:terminal-exhaustion-main` has a named downstream route.
- The active locus and every residual restriction use the same selected
  terminal sequence, diagonal subsequence, threshold, deletion radius, and
  named terminal region.
- A compact retained profile is recorded only after positive velocity
  concentration and the applicable local compactness contract have produced
  it.
- A diffuse output is recorded first as normalized measure data on the fixed
  observer compactification.  If later exclusions leave positive mass on the
  selected windows, the cited support theorem produces a support point outside
  those exclusions.  This is a contrapositive and never an existence
  assumption.
- Each descendant carrying retained mass cites its realization,
  semicontinuity, and heredity interfaces.
- Each pressure-dependent row uses the representative belonging to its own
  local chart.
- Downstream closure and assembly theorems occur only in the route column and
  are not premises of the paired decomposition.

## I6. Display the true critical-tail dependency order

**Implementation status:** complete.  The manuscript now contains
`tab:critical-tail-local-dependency-directory`.  It is a directory of the
existing theorem interfaces, not an additional argument.  Its rows are
instantiated only for the current pre-quotient profile, the current realized
coherent tail, the selected first-bad scale, the selected tight annular
blow-down, or the selected normalized log windows.  The actual pressure used
in the first-bad local energy inequality and the later affine-quotient pressure
are cited separately.  The terminal stratification and generic closure occur
only in the consumer column.  No theorem statement, proof body, profile class,
or proof order was changed.

### Source anchors

- `thm:diffuse-defect-compactness`
- `lem:diffuse-defect-support-transfer`
- `thm:diffuse-defect-trichotomy`
- `thm:oscillatory-entry-normalization`
- `lem:actual-pressure-minimal-scale-energy`
- `lem:first-bad-pressure-compactness`
- `thm:first-bad-mesoscopic-reduction`
- `thm:no-hidden-scale-variance-realized-defects`
- `cor:young-branch-exclusion`
- `thm:log-diffuse-from-hidden-scale`
- `cor:log-diffuse-branch-exclusion`
- `thm:bounded-origin-realization-coherent-tails`
- `cor:coherent-critical-tail-branch-closure`
- `cor:critical-tail-exclusion-complete`

### Existing route

The coherent critical-tail alternatives are closed independently by
bounded-origin realization and log-hull rigidity.  Minimal mesoscopic reduction
then eliminates hidden-scale variance.  The Young branch follows from that
variance exclusion.  The log-diffuse branch begins with the normalized data on
the selected log windows; its support point is used only after the named local
support theorem has produced it.  The branch then uses hidden-scale exclusion
and the already closed coherent alternatives.

### Expository edit

Insert one dependency diagram or table using the actual proof order:

\[
\begin{gathered}
\text{affine routing},\qquad
\text{coherent-tail closure},\qquad
\text{minimal mesoscopic reduction},\\
\Downarrow\\
\text{no hidden-scale variance}
\Longrightarrow
\begin{cases}
\text{Young closure},\\
\text{log-diffuse closure together with coherent-tail closure},
\end{cases}\\
\Downarrow\\
\text{complete critical-tail closure}.
\end{gathered}
\]

For each selected blow-down or normalized defect window, record separately
which interfaces have already been proved: realized ancestry, retained
velocity concentration, positive normalized defect mass, and a support point
produced by a named theorem.  Cite the applicable heredity or support-transfer
statement.  When two interfaces have been proved for the same realized datum,
retain both in the singular-profile ledger.

This item adds only a dependency diagram or table.  It does not request a new
compactification, profile class, state space, theorem, or hypothesis.  A later
closure appears as a consumer of the selected local output and never as a
premise of the theorem producing that output.

### Mathematics preserved

- Coherent-tail closure does not depend on the later log-diffuse conclusion.
- The Young and log-diffuse rows share the minimal mesoscopic mechanism without
  being identified as the same state.
- The variance Liouville theorem is used only after the local blow-down and
  pressure interfaces have produced its hypotheses.
- Each row is instantiated to the current realized profile or selected defect
  window in the fixed ledger.

### Acceptance checks

- The dependency diagram agrees with `tab:typeI-dependency-order`.
- No theorem cites a closure that is downstream from itself.
- Every pressure, viscous, affine, and Young defect coordinate has an explicit
  route or closure.

## I7. Expose how the endpoint hypotheses are manufactured

**Implementation status:** complete.  The manuscript now contains
`tab:atomic-endpoint-input-production` and
`tab:terminal-indecomposable-production`.  The first table records the
conditional endpoint argument for the current realized indecomposable profile;
the second records the independent routing which produces indecomposability for
the remaining selected single profile.  Retained concentration, sequence-\(L^3\),
finite-shift mildness, and endpoint vanishing are assigned to their exact
selected owners.  Pressure remains attached to the chart in which each routing
step is performed.  The implementation changes no theorem statement, proof
body, profile class, hypothesis, or proof order.

### Source anchors

- `def:finite-separated-profile-family`
- `def:atomic-terminal-profile`
- `lem:descendant-to-separated-family`
- `lem:atomic-sequence-L3`
- `prop:bounded-mild-stability`
- `thm:mildness-inheritance-main`
- `thm:AB-main`
- `lem:no-atomic-active`
- `thm:ancestor-realization-inheritance`
- `lem:diagonal-lifting-descendants`
- `thm:descendant-heredity`
- `lem:no-pressure-only-retained-profile`
- `lem:finite-successor-alternatives`
- `lem:no-inactive-successor`
- `thm:active-path-space-recurrence`
- `thm:compact-active-descendant`
- `lem:finite-graph-cycle`
- `thm:no-finite-separated-profile-family`
- `prop:no-multi-implies-atomic`
- `thm:terminal-stratification`

### Existing route

There are two distinct theorem-production phases.

First, the atomic endpoint argument is conditional.  If the current realized
terminal profile is terminally indecomposable, then
`lem:atomic-sequence-L3` produces its backward sequence-\(L^3\) bound.
`thm:mildness-inheritance-main` either routes that profile to the
affine/parasitic lower state or produces the bounded mild physical pullback of
the same profile after a fixed finite terminal shift.  Critical scaling carries
the selected sequence-\(L^3\) bound to that shifted pullback.  `thm:AB-main`
then makes the shifted pullback zero, and `lem:no-atomic-active` transports this
conclusion back to the current centered profile and contradicts its retained
local velocity concentration.

Second, the terminal routing uses the already proved no-atomic result and the
independent no-infinite-chain result to exclude a finite separated family.
Only after that exclusion does the deferred proof of
`prop:no-multi-implies-atomic` show that the remaining selected single profile
is terminally indecomposable.  The conditional atomic exclusion then applies
to that profile.  Thus `prop:no-multi-implies-atomic` is not a premise of the
earlier proof of `lem:no-atomic-active`.

### Expository edit

Add an endpoint input-production directory with two visibly separated parts.
Every row is conditional on the current profile having reached the state named
in its first column.

#### Part A: conditional atomic exclusion

| Selected owner | Existing producer and exact prerequisite | Produced fact for that owner | Later consumer only |
|---|---|---|---|
| current realized terminal profile \(U\) with retained local velocity concentration | `thm:ancestor-realization-inheritance` at the root and `thm:descendant-heredity` at each realized descendant step | retained nonzero velocity concentration for this \(U\) | final contradiction in `lem:no-atomic-active` |
| the same \(U\), after terminal indecomposability has been established or assumed conditionally | `lem:atomic-sequence-L3`; its hypotheses are affine-normalized membership in the realized terminal class, retained local velocity concentration, and terminal indecomposability | a selected sequence \(\tau_k\to-\infty\) with \(\sup_k\|U(\tau_k)\|_{L^3}<\infty\) | `lem:no-atomic-active` |
| the same \(U\) on the non-affine branch | `thm:mildness-inheritance-main`, through `prop:bounded-mild-stability`, after the affine/parasitic alternative has been routed for this profile | for each fixed \(T<0\), the selected physical pullback \(u^T\) is a bounded mild ancient solution | `thm:AB-main`, only after the sequence input has also been transported |
| the selected \((U,\tau_k)\) and a fixed \(T<0\) | the critical scaling calculation in `lem:no-atomic-active`, with \(t_k=-e^{-\tau_k}\) and \(s_k=t_k-T\) | \(s_k\to-\infty\) and \(\|u^T(s_k)\|_{L^3}=\|U(\tau_k)\|_{L^3}\) | `thm:AB-main` |
| the selected bounded mild pullback \(u^T\) carrying that sequence | `thm:AB-main` | \(u^T\equiv0\) | the pullback step in `lem:no-atomic-active` |
| the current centered profile \(U\) | `lem:no-atomic-active`, using arbitrary finite \(T\) and the preceding output | \(U\equiv0\), contradicting the retained local velocity concentration of this same \(U\) | finite separated-family exclusion and terminal routing |

The sequence-\(L^3\) row records a conclusion of
`lem:atomic-sequence-L3`, not an entry condition on an R2 or R3 profile.  The
mild row records only alternative (ii) of
`thm:mildness-inheritance-main`; alternative (i) is routed to the
affine/parasitic lower state.  The endpoint theorem acts on the selected
finite-shift pullback \(u^T\), not directly on every centered profile.

The endpoint directory carries no pressure representative from one recentering
to another.  Pressure-loss cases occurring in `lem:atomic-sequence-L3` retain
the representative supplied for their own local chart and are routed through
`lem:no-pressure-only-retained-profile`.  Pressure is not an additional
endpoint hypothesis.

#### Part B: production of the terminal indecomposable state

Record the following theorem order separately:

| Selected input | Existing producer | Produced local conclusion | Later consumer only |
|---|---|---|---|
| an infinite retained descendant chain realized through the named lifting and heredity interfaces | `thm:compact-active-descendant` | that selected chain is excluded | `thm:no-finite-separated-profile-family` and terminal routing |
| a selected finite separated family | `lem:finite-successor-alternatives`, `lem:no-inactive-successor`, and `lem:finite-graph-cycle`, followed by the already proved `lem:no-atomic-active` and `thm:compact-active-descendant` | that selected finite family is excluded by `thm:no-finite-separated-profile-family` | `prop:no-multi-implies-atomic` and terminal routing |
| the remaining selected single retained profile, after finite separated, mixed compact--diffuse, and routed noncompact alternatives have been excluded for that profile | `prop:no-multi-implies-atomic`; a retained concentrating tail limit would give a finite two-profile family by `lem:descendant-to-separated-family` | terminal indecomposability of this selected profile | the already proved conditional exclusion `lem:no-atomic-active` |
| the selected terminal extraction after every preceding route has been resolved | `thm:terminal-stratification` | terminal exhaustion | downstream residual closure and final assembly only |

The finite separated-family theorem continues to use its finite directed
successor graph and the independent no-infinite-chain and no-atomic results.
Neither `prop:no-multi-implies-atomic` nor `thm:terminal-stratification` is a
premise of that theorem.  The table records no assertion that an atomic or
residual profile exists: each atomic row is a conditional route for the
current profile selected by the terminal extraction.

### Mathematics preserved

- `lem:no-atomic-active` is proved conditionally from the definition of
  terminal indecomposability and does not use
  `prop:no-multi-implies-atomic`.
- `thm:no-finite-separated-profile-family` uses the independent no-atomic and
  no-infinite-chain conclusions.  The deferred proof of
  `prop:no-multi-implies-atomic` occurs afterward.
- Sequence-\(L^3\) is produced only for the current realized terminally
  indecomposable profile.
- Finite-shift mildness is produced only for that profile after the named
  inheritance theorem selects its non-affine branch.
- The endpoint theorem is applied only to the selected finite-shift pullback
  carrying the transported sequence-\(L^3\) bound.
- The zero conclusion is returned to the same centered profile and conflicts
  with the retained local velocity concentration carried by its cited
  realization and heredity chain.
- R2, R3, the setup residual theorem, and final assembly are downstream
  consumers.  They supply no premise to either part of the directory.

### Acceptance checks

- Every row is instantiated to the current realized profile, selected sequence,
  fixed finite shift, or selected descendant chain.
- Every retained velocity statement cites the realization and heredity
  interface which supplies it; no unrelated descendant receives retained mass.
- The mild identity appears only after
  `thm:mildness-inheritance-main` has selected the non-affine alternative for
  the current profile.
- Each pressure-dependent routing step uses the representative belonging to
  its own local chart.
- Sequence-\(L^3\) is absent from the R2 and R3 entry hypotheses and appears
  only as the output of `lem:atomic-sequence-L3` for the realized terminal
  profile.
- `thm:AB-main` is absent from upstream compactness, classification,
  recurrence, and finite-graph arguments.
- `thm:no-finite-separated-profile-family` uses neither
  `prop:no-multi-implies-atomic` nor `thm:terminal-stratification`.
- `thm:terminal-stratification`, the setup residual theorem, and final assembly
  occur only as downstream consumers.
- The edit adds only an endpoint dependency directory.  It changes no proof
  body, theorem statement, profile class, state space, hypothesis, or proof
  order.

## I8. Synchronize final assembly, auxiliary views, and static checks

**Implementation status:** complete.  This item is a
source-synchronization pass.  It adds a final selected-owner directory, corrects
three overbroad sentences, synchronizes the Type I architecture capsules, and
adds a structural checker.  It changes no analytic argument, profile class,
hypothesis, or proof order.  The displayed residual conclusions are restated
in pointwise implication form only to expose their existing contrapositive
logic.  The checker passes, and both the manuscript and architecture documents
compile without undefined references or new layout warnings.

### Source anchors

- `tab:typeI-dependency-order`
- `tab:terminal-dependency-table`
- `tab:critical-tail-local-dependency-directory`
- `tab:atomic-endpoint-input-production`
- `tab:terminal-indecomposable-production`
- `def:refined-decomposition`
- `thm:R1-exclusion`
- `prop:R2-reduction-to-terminal`
- `cor:R2-closure`
- `prop:R3-stationary-hull-reduction`
- `prop:R3S-R3-terminal-reduction`
- `cor:R3-closure`
- `thm:affine-normalization-dichotomy`
- `thm:oscillatory-entry-normalization`
- `thm:no-hidden-scale-variance-realized-defects`
- `lem:critical-tail-defect-coordinate-closure`
- `lem:log-window-support-transfer`
- `lem:renormalized-log-window-heredity`
- `cor:coherent-critical-tail-extraction`
- `thm:bounded-origin-realization-coherent-tails`
- `thm:realized-critical-tail-rigidity`
- `cor:coherent-critical-tail-branch-closure`
- `cor:young-branch-exclusion`
- `cor:log-diffuse-branch-exclusion`
- `cor:critical-tail-exclusion-complete`
- `thm:terminal-stratification`
- `thm:generic-terminal-exhaustion`
- `thm:R4-final-closure`
- `sec:final-assembly`
- `thm:refined-residual-closure`
- `prop:setup-residual-handoff-complete`
- `thm:typeI-residual-closure`
- `cor:setup-residual-hypothesis-proof`
- `cor:two-paper-local-typeI-exclusion`
- Type I capsules in `overall_proof_architecture.tex`
- `check_type_II_regularity.py` as a structural-checking model only

### Existing route

Fix the incoming profile and its setup ancestry ledger.  If that profile were
in the literal setup raw-residual class, the exact handoff theorem would route
its canonical representative either to the affine/parasitic quotient row or to
the refined residual decomposition.  Each refined row is then closed by its
existing local reduction or closure theorem.  The R2 and R3 routes consume
`thm:terminal-stratification` only after producing a selected terminal sequence
satisfying its hypotheses.  The generic route instead uses
`thm:generic-terminal-exhaustion` and the named branch closures in the proof of
`thm:R4-final-closure`.  After the refined alternatives have been excluded,
`prop:setup-residual-handoff-complete` is applied contrapositively to the same
incoming profile and ledger.  This proves the literal setup raw-residual
theorem.  The setup paper's final assembly is the last consumer.

### Expository edit

#### Final selected-owner directory

Add one table in `sec:final-assembly` with the following columns:

- current selected owner or state;
- entry or production theorem;
- obstruction actually owned by that selected datum;
- existing closing theorem or valid reduction;
- dependency status;
- later consumer only.

The table must use the following routes.

| Current selected owner or state | Entry or production theorem | Owned obstruction | Existing closure or reduction | Dependency status and later consumer |
|---|---|---|---|---|
| arbitrary incoming candidate \(V\) carrying the fixed setup ledger, under the conditional antecedent \(V\in\calR_{\rm setup}(\calS)\) | `prop:setup-residual-handoff-complete` | retained local velocity concentration supplied by the fixed extraction | affine routing or entry of its canonical representative into the refined decomposition | the handoff is used contrapositively only after the refined rows are closed |
| current profile selected into \(\Cax\) | `def:refined-decomposition`, instantiated to the current canonical representative | the retained obstruction already recorded for this profile | `thm:R1-exclusion` | proved independently; consumed by refined closure |
| current profile selected into \(\Crot\) | `prop:R2-reduction-to-terminal` | retained velocity only on the selected realized terminal sequence, through its cited ancestry and heredity interfaces | `thm:terminal-stratification`, then `cor:R2-closure` | sequence-\(L^3\) is produced inside the terminal route, never assumed at R2 entry |
| current profile selected into \(\Cstat\) | `prop:R3-stationary-hull-reduction` and `prop:R3S-R3-terminal-reduction` | retained velocity only on the selected realized terminal sequence | `thm:terminal-stratification`, then `cor:R3-closure` | the stationary sequence-\(L^3\) subcase is a terminal output, not an entry hypothesis |
| current affine/parasitic representative | `thm:affine-normalization-dichotomy` | its selected non-affine oscillation, if retained | `thm:oscillatory-entry-normalization` | quotient routing; no retained normalized representative remains in this row |
| current realized coherent critical tail | `cor:coherent-critical-tail-extraction` and `thm:bounded-origin-realization-coherent-tails` | its selected annular non-affine activity and realized bounded-origin interface | `cor:coherent-critical-tail-branch-closure` | proved before hidden-scale and log-diffuse closure |
| current realized Young or pressure/viscous defect alternative | `thm:no-hidden-scale-variance-realized-defects` for the selected tight annular blow-down and `lem:critical-tail-defect-coordinate-closure` for its chartwise defect coordinates | the Young variance or named defect coordinate produced for that selected datum | `cor:young-branch-exclusion` | consumed by complete critical-tail closure |
| current realized log-diffuse defect and selected normalized log windows | `lem:log-window-support-transfer` and `lem:renormalized-log-window-heredity` | positive normalized window mass and a support point only when the cited theorem produces them | `cor:log-diffuse-branch-exclusion` | uses hidden-scale exclusion and the already closed coherent row |
| current realized critical-tail profile | `thm:realized-critical-tail-rigidity`, instantiated to that profile | only the selected tail obstruction recorded by its producer | `cor:critical-tail-exclusion-complete` | consumed by terminal and generic routing |
| current generic terminal profile and its selected terminal extraction | `thm:generic-terminal-exhaustion` | retained velocity transported along the named realization chain; sequence-\(L^3\) and mildness only at the selected indecomposable endpoint | the named terminal branch closures in the proof of `thm:R4-final-closure` | consumed by refined closure; `thm:terminal-stratification` is not added as an entry premise of this row |
| refined decomposition of the current canonical representative | the ordered refined routing theorem and all preceding row closures | no new obstruction is assigned at assembly | `thm:refined-residual-closure` | consumed by the exact raw-residual handoff |
| the same arbitrary incoming candidate \(V\), under the conditional antecedent \(V\in\calR_{\rm setup}(\calS)\) | `prop:setup-residual-handoff-complete`, used contrapositively after affine and refined closure | the original fixed-ledger retained obstruction | `thm:typeI-residual-closure` proves \(V\in\calR_{\rm setup}(\calS)\Rightarrow\bot\) | produces `cor:setup-residual-hypothesis-proof` |
| proved setup residual statement | `cor:setup-residual-hypothesis-proof` | no new analytic input | literal setup raw-residual closure | `cor:two-paper-local-typeI-exclusion` and the setup final assembly only |

The obstruction column is not a uniform inheritance column.  Root velocity
concentration belongs to the fixed extraction.  A descendant receives retained
velocity only through its cited realization and heredity interfaces.  A defect
window receives normalized mass and a support point only through its named
normalization and support-transfer theorems.  A terminal profile receives
sequence-\(L^3\) and finite-shift mildness only through the I7 producers.
Pressure remains attached to the local chart used in the corresponding row.

#### Required prose corrections

Make only the following ownership corrections in the final-assembly prose.

1. Replace

   > “The positive local velocity concentration inherited by every normalized
   > Seregin limit ...”

   by

   > “The normalized profile selected from the fixed extraction carries
   > retained local velocity concentration.  A descendant row uses this
   > obstruction only after the cited realization and heredity interfaces
   > transport it to that descendant.”

2. Replace the opening

   > “Assume, for contradiction, that a retained admissible residual profile
   > exists.”

   by

   > “Fix an arbitrary centered profile \(V\) carrying the fixed setup ancestry
   > ledger.  To prove
   > \(\calR^\#(\calS;I,J)=\varnothing\), it suffices to
   > prove
   > \(V\in\calR^\#(\calS;I,J)\Rightarrow\bot\).
   > Assume the antecedent.”

   Continue with the existing refined-routing proof.  After that row is proved
   empty, `thm:typeI-residual-closure` separately fixes an arbitrary incoming
   profile \(V\) with the same ledger and proves
   \(V\in\calR_{\rm setup}(\calS)\Rightarrow\bot\) by applying
   `prop:setup-residual-handoff-complete` contrapositively.  This keeps the
   refined closure and raw handoff as their existing two proof stages.  In each
   stage membership is only the antecedent being disproved; no existence
   premise is introduced.

3. Wherever the final proof says that a previously classified class is empty,
   use the conditional formulation:

   > “If the current profile is selected into that previously classified lower
   > state, the corresponding closure theorem excludes that profile.”

These replacements alter exposition only.  The displayed class list, theorem
statements, proof steps, and closure dependencies remain unchanged.

#### Architecture synchronization

Synchronize only the Type I rows and nodes in
`overall_proof_architecture.tex`.  In particular:

- replace “every residual descendant preserves ancestry and retained mass” by
  “each descendant used in the proof is first realized through the named
  ancestry interface; retained velocity is recorded only when the cited
  heredity theorem supplies it”;
- give the R2 node the reduction, selected terminal consumer, and
  `cor:R2-closure` labels;
- give the R3 node its two reduction labels, selected terminal consumer, and
  `cor:R3-closure` label;
- give the coherent, Young, and log-diffuse nodes their actual closure labels;
- give the endpoint node `lem:atomic-sequence-L3`,
  `thm:mildness-inheritance-main`, and `lem:no-atomic-active`, with
  `thm:AB-main` only as the endpoint input consumed there;
- place `thm:typeI-residual-closure`,
  `cor:setup-residual-hypothesis-proof`, and
  `cor:two-paper-local-typeI-exclusion` in that downstream order.

The architecture file is a label-and-route view.  It introduces no additional
profile, closure theorem, or hypothesis.

#### Structural checker

Create a Type I static audit script analogous in purpose to
`check_type_II_regularity.py`.  The script should check only stable structural
facts, including:

- required public labels exist exactly once;
- all local `\Cref` targets exist;
- the R2/R3 reduction labels precede their closure corollaries;
- the terminal dependency table contains the protected acyclic rows;
- the pressure-atlas, retained-descendant, selected-defect-window,
  support-transfer, and endpoint
  interfaces remain named;
- former fourth-paper terminology and the former residual-branch filename are
  absent;
- the rejected nested-set formulation is absent from the manuscript and audit
  documents;
- every final class in the refined decomposition appears in the final assembly.

The checker may compare source offsets to verify declaration order; it must not
encode incidental line numbers or prose punctuation.  It must not infer
ancestry, retained mass, suitability, mildness, pressure compatibility, defect
support, or theorem hypotheses from class membership.  Those facts remain
certified only by the named mathematical producers.  The checker creates no
premise used by the manuscript and is never cited as a proof step.

### Mathematics preserved

- The final theorem remains a consequence of the existing local closures.
- The setup paper's local assembly remains the final downstream consumer, with
  the residual closure supplied as a proved companion theorem rather than an
  added assumption.
- The fixed raw hull, fixed incoming profile, and single ancestry ledger remain
  unchanged.
- Residual emptiness is proved by fixing an arbitrary profile with the existing
  ledger and proving that membership in the relevant residual row implies a
  contradiction.  The exact handoff is then applied contrapositively.
- Mildness, retained descendant concentration, pressure representatives,
  normalized support points, and endpoint sequence-\(L^3\) remain attached to
  their named selected owners and producers.
- R2 and R3 consume terminal outputs; they acquire no new entry assumptions.
- Every proof block, appendix, theorem statement, and supporting lemma remains
  in place.

### Acceptance checks

- Every final-assembly row begins with the current selected profile, sequence,
  defect window, family, or terminal extraction which owns the recorded facts.
- No final-assembly row assigns retained velocity to a descendant without the
  named realization and heredity interfaces.
- No final-assembly row transports a pressure representative beyond its local
  chart.
- Mildness and sequence-\(L^3\) occur only in the selected terminal endpoint
  row after their I7 producers.
- The R2 and R3 rows contain no sequence-\(L^3\) entry hypothesis.
- The R2/R3 terminal consumer and the generic closure are sibling producers;
  `thm:refined-residual-closure`, `thm:typeI-residual-closure`,
  `cor:setup-residual-hypothesis-proof`, and the setup final assembly then occur
  in downstream order.
- The dependency directories and the final proof have the same theorem order.
- The capsule register in `overall_proof_architecture.tex` resolves to labels
  present in the manuscript.
- The structural checker verifies source consistency only and is not a premise
  of any theorem.
- The static checker and both TeX builds pass after the synchronization edits.
- The implementation adds no profile class, state space, hypothesis, theorem,
  proof step, or appendix deletion.

---

# Part IV. Recommended implementation order

## Stage 1. Freeze the public interfaces

1. Complete the setup export/provenance table.
2. Complete the coordinate, threshold, gauge, and pressure directories.
3. Record the retained-descendant and normalized-support-profile distinction.

## Stage 2. Synchronize the state map

4. Align the entry, coarse, refined, terminal, and final-assembly views.
5. Mark classification-only edges separately from theorem dependencies.
6. Add the compact capsule route table.

## Stage 3. Expose the local reductions

7. Add the R1 direct-closure interface.
8. Add the R2 and R3 reduction/deferred-closure interfaces.
9. Audit affine normalization, observer covariance, and pressure compatibility
   at their actual local consumers.

## Stage 4. Expose terminal residual promotion

10. Add the paired concentration/remainder output table.
11. Add the diffuse, critical-tail, and hidden-scale dependency view.
12. Add the separated-profile, recurrence, indecomposability, and endpoint
    input-production table.

## Stage 5. Consolidate and verify

13. Synchronize the final assembly and the overall proof architecture.
14. Add the Type I structural checker.
15. Rebuild the paper and inspect references, warnings, and layout.

This order follows theorem dependencies.  It is not a claim that the proof is a
linear sequence of nested residual sets; every step belongs to the fixed
singular-profile ledger.

---

# Part V. Mechanical audit

## Labels and imports

- [ ] Every label cited from the setup paper appears in the import dictionary.
- [ ] Every import row records the exact output consumed in Paper II.
- [ ] Every local theorem and corollary label resolves exactly once.
- [ ] No former fourth-paper terminology remains.

## State and obstruction interfaces

- [ ] Every theorem, estimate, compactness passage, and endpoint input names
      its local owner: the fixed incoming profile, a realized descendant, a
      normalized measure on a selected defect window, a support point already
      produced by a named theorem, or a finite-shift terminal pullback.
- [ ] A formula written on a centered, physical, hull, blow-down, or terminal
      coordinate domain is recorded as a property of that current profile and
      is never promoted to an assumption on the incoming physical solution or
      on unrelated profiles in the setup hull.
- [ ] Every structural property is identified either as a state-selection
      criterion already verified for the current profile or as an output of a
      named local producer.
- [ ] Every conditional lower-state criterion, including the R2 and R3
      integrable subcases, is used only after it has been verified for the
      selected profile.
- [ ] Every auxiliary profile or selected defect datum records each connection
      to the incoming branch that has been proved for it: realized ancestry,
      inherited velocity retention, positive defect mass, and the
      corresponding heredity or support-transfer theorem.
- [ ] A profile with proved realization and velocity retention keeps that
      interface when the same ledger also records normalized defect data.
- [ ] Normalized defect data with only positive mass are returned through the
      named support-transfer theorem; retained velocity concentration is not
      inferred from defect mass alone.
- [ ] When realized retained mass, positive defect mass, and a produced support
      point are available for the same datum, the proved interfaces remain
      recorded in the same ledger and may carry the terminal contradiction
      backward.
- [ ] Retained velocity mass and positive defect mass are never conflated as
      quantities; both are recorded when the named local producers establish
      them for the same realized datum.
- [ ] Every terminal contradiction identifies the obstruction it uses and the
      matching return interface: descendant heredity for retained velocity
      mass, support transfer for a produced support point, or both when both
      obstructions participate.

## Domains, topology, and pressure

- [ ] Every local estimate states its working and core regions.
- [ ] Every compactness theorem states its topology.
- [ ] Every pressure passage states the representative and gauge freedom.
- [ ] Every pressure-atlas failure has a named route.
- [ ] Every minimal-scale energy limit uses the actual pressure representative
      justified for that blow-down.

## Dependency direction

- [ ] R1 closes without terminal assembly.
- [ ] R2 and R3 reduce before terminal assembly and close after it.
- [ ] Coherent critical tails close before they are used in log-diffuse closure.
- [ ] Minimal mesoscopic reduction precedes hidden-scale, Young, and
      log-diffuse conclusions.
- [ ] Atomic sequence-\(L^3\) precedes endpoint Liouville.
- [ ] Finite separated-family and infinite-chain exclusions precede terminal
      assembly.
- [ ] Final assembly cites only imported or previously proved results.

## Build checks

After manuscript implementation:

1. run the Type I structural checker;
2. compile `type_I_residual_closure.tex` to stable references;
3. search the log for undefined references, multiply defined labels, and
   missing citations;
4. inspect overfull boxes introduced by new tables or captions;
5. verify `overall_proof_architecture.tex` still resolves all Type I labels;
6. run `git diff --check` on the edited files.

---

# Part VI. Referee-facing checklist

A reader should be able to answer yes to each question.

## Entry and ancestry

- [ ] Is the normalized raw Seregin profile imported from the setup paper with
      an exact output tuple and fixed ledger?
- [ ] Is residual membership invoked only after the direct setup classes have
      been closed for that profile?
- [ ] Is its positive local velocity obstruction fixed before residual routing?
- [ ] Does every later profile record every applicable proved connection to the
      incoming branch---realization, retained-mass heredity, support transfer,
      or both interfaces together?

## Local capsules

- [ ] Does every datum have a named local owner in the fixed
      singular-profile ledger?
- [ ] Is each structural criterion used only to select the state of the
      current profile?
- [ ] Does every structural theorem state the local hypotheses it consumes?
- [ ] Does every theorem close only its declared component?
- [ ] Does failure of a local hypothesis produce a named adjacent state?
- [ ] Are pressure and coordinate conventions explicit at every limit?

## Terminal graph

- [ ] Are compact active and diffuse residual outputs extracted as a paired
      decomposition?
- [ ] Are affine, pressure, noncompact, Young, log-diffuse, and coherent-tail
      exits all routed?
- [ ] Are finite separated families and infinite descendant chains closed
      independently of terminal assembly?
- [ ] Is sequence-\(L^3\) produced only at the terminal indecomposable state?

## Assembly

- [ ] Does the terminal theorem assemble only earlier local results?
- [ ] Do the R2 and R3 closure corollaries use their reductions plus the now
      established terminal theorem?
- [ ] Does the generic closure exhaust every remaining terminal route?
- [ ] Does the residual theorem prove exactly the literal raw-residual closure
      statement imported by the setup paper as a companion theorem?

---

# Part VII. Intended final reading

After these edits, the paper should read as the following cohesive argument:

\[
\text{candidate local pointwise Type I singularity}
\longrightarrow
\text{admissible Seregin extraction}
\longrightarrow
\text{one normalized raw profile }V_0\text{ with one fixed ledger},
\]

\[
V_0\in
\left(
\text{direct setup classes}
\right)
\cup
\calR_{\rm setup}(\calS).
\]

Every direct setup class closes locally.  For an arbitrary incoming \(V\) with
this same ledger, prove
\[
   V\in\calR_{\rm setup}(\calS)\Longrightarrow\bot .
\]
Assume only the antecedent.  The exact handoff then gives

\[
V
\longrightarrow
\begin{cases}
\text{the affine/parasitic route, which is already closed},\\
\text{a retained canonical representative in }
\calR^\#(\calS;I_{\rm setup},J_{\rm res}).
\end{cases}
\]

The retained alternative is improved through realized local descendants and
selected defect-window data, with each proved interface retained on the datum
for which it was established:

\[
\longrightarrow
\text{paired active/residual terminal decomposition}
\longrightarrow
\text{affine, diffuse, pressure, tail, separated, chain, or atomic state},
\]

\[
\longrightarrow
\text{local closure of the state selected for the current profile},
\]

\[
\longrightarrow
\text{backward contradiction through every applicable heredity and/or
support-transfer interface},
\]

\[
\longrightarrow
\calR^\#(\calS;I_{\rm setup},J_{\rm res})=\varnothing.
\]

Together with the closed affine route and the exhaustive handoff, this gives

\[
\longrightarrow
\calR_{\rm setup}(\calS)
=
\calR\bigl(
\calS_{\mathrm{raw\text{-}gen}}(u,p,z_*;R_0,\eta_*)
\bigr)
=\varnothing,
\]

and therefore

\[
\text{the candidate singular profile }V_0\text{ cannot exist}
\longrightarrow
\text{the setup paper's unconditional local Type I exclusion}.
\]

The proof remains the same proof.  The completed edits make its fixed-profile
refinement, routing interfaces, pressure atlas, obstruction
transport, and final assembly visible at the points where a reader needs them.
