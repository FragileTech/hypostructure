# Type I Residual Closure: Interface and Exposition Blueprint

## Purpose

This document specifies presentation and interface edits for
`to_formalize/type_I_residual_closure.tex`.  The proof is mathematically
airtight.  The edits preserve its theorem statements, hypotheses, conclusions,
local estimates, dependency order, and contradiction strategy.

The objective is to make the existing proof easy to audit as one local
state-space argument.  A reader should be able to identify, at every stage,

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

Throughout this blueprint, **local** means attached to the fixed hypothetical
singular point and to the singularity-generated profile currently carried by
its ancestry ledger.  Coordinate domains such as \(\mathbb R^3\), ancient-time
intervals, centered hulls, and expanding terminal regions describe the chart
in which that current profile is analyzed.  Their analytic role is confined to
that profile and its fixed ledger.  Each norm,
compactness statement, pressure representative, symmetry criterion, and
Liouville input must therefore be recorded with its local owner: the incoming
profile, a realized descendant, a normalized defect-support profile, or a
finite-shift pullback of the terminal profile.

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

The ledger is consequently a state-space routing ledger for the fixed
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

Recenterings, time translates, hull limits, blow-downs, normalized support
profiles, and terminal profiles may change:

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
concentration bound.  A normalized support profile obtained from a defect
measure carries positive defect support and the associated support-transfer
interface.  It carries inherited positive velocity concentration as well when
local realization and retention theorems prove that additional fact.  The two
interfaces are logically independent and may coexist in the same profile
ledger.

Every diagram, table, and local lemma must identify which of these two
interfaces it exports.  Positive defect support alone does not imply inherited
positive velocity concentration, and retained velocity concentration alone
does not supply defect support.  When both are proved, both remain available
for downstream routing and backward contradiction; construction as a support
profile never discards a stronger realized-descendant or retained-mass
interface.

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
residual-closure theorem into the setup paper's local assembly.  This is an
unconditional contrapositive for the fixed hypothetical singular profile and
its ledger.  Every route consumes properties produced for that profile, and
residual membership is considered only as the hypothetical alternative to be
closed.

---

# Part II. Canonical capsule map

The following map is the backbone of the edited exposition.  It is adapted from
the Type I capsule register in `overall_proof_architecture.tex` and must be
checked against the current theorem bodies before manuscript edits are made.

| Capsule | Mathematical role | Principal source labels | Output or closure |
|---|---|---|---|
| R0 | Fix the normalized raw Seregin profile produced from the hypothetical singular point; enter the residual branch only after the direct setup classes close | `thm:imported-setup-results`, `hyp:base-seregin-hypotheses`, `hyp:previous-nonresidual` | Fixed setup profile with retained compact velocity concentration, pressure compatibility, normalization data, and ancestry |
| R0b | Realize descendants and transfer support | `def:sequence-realized-residual-object`, `def:retained-vs-support-profile-descendant`, `thm:ancestor-realization-inheritance`, `thm:descendant-heredity` | Proof-relevant descendants remain connected to the original branch |
| R1 | Close the axisymmetric bounded-circulation state selected for the current profile | `thm:R1-exclusion` | The centered circulation equation and axis absorption place that profile in the previously closed no-swirl state |
| R2 | Reduce the rotational state selected for the current profile through compact annular Coriolis-flux windows | `prop:R2-reduction-to-terminal`, `cor:R2-closure` | Previously closed local state or realized terminal concentration profile; deferred closure after terminal assembly |
| R3 | Reduce a retained stationary-hull occurrence of the current profile by scale reselection | `prop:R3-stationary-hull-reduction`, `prop:R3S-R3-terminal-reduction`, `cor:R3-closure` | Previously closed local state or realized stationary terminal profile with the inherited ledger; deferred closure after terminal assembly |
| R4 | Covariant observer and affine/parasitic quotient | `thm:covariant-observer-calculus`, `thm:affine-normalization-dichotomy`, `thm:oscillatory-entry-normalization` | Affine mode routed to the lower quotient stratum or positive non-affine activity retained |
| R5a | Recurrent tail-core rigidity | `thm:recurrent-tail-core-rigidity` | Recurrent tail core closed or routed into the terminal alternatives |
| R5b | Log-diffuse critical tail | `thm:log-diffuse-from-hidden-scale`, `cor:log-diffuse-branch-exclusion` | Log-window support profile routed through hidden-scale and coherent-tail closure |
| R5c | Young/variance critical-tail defect | `thm:first-bad-mesoscopic-reduction`, `thm:no-hidden-scale-variance-realized-defects`, `cor:young-branch-exclusion` | Variance defect eliminated by minimal mesoscopic reduction |
| R5d | Coherent homogeneous, log-periodic, or aperiodic tail | `thm:bounded-origin-realization-coherent-tails`, `cor:coherent-critical-tail-branch-closure` | Coherent tail excluded by bounded-origin realization and log-hull rigidity |
| R6a | Paired terminal concentration extraction | `thm:terminal-exhaustion-main` | Compact active profiles plus the residual measure on expanding terminal regions |
| R6b | Inactive and nonconcentrating terminal alternatives | `thm:terminal-inactive-exclusion` | Pure local vanishing and pure exterior escape cannot carry the retained obstruction |
| R6c | Diffuse and mixed compact--diffuse alternatives | `thm:diffuse-defect-compactness`, `thm:diffuse-defect-trichotomy`, `thm:no-mixed-compact-diffuse` | Active, affine, or critical-tail route; mixed remainder excluded |
| R6d | Separated profiles and descendant chains | `thm:active-path-space-recurrence`, `thm:compact-active-descendant`, `thm:no-finite-separated-profile-family` | Infinite chains and finite separated families excluded |
| R7 | Terminal indecomposable endpoint for the realized profile | `lem:atomic-sequence-L3`, `thm:mildness-inheritance-main`, `thm:AB-main`, `thm:R4-final-closure` | Terminally produced sequence-\(L^3\), finite-shift mild pullback, and contradiction with that profile's retained local obstruction |
| Assembly | Fix the setup ledger and a hypothetical incoming \(V\) in its raw residual alternative; close the affine or retained route selected for this \(V\) | `prop:setup-residual-handoff-complete`, `thm:terminal-stratification`, `thm:typeI-residual-closure`, `cor:setup-residual-hypothesis-proof` | The selected \(V\) is impossible; the same pointwise contrapositive establishes raw-residual closure for the fixed ledger |

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
profile.  Fixing a hypothetical incoming residual profile with this ledger,
Paper II closes the affine routing row or the retained residual row selected by
the local routing.  This pointwise contradiction proves the raw-residual
closure for the same fixed ledger.

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

### Source anchors

- `def:terminal-measures`
- `lem:gauge-compatibility`
- `lem:no-pressure-only-retained-profile`
- `lem:first-generation-local-window-compactness`
- `lem:ancient-profile-covariant-compactness`
- `lem:retained-recentering-alternatives`
- `thm:terminal-exhaustion-main`
- `thm:terminal-inactive-exclusion`

### Existing route

The terminal protocol extracts active concentration profiles and, on the same
expanding regions, retains the residual measure left after their neighborhoods
are removed.  The two outputs are paired parts of one local decomposition.

### Expository edit

Add a terminal-output table listing:

| Output | Retention mechanism | Topology/representative | Next route |
|---|---|---|---|
| compact active descendant | positive unit velocity concentration | local Seregin/covariant compactness | descendant, separated-family, chain, or atomic analysis |
| diffuse residual measure | positive normalized defect support | observer compactification and support transfer | diffuse trichotomy |
| pressure/noncompact alternative | failure of the required local atlas or compactness | named local failure state | pressure, affine, diffuse, or critical-tail route |
| critical-tail window | positive critical tail observable | log-annular or Young compactification | R5b--R5d |
| inactive/radiative alternative | local vanishing or sole exterior escape | local exclusion theorem | direct closure as sole carrier |

The table must state that concentration-set removal and residual-measure
formation occur on the same selected terminal regions.

### Mathematics preserved

- Pure radiative alternatives are used only as sole-source exclusions.
- Coexistence is handled by the mixed compact--diffuse theorem.
- Pressure-only activity never substitutes for retained velocity concentration.

### Acceptance checks

- Every output of `thm:terminal-exhaustion-main` has a named downstream route.
- Compact and diffuse outputs are not formed from unrelated subsequences or
  regions without a diagonal realization statement.
- Every nonzero defect state has the support-transfer statement required for
  backward contradiction.

## I6. Display the true critical-tail dependency order

### Source anchors

- `thm:diffuse-defect-compactness`
- `thm:diffuse-defect-compactification-construction`
- `thm:diffuse-defect-trichotomy`
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
variance exclusion.  The log-diffuse branch uses log-window support profiles,
hidden-scale exclusion, and the already closed coherent alternatives.

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

For every blow-down or compactification theorem, record separately whether its
descendant has realized ancestry with retained velocity concentration and
whether it has positive normalized defect support.  State every applicable
heredity or support-transfer theorem; if both interfaces are proved, retain
both in the same singular-profile ledger.  Each compactification is thereby a
local route for the current realized profile, rather than a statement about an
ambient class of unrelated solutions.

### Mathematics preserved

- Coherent-tail closure does not depend on the later log-diffuse conclusion.
- The Young and log-diffuse rows share the minimal mesoscopic mechanism without
  being identified as the same state.
- The variance Liouville theorem is used only after the local blow-down and
  pressure interfaces have produced its hypotheses.

### Acceptance checks

- The dependency diagram agrees with `tab:typeI-dependency-order`.
- No theorem cites a closure that is downstream from itself.
- Every pressure, viscous, affine, and Young defect coordinate has an explicit
  route or closure.

## I7. Expose how the endpoint hypotheses are manufactured

### Source anchors

- `def:finite-separated-profile-family`
- `def:atomic-terminal-profile`
- `prop:no-multi-implies-atomic`
- `lem:atomic-sequence-L3`
- `thm:descendant-heredity`
- `thm:active-path-space-recurrence`
- `thm:compact-active-descendant`
- `thm:no-finite-separated-profile-family`
- `thm:mildness-inheritance-main`
- `thm:AB-main`
- `lem:no-atomic-active`

### Existing route

A retained compact descendant is iterated within the realized normalized
profile class.  It produces a finite separated family, an infinite descendant
chain, a diffuse/noncompact/tail exit, or a single terminally indecomposable
profile.  Only the last state receives the backward sequence-\(L^3\) estimate
and parasitic-free mild pullback required by the endpoint theorem.

### Expository edit

Add an endpoint input-production table:

| Endpoint hypothesis | Producing result | Earlier alternatives whose absence is used |
|---|---|---|
| terminal indecomposability | `prop:no-multi-implies-atomic` | finite separated, chain, diffuse, noncompact, and tail outputs |
| backward sequence-\(L^3\) for the terminal profile | `lem:atomic-sequence-L3` | retained descendants and all residual escape routes removed for that profile |
| bounded mild physical pullback of the terminal profile | `thm:mildness-inheritance-main` | affine/parasitic quotient removed and finite shift fixed |
| nonzero obstruction | retained velocity concentration and ancestry | transported from the singularity-generated raw profile along the residual branch |
| zero conclusion | `thm:AB-main` | all preceding endpoint inputs |

The proof of the finite separated-family theorem must continue to use the
finite directed successor graph and the independent no-infinite-chain/no-atomic
closures, rather than terminal assembly itself.

### Mathematics preserved

- Sequence-\(L^3\) is proved at the terminal indecomposable state for the
  current realized profile and is used only there.
- The endpoint theorem is applied only to the parasitic-free bounded mild
  physical pullback of that profile after finite shift.
- The contradiction is with the retained local velocity obstruction.

### Acceptance checks

- The endpoint theorem is absent from all upstream compactness and
  classification lemmas except where the source already proves the atomic
  contradiction.
- The finite separated-family and infinite-chain exclusions do not use
  `thm:terminal-stratification`.
- The terminal dependency table remains acyclic.

## I8. Synchronize final assembly, auxiliary views, and static checks

### Source anchors

- `tab:typeI-dependency-order`
- `tab:terminal-dependency-table`
- `thm:terminal-stratification`
- `thm:R4-final-closure`
- `sec:final-assembly`
- `thm:typeI-residual-closure`
- `cor:setup-residual-hypothesis-proof`
- `cor:two-paper-local-typeI-exclusion`
- Type I capsules in `overall_proof_architecture.tex`

### Existing route

The terminal assembly closes every terminal output.  The deferred R2 and R3
corollaries then close their classes.  The generic terminal theorem closes
\(\Cgen\).  For the fixed incoming profile and its ledger, the final residual
theorem combines the ordered local class closures and proves the setup paper's
literal raw-residual theorem.

### Expository edit

Make the final assembly table-driven.  Each row should state:

- class or terminal state;
- entry theorem;
- retained obstruction;
- closing theorem or valid reduction;
- dependency status;
- final consumer.

Keep the prose proof as the mathematical assembly, but ensure the figure,
classification table, dependency tables, reader guide, final displayed chain,
and `overall_proof_architecture.tex` use the same labels and route descriptions.

Create a Type I static audit script analogous in purpose to
`check_type_II_regularity.py`.  The script should check only stable structural
facts, including:

- required public labels exist exactly once;
- all local `\Cref` targets exist;
- the R2/R3 reduction labels precede their closure corollaries;
- the terminal dependency table contains the protected acyclic rows;
- the pressure-atlas, retained-descendant, support-profile, and endpoint
  interfaces remain named;
- former fourth-paper terminology and the former residual-branch filename are
  absent;
- the rejected nested-set formulation is absent from the manuscript and audit
  documents;
- every final class in the refined decomposition appears in the final assembly.

The checker must avoid encoding incidental line numbers or prose punctuation.

### Mathematics preserved

- The final theorem remains a consequence of the existing local closures.
- The setup paper's local assembly remains the final external consumer, with
  the residual closure supplied as a proved companion theorem rather than an
  added assumption.
- Supporting appendices remain in place unless a line-by-line comparison proves
  that a block is redundant and all consumers are preserved.

### Acceptance checks

- No reachable terminal state lacks a named closure or reduction.
- The two dependency tables and the final proof have the same topological
  order.
- The capsule register in `overall_proof_architecture.tex` resolves to labels
  present in the manuscript.
- Static checks and the TeX build pass after the manuscript edits.

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
      normalized support profile, or a finite-shift terminal pullback.
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
- [ ] Every auxiliary profile records every connection to the incoming branch
      that is proved for it: realized ancestry, inherited velocity retention,
      positive defect support, and the corresponding heredity or
      support-transfer theorem.
- [ ] A profile with proved realization and velocity retention keeps that
      interface even when it is also constructed or used as a normalized
      defect-support profile.
- [ ] A profile with only positive defect support is returned through the named
      support-transfer theorem; retained velocity concentration is not inferred
      from defect support alone.
- [ ] When both realized retained mass and positive defect support are proved,
      both interfaces remain recorded in the same ledger and either or both may
      carry the terminal contradiction backward.
- [ ] Retained velocity mass and positive defect support are never conflated as
      quantities; their simultaneous presence on one profile is recorded
      rather than suppressed.
- [ ] Every terminal contradiction identifies the obstruction it uses and the
      matching return interface: descendant heredity for retained velocity
      mass, support transfer for defect support, or both when both obstructions
      participate.

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
\text{hypothetical local pointwise Type I singularity}
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

Every direct setup class closes locally.  In the remaining alternative, fix a
hypothetical
\(V\in\calR_{\rm setup}(\calS)\) with this same ledger.  The exact handoff gives

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
typed defect-support states, with every proved interface retained on each
auxiliary profile:

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
\text{the hypothetical profile }V_0\text{ cannot exist}
\longrightarrow
\text{the setup paper's unconditional local Type I exclusion}.
\]

The proof remains the same proof.  The completed edits make its local
state-space refinement, routing interfaces, pressure atlas, obstruction
transport, and final assembly visible at the points where a reader needs them.
