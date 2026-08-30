# Erdős–Gyárfás incomplete nodes and repair plan

## Purpose and sources of truth

This document records the current proof boundary after the latest Lean repairs.
It distinguishes completed nodes from genuine residual obligations and states the
smallest next lemmas that follow the manuscript's strategy.

The sources of truth are, in order:

1. the kernel-checked Lean implementation;
2. `to_formalize/erdos_64_proof.tex` and its proof-flow graph;
3. `Assembly_node_audit.md` when its rows agree with the implementation;
4. the node reports in `audits/erdos-64-red-team/reports/`.

A branch is closed only when its destination contract follows from the literal
incoming `ExactLedger`. Recording a complement is correct routing, but is not
itself a contradiction.

## Current boundary

The earlier plan is obsolete in treating `[19]`, `[171]`, `[175]`, `[176]`, and
`[177]` as unimplemented or incorrectly specified. Those repairs are present in
the live source. A fresh inspection of proposition bodies, Assembly call sites,
the audit tables, and the final result type still proves that the claim “only
`[172a]`, `[181]`, and `[182]` remain” is false. The current proof boundaries
are:

1. **Missing predecessor split at `[50]`–`[52]`** — the ExactLedger executor
   `independentObstructionTranslatesRow` now implements
   `lem:translates-independent`, but no live residual publishes its required
   `K .dominantRootedWedgeType`. The binary high/low entropy split therefore
   still omits the manuscript's repetitive-low versus nonrepetitive-low split,
   and the implemented `[51]` row is unreachable;
2. **Triangular continuation at `[79]`–`[81]` and `[85]` repaired** —
   `lem:triangular-shoulder-completion`, `lem:triangular-port-return`, the exact
   first-landing exhaustion, and cross-shoulder multiplicity are implemented
   and wired on the literal degree-four Type-B ledger. The four independently
   proved suppression facts are not Node `[85]` outputs: their ExactLedger
   producers now run on the sparse-surplus survivor before `[128]`.
   `sparsePortActivationRow` reads
   `lem:single-open-port-suppression-witness` through `inputs.get` instead of
   reproving its minimality argument. The canonical upstream
   `def:fan-closed-port` is now published once as `K .fanClosedPort` in the
   common `[72]` port-routing prefix and inherited by its surviving Node `[85]`
   continuations. `lem:compatible-pair-fan-closure` now reads that definition
   through `inputs.get` and invokes the canonical upstream theorem. The first
   quantitative routing proposition now reads the same definition key and
   invokes the canonical upstream theorem. The compatible-pair routing
   corollary then reads both preceding `[72]` keys through `inputs.get` and
   invokes its canonical upstream corollary.  Finally
   `triangularPortTypeBRoutingRow` reads `K .fanClosedPort` and
   `K .fanClosedPortTypeBRouting` through `inputs.get`, invokes the canonical
   upstream `triangularPortTypeBRouting`, and publishes the exact
   `(5k-19)/4` positive-deficit conclusion before the certificate split.
   `def:typeB-fan-safe` is instead published at the common Type-B entry, where
   the paper and the exit-(7) handoff first use that standing definition;
3. **Uncomposed implementation outputs** — `SelectedLedgerBoundaryResult`
   still returns sparse target-defect, raw/common Type-B accounting, route-8
   sublinear/quotient/rate, and absorbed-germ propositions instead of closing
   or routing them as the manuscript prescribes;
4. **`[172a]`** — on the nonadditive arm of `[170]`, construct the manuscript's
   cardinality-minimal connected barrier-overlap producer and route its actual
   uncrossing outcomes;
5. **`[181]`** — close or type-route the peeled target-defect demand residual
   from its retained stage-accounting and blocker facts;
6. **`[182]`** — prove the uncovered implications left by the exact decisions
   at `[178]`–`[180]`.

Nodes `[178]`–`[180]` are not gaps on their covered arms. Their exact negative
arms are deliberately retained at `[182]`.

The direct evidence is the codomain of `selectedLedgerBoundary`: it returns
several semantic propositions besides the three numbered residuals. None is
definitionally `False`, so successful elaboration does not close them.

## Correctness classification from the live code

### Implemented prefix and remaining gap: nodes `[79]`–`[81]`, `[85]`

The live `triangularFanCoreRow` still owns only the core and incidence
definitions. It is now followed on the same `ExactLedger` by two exact owners:

- `triangularShoulderCompletionRow` reads `K .highCentreNormalForm` and
  `K .triangularFanCore`, publishes all four clauses of
  `lem:triangular-shoulder-completion`, and appends only
  `K .triangularShoulderCompletion`;
- `triangularPortReturnRow` reads `K .bridgeless`, `K .selection`,
  `K .highCentreNormalForm`, and `K .triangularShoulderCompletion`. For each
  triangular port it constructs the simple return, records
  `Q = R.tail ⊆ G-x`, excludes the restored dyadic cycle length, and witnesses
  the manuscript's conditional noncentral shoulder-completion incidence. It
  appends only `K .triangularPortReturn`.

`selectedTypeBAfterNormalFormContinuation` runs these rows consecutively before
the existing certificate cap. Thus the old claim that Assembly jumps directly
from `triangularFanCoreRow` to `fanCertificateCapRow` is no longer true.

`triangularFirstLandingRow` now reads the core, shoulder-completion, and
port-return facts and publishes the mutually exclusive central,
cross-triangular, and outside classification, together with the two explicit
nonlanding conclusions. `triangularCrossShoulderRow` then implements the
shared-shoulder degree alternative and the disjoint-edge quadrilateral
argument. `openPortSuppressionRow` then publishes the paper's four
suppressibility conditions and literal delete-and-add graph.
`openPortSuppressionSafeRow` reads that exact definition fact, converts clause
(d) to `CenterCapacity`, and applies the proved centre-load degree identity to
every surviving vertex. `singleOpenPortSuppressionWitnessRow` then specializes
the upstream tight-vertex suppression theorem to the selected ExactLedger
object and publishes its simple shoulder path avoiding the deleted port. The
`suppressedFamilyCriticalCycleRow` now supplies the nonempty-family baseline
and minimality step, and publishes both the nonempty used-chord cycle and the
universal simple expansion with forbidden lifted length. The standing
`def:typeB-fan-safe` is published at the common Type-B producer, while the
canonical `def:fan-closed-port` interface is published by the common `[72]`
prefix. Its surviving Node `[85]` continuations inherit both. The exact
`prop:triangular-port-typeB-routing` producer now reads that definition and the
fan-closed routing theorem through `inputs.get`, publishes the stronger
triangular deficit bound, and feeds the existing certificate/B1/B2 continuation.

### Manuscript and implementation agreement at `[153]`

`coldFirstFailureRoutingRow` reads all F1–F4 exclusion/handoff facts, and
`coldGermCandidatesRow` proves the exact candidate/complement and loss
inequalities. The manuscript now defines the same family as Lean: the 11
one-stub interior incidences of an ambient-cubic window, with the first two
dropped as absorbed corridor incidences. Thus `[152]` supplies `9C-o(n)` and
`lem:cold-germ-extraction` supplies `9C/D_cold-o(n)`. The diagram, proof,
dependency ledger, and quantitative closure all use this family.

### Implemented but unreachable: `lem:translates-independent`

`independentObstructionTranslatesRow` is the live ExactLedger owner for the
manuscript lemma. It reads `K .curvatureFullRank` and
`K .dominantRootedWedgeType`, constructs the maximal separated translate family
on the current object, and publishes `K .independentObstructionTranslates`.

The remaining defect is upstream and topological: the current entropy
dichotomy publishes only high entropy or undifferentiated low entropy. It does
not separate the repetitive-low arm carrying the dominant rooted type and
internal root wedge from the nonrepetitive-low arm. Consequently no live
Assembly caller can satisfy the row's exact manifest. Node `[51]` is therefore
implemented but unreachable, while node `[52]` remains incomplete.

The present full `SpineRows` build also reports a later elaboration mismatch in
this executor's subcubic-ball bound: the local hypothesis is phrased through
`FiniteObject.degree`, while `SubcubicReach.card_reach_le` expects the graph
degree expression. This is an implementation-level type mismatch in the live
checkout, not permission to replace the manuscript lemma or alter its strategy.

### Unclosed outputs visible at the root

The final Assembly result still exposes:

- `sparseTargetDefectResidual` from `[125]`;
- a raw `typeBFanEntry` on early Type-B routes;
- `fanCertificateResidualMass`, `typeBExcluded`,
  `typeBExclusionResidualMass`, and `typeBOverlapObstructionMass`;
- `typeBSublinearResidual`, `route8QuotientResidual`, and `route8RateFails`;
- the absorbed-germ extracted-Type-B output and `coldBranchClosed` fact.

Each must be proved contradictory or routed to the exact destination prescribed
by the manuscript. Merely naming it a boundary or returning it in a disjunction
does not close the proof.

## Repairs completed since the previous plan

### Node `[19]`: routing-alphabet coefficient

The surplus threshold now uses `spineData.routingLabelBound`, the certified
cardinality bound for the complete seven-coordinate routing alphabet.
`homogeneousTokenCap` receives that same quantity and forms the manuscript's
augmented alphabet internally. The baseline degree remains only in the two
boundary-profile cardinal factors; it is no longer substituted for `Q_geom`.

### Node `[85]`: triangular prefix and corrected producer ownership

The common degree-four Type-B continuation now publishes, in manuscript order,
`K .triangularShoulderCompletion`, `K .triangularPortReturn`, and
`K .triangularFirstLanding`, and `K .triangularCrossShoulder` through canonical
`factOnly` rows.  The four suppression labels are not introduced at `[85]`:
their rows run on the sparse-surplus producer before `[128]`, and the activation
consumer reads `K .singleOpenPortSuppressionWitness` with `inputs.get`.
Likewise `K .typeBFanSafe` is published once at the common Type-B entry
`[65]`/`[108]`, before the degree split; it is not re-proved at `[85]`.  All
these proofs are anonymous executor bodies over the literal `FactInputs`; no
detached theorem, callback, alternate carrier, or second ledger was introduced.
The common `[72]` prefix then publishes the fan-closed definition and routing
facts exactly once.  `triangularPortTypeBRoutingRow` consumes those registered
facts with `inputs.get` and appends `K .triangularPortTypeBRouting` between
cross-shoulder completion and the fan-certificate cap.  Thus the triangular
local route into the existing B1/B2/exclusion ledger is complete; the later
bridge-mass and sublinear owners remain at `[84]`/`[85]` and are not re-proved
on this branch.

### Nodes `[160]`–`[161]`: exact route-8 rate routing

The deficiency branch now makes the separate route-8 rate decision required by
the later contradiction. Only the arm carrying both the deficiency cap and the
route-8 rate enters `[161]` and its `[25]` continuation. The literal failed-rate
arm remains on the hot/cold or peeled-residual route. Thus no use of
`τ < 1/4` is substituted for the stronger `τ < 3/13` contract.

### Node `[157]`: graph representatives versus neutral symmetry

The equal-length table route now distinguishes an actual smaller graph
representative from a merely symmetric neutral configuration. Replacement is
used only with the complete proper-representative witness. The neutral arm
retains its row and proceeds through the canonical-piece/second-strand route.

### Nodes `[165]`–`[166]`: refined minimality and canonical replacement

The canonical arm now carries the refined minimality and replacement facts
needed to prove the universal equality `Q = E` for the exact quantified neutral
configuration. The equality is published in the same `ExactLedger` and remains
available to `[169]` and the downstream blocked-class construction. It is not a
detached selected-fact theorem or an unregistered global premise.

### Node `[168]`: actual interior-stub exclusion

The implementation selects and retains actual interior occurrences, uses the
correct `9C` extraction after transit incidences are paid, and proves the
endpoint/interior incompatibility for the same selected occurrence. The old
invalid inference from thirteen arbitrary external stubs is no longer used.

### Nodes `[169]`–`[171]`: blocked-class compression

Node `[171]` is implemented according to the paper:

- `blockedCompressionRow` in
  `hypostructure/Hypostructure/Graph/Strategy/BlockedCompressionRows.lean`
  reads `blockedClassMember` and `blockedScaleAdditive` exclusively through
  `inputs.get`;
- its sealed executor performs the canonical scale/window/barrier exposure,
  conditional-fibre multiplication, injective graph coding, and registered
  `(F/W)` product-rate conversion;
- it publishes `blockedCompressionBound` and `blockedCompressionCap` through
  the canonical `ExactLedger`;
- `blockedCompressionCloses` closes the cap against the inherited
  `densePackingOverflow` with `runAndCloseIncompatible`;
- `selectedCanonicalReplacementContinuation` matches the live `[170]`
  decision: the additive arm runs `[171]`, while the nonadditive arm is retained
  as the `[172a]` boundary.

There is no explicit saving premise, callback, detached theorem, alternative
carrier, or custom application wiring. Validation included
`lake build Hypostructure.Graph.Strategy.BlockedCompressionRows`, the canonical
`ExactLedger` fixtures, the API-catalog check, and the relevant audit sync.

### Nodes `[173]`–`[174]`: exact collision residual

The live proof no longer relies on the previous plan's proposed ad hoc
`C = 0` cold-occurrence selection. Node `[173]` decides the exact collision
predicate. Its failure arm runs `[174]`, which publishes the cleared absorbed
configuration inequality from `exactCollisionFails`, `boundaryDemand`, and
`coldWindowLedgerSplit`. The literal residual then enters the registered
cold-corridor prerequisite chain and `[175]`.

### Nodes `[175]`–`[177]`: lossless absorbed-family routing

The relevant former failures are fixed.

- **`[175]` partitions without data loss.** For every eligible retained
  incidence, `absorbedGermSplitRow` proves either membership in the exact
  subcubic candidate image or the heavy-centre alternative. The decision asks
  whether the candidate class is inhabited; it does not discard the
  complementary incidences. Mixed families therefore retain both kinds of
  facts.
- **`[176]` executes the paper route.** The candidate arm runs the prescribed
  `[154]`–`[157]`, `[163]`, and `[165]`–`[168]` path. A genuine second strand
  closes by the two-cycle endpoint/interior argument. A canonical
  representative retains `[166]`'s equality and continues without erasing the
  heavy complement.
- **`[177]` constructs the actual Type B handoff.** It reads the aggregate
  complement from the canonical `ExactLedger`, constructs every prescribed fan
  envelope and literal `typeBFanEntry`, and enters `[65]` on the same monotone
  ledger. Both the mixed-family path and the empty-candidate path use this
  continuation. The seven downstream consumers now destructure the expanded
  envelope witness and project its explicit high-centre proof; none mistakes
  the germ equality field for that proof.

No detached facts, alternative carriers, hardcoded proof data, callbacks, or
custom routing state were introduced. The complete
`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean`
kernel-check succeeded (the integrated continuation begins around line 5313),
and the corresponding node-audit rows `[175]`–`[177]` beginning around
`Assembly_node_audit.md:557` were changed from unsupported failures to
evidence-backed successes.

### Node `[144]`: common Type B continuation

The same-token bottleneck route no longer stops after publishing
`typeBFanEntry`. Its three live callers preserve the exact `[144]` packing,
core, envelope, and handoff facts, then execute the same registered
`[68]`–`[85]` continuation used by the other Type B entries. The result is one
of the concrete existing accounting facts: certificate residual mass,
successful exclusion, exclusion residual mass, or overlap-obstruction mass.
The strict-surplus root exposes that concrete boundary and never feeds the
strict ledger into the near-cubic continuation.

### Removal of the false positive-germ closures

The two conditional `ExactLedger → False` callbacks have been removed.
Ordinary and absorbed positive-germ branches now run their concrete registered
nodes and return `coldBranchClosed` (`NoTerminalColdResidual`) on the arms where
the paper's `[154]`–`[157]` argument closes the residual.

Consequently:

- nodes `[163]`–`[172]` are reachable only from the manuscript's actual dense
  residual;
- node `[125]`'s accumulated sparse-surplus fact remains in the literal ledger
  throughout;
- there is no invented compatibility edge or back-loop;
- no fabricated conditional hypothesis is needed to close an ordinary or
  absorbed positive-germ branch.

The relevant validation covered `Assembly.lean`, `StrategyDag.lean`, canonical
`ExactLedger` fixtures, the node-`[153]` fixture, `ColdCorridorRows`, the API
catalog, and `git diff --check`.

## Preserved arithmetic repair at `[172b]` and `[180]`

For

\[
g=2^a u,\qquad u\text{ odd},
\]

an orbit hit modulo `u` alone is insufficient. A direct target hit requires

\[
2^a\mid L+r,
\qquad
2^{k-a}\equiv \frac{L+r}{2^a}\pmod u,
\]

and the exact coefficient

\[
t=\frac{2^k-L-r}{g}
\]

must lie in its residue-specific central range

\[
C_{\rm sys}\le t\le T_r-C_{\rm sys}.
\]

The finitely many exponents `k < a` are checked directly. If there is no exact
hit, the proof retains the full phase modulo `g`, not merely its odd-part
projection modulo `u`. This is why reducing only modulo `u` cannot close the
arithmetic node: it forgets the necessary `2^a` divisibility condition.

## Remaining obligation `[172a]`: connected barrier overlap

### Exact incoming ledger

The nonadditive arm of `[170]` retains the least failed relative graph fibre,
including:

- the reference blocked member and active coordinate;
- the fixed outside-edge record and realized prefix;
- strict failure of the exact denominator-cleared `(F/W)` inequality;
- all earlier coordinate bounds;
- `card(state fibre) ≤ F + 1`;
- graph-fibre monotonicity.

These facts are sufficient to state the paper's next construction, but they do
not by themselves prove connected overlap.

### Required local producer

The next theorem must be residual-local, not a theorem about all graphs:

> Within the current fixed-`(n,m)` conditional fibre, graph-realized barrier
> completions on support families that are disjoint outside their declared root
> windows and interfaces factor while preserving the outside record, the
> realized prefix, window presentations, boundary degrees, simplicity, and all
> blocked-class conditions.

Using only that ledger-local statement, the owner should:

1. choose a cardinality-minimal failed family;
2. suppose its overlap support is disconnected;
3. split it into proper support components;
4. apply minimality within each component;
5. use the local factorization lemma to concatenate their completion orders;
6. contradict the selected failure and publish the connected overlap object.

If factorization is false for the exact incoming fibre, the output must instead
be the precise separated-support realization defect. It must not be renamed a
connected obstruction or sent to the serial-system arithmetic.

## Remaining obligation `[181]`: peeled target-defect demand

Node `[181]` is open by design. Its ledger retains exact stage accounting,
maximal demand, maximal absorption, unique-window blockers, and every registered
peel witness. It does not yet imply a smallness conclusion.

A repair must prove from those local facts one of:

- a sublinear bound on remaining open demand;
- a zero-signature or same-window excess cap;
- a stronger absorber-capacity inequality;
- a typed construction routing every survivor into an existing target-defect
  or route-8 obstruction.

The proof must use the selected incoming ledger. A universal premise about all
graphs or a callback supplying the desired bound would defeat the framework.

## Remaining obligation `[182]`: uncovered pair-code implications

Node `[182]` retains exactly one literal complement:

1. the graph skeleton model with failure of conditional factorization;
2. the exact pair-return package with no typed `[179]` outcome;
3. the graph-realized serial system with no covered `[180]` outcome.

The three constructors require distinct local lemmas.

### Pair conditional factorization

Prove factorization for separated supports in the current conditional fibre,
preserving fixed `n`, fixed `m`, profiles, earlier coordinates, and canonical
demand data. The failed-prefix inequality must be used in its actual direction.

### Pair uncrossing and serial certificate

Construct the switched graphs and prove that they remain in that fibre. A
serial certificate must contain ordered interfaces, internally disjoint graph
paths, disjoint cell interiors, closing returns, graph-derived increment bounds,
and actual simple-cycle realizations. Each early exit must carry the complete
G1/G2/G3/Type B destination witness.

### Full-state periodic routing

When there is no exact target hit, retain the complete finite state and full
phase modulo `g`. A repeated state may route only after constructing an actual
destination object: both contexts for G2, a proper smaller representative for
G3, a complete same-token Type B entry, or a proved bounded table row.

Until all three implications are derived, `[182]` remains an honest endpoint,
not a terminal contradiction.

## Lean implementation discipline

Every remaining repair must satisfy all of the following:

1. read prerequisites from the literal incoming `ExactLedger` with
   `FactInputs.get`, `ExactLedger.get`, or the sealed decision boundary;
2. prove the mathematics inside the owning backend executor, never in
   `Problem.lean`;
3. publish reusable conclusions under their semantic keys and declared
   `FactManifest`;
4. introduce no callback, detached selected-fact theorem, side carrier,
   alternate ledger, or hardcoded proof data;
5. retain every genuine complement as a typed decision arm;
6. prove that every graph construction stays in the selected fixed class and
   that every counted length is an actual simple cycle;
7. update audit rows only from the compiled implementation.

## Recommended order

1. Repair the `[50]` entropy topology so the repetitive-low residual publishes
   `K .dominantRootedWedgeType` and can run the existing `[51]` executor, while
   the nonrepetitive-low residual remains distinct. Resolve the current local
   degree-expression elaboration mismatch without changing the lemma.
3. Compose the remaining Type-B and sparse target-defect outputs into their
   manuscript consumers.
4. Implement `[172a]`'s minimal connected overlap producer from the exact
   failed `[170]` fibre.
5. Prove one exact pressure/smallness or typed-routing theorem for `[181]`.
6. Address `[182]` constructor-by-constructor: conditional factorization,
   pair uncrossing/realizability, then full-state increment routing.
7. Re-run the narrow owners, complete `Assembly.lean`, fixtures, API catalog,
   audit consistency checks, and `git diff --check` after each repair.

## Repository-audit note

The detailed `[19]`, `[171]`, and `[175]`–`[177]` rows agree with the live
implementation. Node `[144]` reaches the common Type-B continuation on the
same ledger, including the completed triangular-port routing producer and the
existing B1/B2/exclusion continuation. The remaining mathematical open set
still includes the `[50]`–`[52]` entropy split/reachability defect, `[172a]`,
`[181]`, `[182]`, and the uncomposed root boundary outputs.
