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

The earlier plan is obsolete in treating `[171]`, `[175]`, and `[176]` as
unimplemented. Those owners now run. A fresh inspection of proposition bodies,
Assembly call sites, and the final result type proves that the claim “only
`[172a]`, `[181]`, and `[182]` remain” is false. The remaining bugs and proof
boundaries are:

1. **Implementation bug at `[19]`** — `C_sp` is computed from the baseline
   degree instead of the routing-label alphabet bound required by the
   manuscript and by `homogeneousTokenCap`;
2. **Missing implementation at `[51]`–`[52]`** —
   `lem:translates-independent` has not been formalized; the entropy rows are
   not that theorem;
3. **Missing implementation at `[79]`–`[81]`** — the shoulder-completion,
   port-return, first-landing, cross-shoulder, and open-port-suppression chain is
   absent, and the code incorrectly jumps from the core definition to a
   conditional certificate cap;
4. **Implementation bug at `[177]`** — the code weakens the required assigned
   Type-B support by adding `AbsorbedGermFanEnvelopeStatement` as a new
   `TypeBFanEntryStatement` disjunct. That is a specification violation, not an
   admissible alternative route;
5. **Uncomposed implementation outputs** — `SelectedLedgerBoundaryResult`
   still returns sparse target-defect, raw/common Type-B accounting, route-8
   sublinear/quotient/rate, and absorbed-germ propositions instead of closing
   or routing them as the manuscript prescribes;
6. **`[172a]`** — on the nonadditive arm of `[170]`, construct the manuscript's
   cardinality-minimal connected barrier-overlap producer and route its actual
   uncrossing outcomes;
7. **`[181]`** — close or type-route the peeled target-defect demand residual
   from its retained stage-accounting and blocker facts;
8. **`[182]`** — prove the uncovered implications left by the exact decisions
   at `[178]`–`[180]`.

Nodes `[178]`–`[180]` are not gaps on their covered arms. Their exact negative
arms are deliberately retained at `[182]`.

The direct evidence is the codomain of `selectedLedgerBoundary`: it returns
several semantic propositions besides the three numbered residuals. None is
definitionally `False`, so successful elaboration does not close them.

## Correctness classification from the live code

### Implementation bug: node `[19]`

`SameTokenBlockerRoles.homogeneousTokenCap` accepts the routing-label alphabet
bound `Q_geom` and internally forms `L_geom = Q_geom + 1`. The application
currently passes `erdosReceiverLoadProfile.baselineDegree`, while the actual
routing-label count is stored separately in `spineData.routingLabelBound`.
Factor that count into one application constant and use it in both places.

### Implementation bug: nodes `[79]`–`[81]`

The live `triangularFanCoreRow` proves only the core and incidence definitions.
Its own comment correctly says it does not prove completion existence. The
common Assembly continuation then jumps directly to `fanCertificateCapRow`.
There are no live propositions or owners for:

- `lem:triangular-shoulder-completion`;
- `lem:triangular-port-return`;
- `lem:triangular-first-landing`;
- `lem:triangular-cross-shoulder`;
- `def:open-port-suppression`.

The conditional cap for an already supplied labelling does not prove any of
these statements. The required fix is to implement them on the literal Type-B
ledger and route their exact alternatives before the certificate/B2 owners.

### Implementation bug: node `[177]`

The aggregate candidate/complement split and corridor-tail witness are real,
but they do not satisfy the manuscript destination. The definition of
`AbsorbedGermFanEnvelopeWitness` expressly denies that it provides the counted
connected remainder core of `DecoratedHandoff.Envelope`. The implementation
then changes `TypeBFanEntryStatement` by accepting that weaker witness as a new
disjunct. This is the bug: the destination contract was weakened to make the
call type-check.

The fix must remove that weaker disjunct from the common Type-B contract and
prove the manuscript's actual assigned-support/decorated-envelope statement
from the incoming `[177]` ledger. If the manuscript does not imply that
conversion, then `[177]` is a manuscript bug and must be repaired there; the
implementation still may not invent a parallel definition.

### Manuscript and implementation agreement at `[153]`

`coldFirstFailureRoutingRow` reads all F1–F4 exclusion/handoff facts, and
`coldGermCandidatesRow` proves the exact candidate/complement and loss
inequalities. The manuscript now defines the same family as Lean: the 11
one-stub interior incidences of an ambient-cubic window, with the first two
dropped as absorbed corridor incidences. Thus `[152]` supplies `9C-o(n)` and
`lem:cold-germ-extraction` supplies `9C/D_cold-o(n)`. The diagram, proof,
dependency ledger, and quantitative closure all use this family.

### Missing implementation: `lem:translates-independent`

No live theorem proves the manuscript's dominant rooted type, wedge, separated
balls, or full-rank translate conclusion. `remainderEntropyDichotomy` and
`entropyPackageRow` do not implement it. Either formalize the lemma exactly, or
prove a replacement route that closes the same incoming branch from the same
ledger. Until one of those proofs exists, the node is not correct.

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

1. Fix `[19]`'s coefficient and implement `[79]`–`[81]`; these affect every
   downstream use of the common Type-B continuation.
2. Repair `[177]` without weakening `TypeBFanEntryStatement`, then compose the
   remaining Type-B and sparse target-defect outputs into their real consumers.
3. Implement `[172a]`'s minimal connected overlap producer from the exact
   failed `[170]` fibre.
4. Prove one exact pressure/smallness or typed-routing theorem for `[181]`.
5. Address `[182]` constructor-by-constructor: conditional factorization,
   pair uncrossing/realizability, then full-state increment routing.
6. Formalize `lem:translates-independent` or prove a fully local replacement
   that closes the identical incoming branch.
7. Re-run the narrow owners, complete `Assembly.lean`, fixtures, API catalog,
   audit consistency checks, and `git diff --check` after each repair.

## Repository-audit note

The detailed `[171]`, `[175]`, and `[176]` rows agree with the compiled source.
The `[144]` and `[177]` rows describe real ledger composition but previously
misclassified that composition as a correct manuscript proof. The code-first
correction ledger in `Assembly_node_audit.md` supersedes those green claims.
The mathematical open set is not yet exactly `[172a]`, `[181]`, and `[182]`.
