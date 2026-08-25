# Erdős–Gyárfás Lean port: unresolved compliance work

This ledger describes the present Lean implementation and the unresolved work needed for full
180-node compliance. `Assembly_node_audit.md` is the status authority. A node belongs here exactly
when its current audit row fails at least one implementation, wiring, residual-locality,
canonical-ledger, manuscript-fidelity, or kernel gate.

## 1. Authorities and compliance gates

The mathematical authority is `to_formalize/erdos_64_proof.tex`. Its statements, inherited
hypotheses, alternatives, branch order, and terminal behavior determine the required proposition.
The implementation authority is the current Lean declaration type and body, its literal call
site, its semantic-key manifest, and a kernel check. Lean comments and `EG-NODE` annotations are
locators, not implementation evidence.

A node is compliant when all of the following hold:

1. The exact manuscript proposition or exhaustive alternative is represented.
2. A sealed `factOnly`/`AtomicCT.run`, `Decision.run`, canonical terminal, or straight-line
   composition owns the step.
3. The owner obtains the active residual from `FactInputs.current`, reads every prerequisite with
   `FactInputs.get`, and publishes every reusable result through its declared semantic key.
4. The literal predecessor ledger reaches the owner on the correct typed branch.
5. The implementation uses one canonical `ExactLedger`, with no callback, proof carrier,
   reconstructed cursor, alternate ledger, or application-local mathematical interface.
6. The narrow owner and its composed branch kernel-check without an unresolved producer or
   admitted mathematical goal.

## 2. Current unresolved set

The unresolved diagram nodes are:

`[123]`, `[144]`, `[162]`, `[165]`, `[166]`, `[167]`, `[168]`, `[170]`, `[171]`,
`[172]`, `[175]`, `[176]`, `[178]`, `[179]`, and `[180]`.

The current `Assembly.lean` call sites contain these unresolved continuation identifiers:

- `selectedRouteEightFailedStageClosure`
- `selectedRouteEightQuotientResidual`
- `selectedTypeBSublinearResidual`
- `selectedDenseSameSizeCanonicalSwap`
- `selectedGenuineSecondStrandCloses`
- `selectedBarrierOverlapSerialSystem`
- `selectedRouteEightBudgetEdge`
- `selectedAbsorbedTypeBFanHeavyContinuation`
- `selectedAbsorbedTypeBFanDegreeFourContinuation`
- `selectedSparsePairSerialSystem`

`StrategyDag.lean` contains presentation-equality examples but no final `strategyDag`; the package
root imports `Assembly.lean`. The sealed topology endpoint therefore remains absent.

## 3. Dependency order

1. Close the unified route-8 failed-rate arm at `[123]` and its two tested residual lanes.
2. Prove the three same-token routing implications used twice by `[144]`.
3. Complete the cold/dense branch at `[165]`--`[172]` and the two Type B continuations reached
   through `[175]`--`[176]`.
4. Construct the pair-obstruction, serial-system, and arithmetic chain `[178]`--`[180]`.
5. Define the sealed topology in `StrategyDag.lean` after every node owner composes.

## 4. Node specifications

### Node [123] — large-budget demand descent

**Current implementation.** `route8PeelingDescentRow` constructs the finite peel chain.
`route8StageOutcomeDichotomy` separates the true route-8 survivor from
`∃ chain, PeelChain chain ∧ ¬ StageRate chain.toFinset`. The survivor reaches
`route8UnifiedTerminalNoGoRow` and node `[124]`. The failed-rate arm calls
`selectedRouteEightFailedStageClosure`. `selectedLargeBudgetPressureCensus` also exposes the
tested quotient and Type B sublinear residuals through `selectedRouteEightQuotientResidual` and
`selectedTypeBSublinearResidual`.

**Unresolved obligation.** Prove the manuscript's claimed contradiction for the exact failed
stage from the large-budget net-deficiency cap and `thm:branch-kill`, including the bridge slack
present in `StageRate`. Route the quotient and Type B sublinear residuals through their stated
manuscript continuations on the same ledger.

**Required validation.** The descent, both decision arms, both residual lanes, and the `[124]`
survivor must elaborate as one composition. The failed-rate proof must not use a conditional S24
criterion as an unconditional contradiction.

### Node [144] — same-token bottleneck discharge

**Current implementation.** `sameTokenBottleneckRoutingRow` reads
`homogeneousBottleneckPattern`, `activeSurplusDemands`, `cubicBaseline`,
`capacityTokenLedger`, `selection`, `degreeProfileFibres`,
`targetCompleteContextUniversality`, `replacementExclusion`, and `uncompressible`. It derives the
matching/star endpoint choice, routing-label collision, registered configurations, common root,
connected parallel/switch supports, first-separator tails, and the high-degree envelope after
the cubic exclusion.  Its cubic incidence argument is exhaustive: it uses the last common-prefix
vertex when the prefix is nonempty and derives the unique third incidence from the registered
cubic degree equation when the routes diverge immediately.

**Unresolved obligation.** Four mathematical goals remain: for each of the matching and star
shapes, prove the parallel declared-identification route and the cubic-switch route.  The remaining
work is to expose through the registered homogeneous-pattern fact the two same-boundary response
readings and the proper/closed representative data used by those quotient arguments; immediate
divergence no longer leaves an obligation.

**Required validation.** The one sealed owner must publish `bottleneckRouting` and `typeBHandoff`
for all three class routes without an admitted goal or auxiliary route carrier.

### Node [162] — dense hot/cold pass

**Current implementation.** The `.right` arm of `selectedNearCubicBranch` runs the shared
`[22]`--`[23]` hot/cold split and state-count contradiction on the literal dense residual. The
larger-residual path retests the supply bound at `[160]` and enters the cold owners.

**Unresolved obligation.** The composed branch reaches the same-size canonical swap, genuine
second-strand, barrier-overlap serial-system, and exact route-8 budget-edge frontiers. Complete
those owners and preserve the dense residual through every call.

**Required validation.** Both dense arms must elaborate through their terminal continuations;
the shared hot/cold decision must append only its declared key pair.

### Node [165] — same-size canonical replacement

**Current implementation.** `canonicalSwapSizeDichotomy` separates
`coldCanonicalSwapSmaller` from `coldCanonicalSwapSameSize`. `selectedCanonicalSwapCloses`
closes the strictly smaller vertex-count arm. The same-size arm calls
`selectedDenseSameSizeCanonicalSwap`.

**Unresolved obligation.** Implement the manuscript's same-size swap using the refined order
`(|V|, |E|, Φ)` and close the `coldCanonicalSwapSameSize` ledger. The current two-coordinate
`lexicographicProgress` API does not express the `Φ` tie-break.

**Required validation.** The constructed canonical germs must make the two decision arms
exhaustive, and the same-size arm must close through a sealed terminal owner.

### Node [166] — refined lexicographic minimality

**Current implementation.** No declaration publishes node `[166]`. The case assumption
`coldCanonicalSwapSameSize` reaches `selectedDenseSameSizeCanonicalSwap`.

**Unresolved obligation.** Extend the progress proposition to the manuscript's
`(|V|, |E|, Φ)` order, prove the `Q = E` consequence at the selected canonical germ, and expose
that proof through the `[165]` terminal owner.

**Required validation.** The proposition must be residual-local and must not be encoded as an
application callback or an unregistered side theorem.

### Node [167] — finite two-strand closure

**Current implementation.** `TwoStrandEnumeration.lean` contains a `decide`-checked arithmetic
enumeration, but no Strategy key, row, or Assembly declaration instantiates it at the selected
graph-realized strand pair. The corresponding branch calls `selectedGenuineSecondStrandCloses`.

**Unresolved obligation.** Instantiate the finite check with the selected pair and its closing
lengths `2ℓ` and `ℓ+d`, connect the arithmetic survivor statement to
`HasCycleWithLength`, and publish the terminal contradiction on the incoming ledger.

**Required validation.** The Strategy owner and the application branch must kernel-check; a
module import or doc comment is not implementation evidence.

### Node [168] — endpoint attachment of the surviving pair

**Current implementation.** `coldWindowStubStructureRow` publishes the selected-stub and
endpoint hypotheses. It does not state either conclusion of `lem:symmetric-pair-endpoint`; the
symmetric-pair exclusion appears only in prose.

**Unresolved obligation.** Publish the two endpoint conclusions for the selected surviving pair
and consume them in the node `[167]` closure.

**Required validation.** The owner must read the actual selected pair and append a semantic key
whose `Holds` proposition is exactly the manuscript lemma.

### Node [170] — scale-additivity decision

**Current implementation.** `scaleAdditivityDichotomy` decides
`BlockedScaleAdditivityStatement`. That proposition combines the fixed-scale conditional-fibre
bound with node `[171]`'s global compression inequality. Its complement is
`¬ BlockedScaleAdditivityStatement`.

**Unresolved obligation.** Make node `[170]` decide only the fixed-scale additivity assertion.
Derive node `[171]`'s global inequality on the positive arm. On the negative arm, publish the
specific failed fixed-scale inequality required by `lem:barrier-failure-overlap`.

**Required validation.** Neither decision arm may assume the conclusion of its successor, and
the negative arm must be strong enough to construct the overlap obstruction.

### Node [171] — blocked-class compression

**Current implementation.** `blockedClassCompressionCloses` reads
`blockedScaleAdditive`, `blockedClassMember`, and `densePackingOverflow` and derives
`card 𝓑(𝒫) < 1`. The needed global compression inequality is already a conjunct of
`BlockedScaleAdditivityStatement`.

**Unresolved obligation.** Prove the encoding injectivity and uncompressed baseline inside a
sealed owner, derive the global compression inequality from node `[170]`'s fixed-scale facts,
and then run the existing arithmetic terminal.

**Required validation.** The compression bound must be produced, registered, and consumed on
the literal additive-arm ledger rather than assumed by the decision proposition.

### Node [172] — fixed-scale overlap serial system

**Current implementation.** The negative arm of `scaleAdditivityDichotomy` calls
`selectedBarrierOverlapSerialSystem`. `SerialSystemArithmetic.lean` supplies a graph-free
arithmetic core, while no owner constructs the graph-derived overlap obstruction or the
scale-spanning window system.

**Unresolved obligation.** From the exact failed fixed-scale additivity statement, construct the
minimal connected barrier-overlap obstruction, uncross it into the manuscript's serial window
system, instantiate the spectrum, and connect the realized outcome to the terminal target cycle.

**Required validation.** The obstruction and serial system require registered semantic keys and
one monotone ledger path through the arithmetic terminal.

### Node [175] — selected-corridor high-degree split

**Current implementation.** `absorbedGermSplitRow` publishes the manuscript's per-half-edge
subcubic-support or heavy-centre alternative. `absorbedGermDichotomy` then chooses globally
between a nonempty candidate family and the all-heavy fan-data branch. In a mixed residual, the
candidate branch does not route its heavy-centre incidences to Type B.

**Unresolved obligation.** Preserve and consume the per-half-edge split so that subcubic
incidences enter the graph-realized chain and heavy-centre incidences enter the Type B chain on
the same residual. Cover the empty ambient-cubic family explicitly.

**Required validation.** Mixed, all-subcubic, all-heavy, and empty cases must be exhaustive, and
each output must retain the selected corridor and first-failure support that justified it.

### Node [176] — graph-realized cold configuration

**Current implementation.** The candidate arm of `selectedAbsorbedGermResidual` runs the germ
trichotomy, same-interface table, cold-branch row, neutral-symmetry decision, and canonical-size
decision. It reaches `selectedDenseSameSizeCanonicalSwap` or
`selectedGenuineSecondStrandCloses`. The all-heavy arm reaches the two unresolved Type B fan
continuations.

**Unresolved obligation.** Complete nodes `[165]`--`[168]`, preserve the per-half-edge routing
from `[175]`, and implement the heavy and degree-four Type B continuations without bypassing
their common `typeBFanEntry` ledger.

**Required validation.** Every candidate and heavy-centre arm must terminate through its
manuscript continuation, with no unregistered application-level branch function.

### Node [178] — pair-overlap obstruction

**Current implementation.** `freePairEntropyDichotomy` and `blockedPairEntropyDichotomy`
publish the bare negations of their pair-entropy sandwich propositions. The code defines no key
for the minimal pair-overlap obstruction and both residual arms call
`selectedSparsePairSerialSystem`.

**Unresolved obligation.** Construct `lem:pair-failure-overlap`'s minimal obstruction from each
exact entropy failure, publish it under a semantic key, and retain every prerequisite used in
the construction.

**Required validation.** Both entropy-failure lanes must reach the same obstruction owner on
their literal ledgers.

### Node [179] — pair serial demand system

**Current implementation.** No Strategy declaration publishes a graph-derived pair serial
system. `SerialSystem.Spectrum` is graph-free, and `D_sp` and `ℓ_ret` are not instantiated in
the Assembly path.

**Unresolved obligation.** Uncross the node `[178]` obstruction into a scale-spanning chain of
interfaces with the manuscript's bounded increments and return length, and publish that system
on the same branch ledger.

**Required validation.** The semantic key, `Holds` proposition, manifest, owner, and Assembly
call must all refer to the active graph and selected obstruction.

### Node [180] — pair increment arithmetic

**Current implementation.** `Spectrum.exists_pow_realized` proves the natural-number arithmetic
core. No graph-derived `Spectrum` discharges `ScaleSpanning`, and no `S.Realized` value is
connected to the target cycle or periodic-response routing.

**Unresolved obligation.** Instantiate the arithmetic core on node `[179]`'s system, turn a
realized power-of-two increment into `HasCycleWithLength`, and route the periodic response class
to the named sparse exit or Type B alternative.

**Required validation.** The Assembly path must use a sealed sequence of registered rows and
terminal continuations that kernel-check from both node `[178]` lanes.

## 5. Validation contract

For each resolved node:

1. Inspect the owner type, body, manifest, and literal call site.
2. Check every `Requires` key is read and every `Produces` key is returned.
3. Check the active object comes from `FactInputs.current` and all reusable facts use semantic
   keys.
4. Kernel-check the narrow owner and an independent branch composition.
5. Run the aggregate build and the axiom/API audit when all required `.olean` files exist.
6. Keep the corresponding paper-fact and node rows in `Assembly_node_audit.md` synchronized with
   the compiled term.

The label groups relevant to this ledger are L17 (`[123]`), L24 (`[144]`), L26
(`[162]`, `[165]`--`[168]`), L27 (`[170]`--`[172]`), L28 (`[175]`--`[176]`), and
L29 (`[178]`--`[180]`).
