# Erdős–Gyárfás Lean port: unresolved compliance work

This ledger records the current Lean implementation and the obligations that prevent full
diagram compliance. `Assembly_node_audit.md` is the status authority. A node belongs here when
its current audit row fails an implementation, wiring, residual-locality, canonical-ledger,
manuscript-fidelity, or kernel gate.

## 1. Authorities and compliance gates

The mathematical authority is `to_formalize/erdos_64_proof.tex`. Its statements, inherited
hypotheses, alternatives, branch order, and terminal behavior determine the required proposition.
The implementation authority is each current Lean declaration type and body, its literal call
site, its semantic-key manifest, and its kernel status. Lean comments and `EG-NODE` annotations
are locators rather than implementation evidence.

A compliant node satisfies all of the following conditions:

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

`[168]`, `[170]`, `[171]`,
`[172]`, `[175]`, `[176]`, `[181]`, and `[182]`.

The current `Assembly.lean` call sites contain these unresolved continuation identifiers:

- `selectedSparseTargetDefectContinuation`
- `selectedDenseSameSizeCanonicalSwap`

`StrategyDag.lean` contains presentation-equality examples and no final `strategyDag`. The package
root imports `Assembly.lean`, so the sealed topology endpoint is absent.

## 3. Dependency order

1. Produce node `[123]`'s declared unified-deficit and entry-census prerequisites on each incoming
   lane, then continue the explicit peeled-demand output at `[181]`.
2. Continue `[125]`'s exact target-defect handoff at the downstream peeling frontier `[181]`.
3. Complete the cold/dense branch at `[168]`--`[172]` and the Type B continuations reached through
   `[175]`--`[176]`.
4. Close node `[182]` by proving the first exact implication that fails in the covered
   `[178]`--`[180]` chain: conditional factorization, exhaustive pair-system uncrossing, or
   exhaustive increment-arithmetic/periodic routing.
5. Define the sealed topology in `StrategyDag.lean` when every node owner composes.

## 4. Node specifications

### Node [153] — actual first-failure incidence and extraction accounting

**Partially implemented.** The corridor, the two actual window interfaces, their offsets, the
bounded active-interface estimate, and the structural terminal/least-repeat support are
current-object constructions. `DeclaredSignature.Value` is indexed by the generating coordinate,
so each D1--D7 kind carries its own current-object value type. The least-repeat witness derives from
state equality and retains, in the published `K .coldCorridorState` fact, equality of every
supported generated reading (including every (D8) combination) together with the complete table
record at both repeated endpoints. The extraction
owner also proves the least high-degree corridor head and every earlier bounded head inside its
atomic executor, publishes that fact once as `K .coldHandoffTransfer`, and
`coldGermCandidatesRow` reads it with `inputs.get`. This is distinct from the paper's F4 Type B or
route-8 handoff, which remains under `K .coldFailureHandoff`.

`valueAt` reads the supported positions, their graph-incidence relation, and the anchored labelled
degree from the current object for each heterogeneous generated coordinate. The F5 owner constructs
both terminal and least-repeat germs inside its atomic executor, carries the complete endpoint
record, and bounds both the actual support and the selected second representative by `M_cold`.
Target response remains an explicit later F2/G2 test; the owner assumes no all-context target
equivalence. The bounded-germ and first-failure witnesses are constructed inside the atomic owner
rather than supplied by detached declarations.

One linked obligation remains.  The row proves the generic implications attached to F1--F4 but
does not construct their earliest occurrence and then select F5 only on the remaining corridors.
Consequently the complement currently called `routedLoss` is only the set-theoretic difference
between all selected stubs and the subcubic eligible F5 occurrences.  In particular it also
contains selected stubs whose second endpoint lies directly in another packed window; no current
ExactLedger input proves that this cross-window class is in the paper's already routed Type B or
route-8 handoff loss, or bounds it by the registered `o(n)` surplus allowance.  Until that literal
F4 routing/absence fact is produced on the surviving cold residual, the displayed
`9C/D_cold-o(n)` inequality must not be inferred from the existing `routedLoss` field.

**Validation.** `ColdCorridor`, `ColdGermFamily`, `SpineVocabulary`, `ColdCorridorRows`,
`SpineRows`, and `HomogeneousBottleneckRows` kernel-build. This validates the bounded-germ owner,
but not the paper's complete node-[153] conclusion while the occurrence-level F4
handoff and routed-loss bound remain absent.

### Node [123] — exact large-budget descent (implemented)

**Current implementation.** `selectedLargeBudgetPressureCensus` requires the literal
`K .route8UnifiedDeficit` and `K .route8UnifiedEntryCensus` facts and delegates to
`selectedRouteEightCensus`. The latter runs the finite exit-(4) descent, closes both true route-8
origins only through node `[124]`, and returns the exact
`K .route8PeeledDemandResidual` ledger on failed reduced rate. The wrapper's return type is that
ledger, not `False`.

**Status.** Node `[123]` is complete and paper-faithful. The current incoming call at
`Assembly.lean:1880` currently stops before this node because it has produced only
`K .route8UnifiedNegative`, not the two declared prerequisites. That is an upstream wiring task,
not a missing proposition or continuation inside node `[123]`.

**Validation.** The complete ExactLedger/Strategy fixture set and `SpineRows` build successfully;
direct elaboration passes the node wrapper and reports the first mismatch at the current incoming call.

### Node [125] — named sparse-exit continuation (implemented)

**Current implementation.** `selectedSparseSurplusDichotomy` publishes either `K .sparsePairExit`
or `K .sparseSurplusSurvivor`. `selectedLedgerClosure` sends the survivor ledger to
`selectedStrictSurplusBranch` and sends the sparse-exit ledger through
`sparseSurplusExitRoutingRow`. The four terminal constructors close inside that sealed row. The
target-defect constructor produces the exact `K .sparseTargetDefectResidual` ledger, which reaches
`selectedSparseTargetDefectContinuation`.

**Status.** Node `[125]` is complete.  The left arm closes the four terminal constructors and
publishes the concrete attempted-quotient defect under `K .sparseTargetDefectResidual`; the right
arm alone writes `K .sparseSurplusSurvivor` into the exact ledger consumed by `[126]`--`[129]`.
Processing the published target-defect handoff is a downstream peeling obligation, currently
named `selectedSparseTargetDefectContinuation`, not missing work inside node `[125]`.

**Required validation.** The target-defect handoff must preserve its exact key and complete
ancestry and must continue through registered Strategy owners.

### Node [162] — dense hot/cold pass (implemented)

**Current implementation.** The dense arm of `selectedNearCubicBranch` executes the shared
hot/cold decisions and cold first-failure rows on the literal dense residual. On the linear cold
arm, `remainderNormalizationRow` supplies induced-(P_{13})-freeness for the remainder of the
same canonical maximal packing. `coldFirstFailureRoutingRow` publishes the retained corridor
state with every component and selected path inside that remainder.
`denseColdCorridorsTerminalRow` reads `K .coldCorridorState`, `K .remainderNormalized`, and
`K .hotColdPartition` with `inputs.get`, uses the canonical path's schedule-minimality to bound
its length, and publishes the exact incoming state together with terminality of every corridor
under `K .denseColdCorridorsTerminal`.

**Status.** Node `[162]` is complete and paper-faithful. The exact output ledger continues to the
neutral configuration decision `[163]`; the all-cold branch reaches `[164]`. The canonical arm
has the exact `[165]`--`[166]` replacement/minimality owners. The graph-realized arm runs the
exact `[167]` finite check and passes its survivor ledger to the endpoint exclusion at `[168]`.

**Validation.** The exact `[163]` decision, `[167]` owner, restricted `9C` selection, and `[168]`
endpoint-exclusion owner kernel-check in isolated slices.

### Nodes [165]--[166] — refined minimality swap

**Current implementation.** `CanonicalReplacementSwapStatement` is quantified over every
neutral equal-length terminal configuration of the selected object. `canonicalReplacementSwapRow`
reads the canonical branch entry with `inputs.get` and publishes the universal exchange:
whenever `E ≠ Q`, gluing `E` into the retained outside context preserves the baseline, target
avoidance, vertex count, and edge count and strictly decreases the canonical-decomposition
coordinate. `canonicalReplacementTrivialRow` reads that exchange and `K .selection` with
`inputs.get`; refined minimality rules out `E ≠ Q` and publishes universal `Q = E` under
`K .coldCanonicalReplacementTrivial`.

**Status.** Nodes `[165]` and `[166]` implement `lem:refined-minimality-swap`. The universal
equality remains in the ExactLedger for `[169]` and for later identifications of neutral pieces.

**Validation.** `SpineVocabulary.lean` and an isolated current [165]--[166] ExactLedger
executor check kernel-check. Whole-module `ColdCorridorRows.lean` validation remains pending
because its full [145]--[177] elaboration exceeds the bounded validation window.

### Node [167] — finite two-strand check (implemented)

**Current implementation.** `K .coldGenuineSecondStrand` retains the two equal-length ambient
strands, their common attachment vertices, the window segment, the path and disjointness
certificates needed to form the pair and segment cycles, their exact lengths, and the registered
finite bound. `twoStrandSurvivorRow` reads that key and `K .selection` with `inputs.get` and
constructs the cycles of lengths `2ℓ` and `ℓ+d` inside the executor. If either length is dyadic,
`Data.lengthOK_iff_powerOfTwo` makes that cycle an accepted target and contradicts the selected
graph. The remaining arm is published as `K .coldTwoStrandSurvivor`, with membership in
`Graph.TwoStrand.survivors data.windowOrder (twoStrandEnumerationBound data)`.

**Status.** Node `[167]` is complete. Both graph-realized Assembly branches run its registered
owner and expose the literal survivor ledger to `[168]`; `[167]` does not claim `False` on that
arm.

**Validation.** `SpineVocabulary.lean`, the isolated `[163]` decision, and the isolated `[167]`
`factOnly` owner kernel-check.

### Node [168] — endpoint attachment of the surviving pair

**Current implementation.** `selectedStubs` is the paper's restricted selection: the external
stub list is filtered to the one-stub interior window vertices and the two corridor ends are
absorbed. `coldInteriorBranchExcess` is therefore the registered `9` per ambient-cubic `P₁₃`,
and the `[152]`--`[153]` extraction uses its `9C` lower bound. The `[163]` witness retains the exact
selected occurrence that produced its germ, proves that occurrence belongs to the same window,
and identifies it with one of the pair's four strand stubs.

`symmetricPairEndpointExclusionRow` reads `K .coldWindowStubStructure` and
`K .coldTwoStrandSurvivor` through `inputs.get`. Two distinct stubs at each attachment force both
attachments into the published endpoint set. The retained selected occurrence has external
degree one, while either endpoint has external degree two, so the row publishes
`K .coldSymmetricPairExcluded`. Both Assembly paths run the stub-structure owner and use
`AtomicCT.runAndCloseIncompatible` to commit the distinguished closure against the survivor.

**Status.** Node `[168]` is complete.

**Validation.** `ColdGermFamily.lean` and `SpineVocabulary.lean` kernel-check; isolated checks for
the restricted `[152]` mass, `[153]` positivity, `[168]` owner, and canonical incompatibility
closure kernel-check.

### Node [170] — scale-additivity decision

**Current implementation.** `scaleAdditivityDichotomy` decides
`BlockedScaleAdditivityStatement`. That proposition combines the fixed-scale conditional-fibre
bound with node `[171]`'s global compression inequality. Its complement is
`¬ BlockedScaleAdditivityStatement`.

**Missing obligation.** Make node `[170]` decide only the fixed-scale additivity assertion.
Derive node `[171]`'s global inequality on the positive arm. On the negative arm, publish the
specific failed fixed-scale inequality required by `lem:barrier-failure-overlap`.

**Required validation.** Each decision arm must state its own node proposition, and the negative
arm must imply the overlap obstruction's hypothesis.

### Node [171] — blocked-class compression

**Current implementation.** `blockedCompressionRow` reads `blockedClassMember` and
`blockedScaleAdditive` through `inputs.get`. Its sealed executor performs the canonical finite
prefix exposure, multiplies the conditional `F/W` fibre inequalities, converts the registered
products to the package-bit rate, and publishes `blockedCompressionBound` and
`blockedCompressionCap`. `blockedCompressionCloses` runs that row and closes the cap against the
inherited `densePackingOverflow` fact with `AtomicCT.runAndCloseIncompatible`.

**Missing obligation.** In `selectedCanonicalReplacementContinuation`, match the live node `[170]`
decision, invoke `blockedCompressionCloses` on the additive arm, and pass the nonadditive arm to
node `[172a]`'s overlap producer.

**Required validation.** The complete application composition must elaborate with the additive
arm closed at `[171]` and the nonadditive arm entering `[172a]` on its literal ledger.

### Node [172] — fixed-scale overlap serial system

**Current implementation.** The negative arm of `scaleAdditivityDichotomy` calls
`selectedBarrierOverlapSerialSystem`. `SerialSystemArithmetic.lean` supplies a graph-free
arithmetic core. No owner constructs the graph-derived overlap obstruction or scale-spanning
window system.

**Missing obligation.** Construct the minimal connected barrier-overlap obstruction from the
failed fixed-scale additivity statement, uncross it into the manuscript's serial window system,
instantiate the spectrum, and connect the realized outcome to the target cycle.

**Required validation.** The obstruction and serial system require registered semantic keys and
one monotone ledger path through the arithmetic terminal.

### Node [175] — selected-corridor high-degree split

**Current implementation.** `absorbedGermSplitRow` reads `K .coldCorridorState` and
`K .slackIndependent`, retains the routing state's exact incidence, and publishes the
per-half-edge subcubic-support or heavy-centre alternative. The subcubic member is in the exact
filtered image of that incidence; the heavy-centre member has threshold-degree neighbours.
`absorbedGermDichotomy` chooses globally between a nonempty candidate family and the all-heavy
fan-data branch. A mixed residual enters the candidate branch without transferring its
heavy-centre incidences to Type B. The EG call site cannot enter the split until node `[153]`
publishes `K .coldCorridorState` and the extraction estimates.

**Missing obligation.** Preserve and consume the per-half-edge split so that subcubic incidences
enter the graph-realized chain and heavy-centre incidences enter the Type B chain on the same
residual. The empty ambient-cubic family also requires an explicit branch.

**Required validation.** Mixed, all-subcubic, all-heavy, and empty cases must be exhaustive. Each
output must retain the selected corridor and first-failure support. Validation of the composed
path requires the exact upstream state producer.

### Node [176] — graph-realized cold configuration

**Current implementation.** The candidate arm is built from the exact subcubic filtered image of
the routing incidence and retains its overlap and charged-count inequalities. It runs the germ
trichotomy, same-interface table, cold-branch row, neutral-symmetry decision, and canonical-size
decision. The canonical same-size arm reaches `selectedDenseSameSizeCanonicalSwap`; the
graph-realized arm runs `twoStrandSurvivorRow` and reaches `[168]` with
`K .coldTwoStrandSurvivor`. The all-heavy arm constructs [177]'s `typeBFanEntry` from the
actual return corridor and returns that exact ledger directly to the common Type B node [65].

The graph-realized arm runs the `[168]` endpoint/interior exclusion and closes through the
distinguished ExactLedger closure. The canonical arm uses the `[165]`--`[166]` owners.

**Implementation bug.** The per-half-edge routing is preserved and the common
node-[65] function is now called, but its input contract was weakened:
`TypeBFanEntryStatement` admits `AbsorbedGermFanEnvelopeStatement` as a new
disjunct even though that witness explicitly lacks the manuscript's counted
connected assigned support. Remove the parallel disjunct and prove the actual
`[177]` → `[65]` conversion, or repair the manuscript if that implication is
false.

**Required validation.** Every candidate and heavy-centre arm must terminate through its
manuscript continuation.

### Node [178] — pair-overlap obstruction

**Implemented system owner.** `pairOverlapSystemRow` publishes the actual fixed-`(n,m)` skeleton
model and the correctly polarized binary predicate: an exposure order must retain at least two
response values at every conditional prefix. Its finite-prefix branching count is proved
anonymously inside the sealed executor and committed only as `K .pairOverlapSystem`; the former
standalone `branching_card_bound` proof has been removed. `pairConditionalFactorizationDichotomy`
then decides the paper's two graph-level factorization clauses on that exact model.

**Implemented overlap owner.** The positive ledger is the only input accepted by
`pairFailureOverlapRow`. Inside that sealed executor, the row inclusion-minimizes the failed
family, obtains two distinct off-return overlapping coordinates from the retained separated
clause, and proves
`ConnectedOn inputs.current.object (system.overlapSupport family)` by the manuscript's component
argument. If the support were disconnected, its components split the family into two proper
nonempty blocks; the stored minimality realizes both blocks and the stored concatenation clause
realizes their union, contradicting the obstruction. The former detached theorem
`connectedOn_biUnion_of_minimal_not_realizing` has been deleted. No factorization fact is derived
from blocker absence.

**Next separate topology defect.** The later `lem:pair-count-or-arithmetic` composition still uses
the custom `selectedPairCountFailureContinuation` `Sum` wrapper. That wrapper is not part of the
now-complete `lem:pair-failure-overlap` owner and must be replaced at its own label by literal
typed `ExactLedger` branch composition.

**Complement.** If conditional factorization is unavailable, the decision publishes
`PairUncoveredResidual.factorization system failure` under the single node-[182] key. The exact
model and `¬ system.ConditionalFactorization` are retained; the branch is not renamed as a
blocker, quotient, sparse exit, or Type B witness.

### Node [179] — pair serial demand system

**Implemented covered arm.** `pairDemandReturnsRow` is the first sealed `[179]` owner. It reads
`K .pairFailureOverlap`, recovers the failed schedule member's two literal active demands, and
publishes `K .pairDemandReturns` on the same `ExactLedger`.  The value reuses the canonical return
selected by `pairResponseActivation`, proves both endpoints of both demands lie in the connected
`X_π ∪ R_p ∪ R_q` connector, selects the two oppositely oriented connector paths, derives
`ℓ_ret` as the maximum of the two actual return lengths, and defines
`D_sp = 2 M_cold + 2 ℓ_ret`. `PairSerialDemandSystem` represents the paper object itself: ordered
interfaces, nonempty length families, actual graph walks, path/support/incidence proofs,
within-cell and cross-cell interior disjointness, the two exact closing returns, graph-derived
increment bounds, and an actual simple cycle for every route choice. The other outcomes carry an
actual target cycle, named sparse exit, or Type B entry. `pairSystemOutcomeDichotomy` routes these
forms without reconstructing any proof.

**Complement.** `pairSystemRealizabilityDichotomy` publishes
`PairUncoveredResidual.systemRealizability returns failure` at [182] when the manuscript's five-way
uncrossing proposition is not available for the exact return package.

### Node [180] — pair increment arithmetic

**Implemented covered arm.** `pairIncrementOutcomeDichotomy` retains either a concrete periodic
sparse-exit/Type-B outcome or `PairSerialArithmetic` for the exact graph-realized `[179]` system.
The arithmetic package uses the full modulus and the complete central-range doubling orbit.
`pairPowerOfTwoCycleRow` constructs the canonical `SerialSystem.System.spectrum`, whose `Realized`
predicate is definitionally `PairSerialRealized` on the selected graph, applies
`Spectrum.exists_pow_realized`, proves the exponent is at least two from cycle simplicity, and
publishes the registered target cycle before the standard incompatible closure against selection.

**Complement.** If neither covered increment outcome exists,
`pairIncrementCoveredDichotomy` publishes
`PairUncoveredResidual.incrementArithmetic serial failure` at [182].

### Node [182] — uncovered pair-chain implication

**Open by construction.** `PairUncoveredResidual` is the disjoint union of exactly three negated
paper implications: conditional factorization of the actual skeleton model, exhaustive `[179]`
uncrossing of the actual return package, or exhaustive `[180]` arithmetic/periodic routing of the
actual graph-realized serial system. `selectedPairCountFailureContinuation` runs the complete
covered `[178]`--`[180]` chain and returns only a genuine Type B entry or this ExactLedger-published
residual; a power-of-two cycle closes internally.

**Missing obligation.** Prove the relevant retained implication on the specific selected residual.
Until then the public theorem is intentionally reduced to closure of `selectedLedgerBoundary`; no
unconditional theorem silently assumes away [182].

### Node [181] — peeled target-defect demand residual

**Current implementation.** The failed-rate arm of `selectedRouteEightCensus` constructs the
stage accounting, maximal demand ledger, maximal absorption, unique-window blockers, and
`K .route8PeeledDemandResidual`. `selectedLargeBudgetPressureCensus` returns that exact ledger to
the enclosing topology. The residual proposition contains no smallness or terminal contradiction.

**Missing obligation.** Supply the manuscript continuation for the peeled target-defect demand
residual and close or route every constructor using the facts retained in its ledger.

**Required validation.** The consumer must read `K .route8PeeledDemandResidual` from the literal
node `[123]` ledger and terminate through registered rows or a named manuscript handoff.

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

The label groups relevant to this ledger are L17 (`[123]`, `[181]`), L19 (`[125]`), L26
(`[167]`--`[168]`), L27 (`[170]`--`[172]`), L28 (`[175]`--`[176]`), and L29
(`[178]`--`[180]`, `[182]`).
