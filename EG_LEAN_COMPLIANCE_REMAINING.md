# Erdős–Gyárfás Lean port: remaining work for full 180-node compliance

> **Live remediation ledger.** This file records only nodes that do not currently pass every
> implementation, paper-fidelity, kernel, wiring, residual-locality, and canonical-ledger gate.
> `Assembly_node_audit.md` remains the live status authority; this ledger explains how each
> non-green row must be repaired. Remove a section only after both audit tables are updated
> from fresh Lean evidence and every checkbox in that section is green.

## 1. Authorities and scope

The mathematical authority is `to_formalize/erdos_64_proof.tex`: its statements, inherited
hypotheses, alternatives, branch order, and terminal behavior are immutable. The authority for
the implementation is the current Lean declaration type and body, its literal call site, exact
key index and manifest, and a fresh kernel/build result. Comments and `EG-NODE` annotations are
locators only. `LEAN_PORT_HANDOFF.md` is dated context, not live status.

This is a documentation and remediation specification. It does not authorize replacing a paper
argument, adding an axiom or callback, inventing a proof-data interface, or repairing a second
node while implementing one row. Each future repair remains a one-label Type-A task.

## 2. Definition of a fully compliant node

A node is complete only when all of the following hold:

1. Its exact manuscript proposition or exhaustive alternative is represented; a stronger,
   weaker, vacuous, or differently ordered surrogate does not count.
2. Its proof is the value returned for a declared `Produces` key by a sealed atomic executor,
   or it is a literal `Decision.run`/canonical terminal as prescribed by the paper.
3. The executor reads the active object from `FactInputs.current`, reads every prerequisite with
   `FactInputs.get`, and appends a nonempty `FactManifest` with `AtomicCT.run` to the same
   `ExactLedger`.
4. The row is run after the literal incoming ledger on the correct typed branch. No sibling fact,
   reconstructed cursor, custom carrier, callback, alternate ledger, or application-local helper
   transports mathematical information.
5. Every externally reusable witness, bound, classification, or branch decision is published
   under one exact semantic key, registered at all six vocabulary sites, and actually consumed
   where the manuscript uses it.
6. The narrow owner and the composed branch kernel-check without an undefined frontier producer;
   the audit tables and sealed report agree with the compiled term.

The only permitted implementation shapes are the existing Type-A patterns: `factOnly` plus a
literal manifest and `AtomicCT.run`, a binary `Decision.run`, a canonical closure, or straight-line
composition of those typed outputs. Mathematical helper theorems detached from the executor are
not an acceptable intermediate state.

## 3. Current measured state

- Diagram nodes audited: **180**.
- Nodes passing every strict gate: **159**.
- Nodes retained in this ledger: **21**.
- Axiom-audit declarations: **75** = **49 clean** + **26 tainted**; unreported: **0**.
- Loud undefined frontier producers: **10**. Node [144] is no longer represented
  by an undefined producer; its anonymous sealed executor stops at one explicit
  unsolved mathematical goal.

### Loud frontier producers

- `selectedAbsorbedGermBlockedResidual`
- `selectedAbsorbedTypeBFanHeavyContinuation`
- `selectedAbsorbedTypeBFanDegreeFourContinuation`
- `selectedBarrierOverlapSerialSystem`
- `selectedDenseJointCodeOverflow`
- `selectedDenseSameSizeCanonicalSwap`
- `selectedLargeBudgetPressureCensus`
- `selectedRouteEightBudgetEdge`
- `selectedSparsePairSerialSystem`
- `selectedTypeAVisibleRouteEightImpossible`

### Cross-cutting framework blockers

- `StrategyDag.lean` contains only presentation-equality examples and no final `strategyDag`; the
  package root still imports the application-local `Assembly.lean`. Full closure therefore lacks
  the sealed topology endpoint required by the framework.
- The default `SpineRows` build is currently blocked by the independently modified Type B
  absorbed-germ owners, beginning at line 3281. Error recovery continues through [116] and reports
  no error in `route8SmallCoreExitRow`; the focused [116] vocabulary and elimination checks pass.
- The current `api_catalog.py` run stops because the independently modified
  `ColdCorridorRows.olean` artifact is unavailable. That export failure is outside [116].

### Exact section set

[123], [144], [162], [165], [166], [167], [168], [170], [171], [172], [174], [175], [176], [178], [179], [180].

## 4. Dependency-ordered repair route

1. **Type A and route 8:** implement the later unified-census producer required by [123]. Node
   [111] is now exactly the paper's deterministic `\mathcal X_A`/`D_A` extraction; the unrelated
   branch-kill classification no longer imports [114]/[123] facts into that node. Node [104]
   closes the literal selected trace-basin compression against inherited uncompressibility.
   Node [116] now closes the small-core branch by reading alternative (b) exactly as the paper's
   nontrivial target-complete response quotient, without an admissibility strengthening.
2. **Sparse-surplus accounting:** resolve the missing same-token routing-germ construction at
   [144]. Node [129] now publishes the paper's active-family baseline package through a sealed
   row; nodes [131]–[143], the direct [145] handoff, and [147]'s rate conversion use the literal
   monotone `ExactLedger` path.
3. **Cold/dense branch:** repair [154], [156], [157], [159], [162]–[172], and [174]–[176].
4. **Pair serial closure:** construct the exact obstruction/system/arithmetic chain [178]–[180].
5. **Sealed endpoint:** only after every node owner is green, express the final topology in
   `StrategyDag.lean`, switch the package root to it, and regenerate the sealed report.

The ordering is diagnostic; it does not authorize a multi-node implementation change. A repair
still stops at its first downstream failure and updates only that label's two audit rows.

## 5. Node-by-node remediation checklists

### Node [123] — unified demand descent

**Exact manuscript diagram output.** The unified Type A ledger contains both target-defect and
route-8 entries. A target-defect two-support entry supplies the canonical exit-(4) peel and lowers
\(\Lambda_4\); a terminal survivor is a true two-support route-8 entry sent to [124].

**Current Lean owners.** `route8PeelingDescentRow` and `route8PeelingTerminalRow`.

**Primary defect class.** Mathematical proof absent at the unified-census producer.

**Fresh audit diagnosis.** ⚠ PARTIAL, WITH THE BURDEN NOW A THEOREM — the flat claim
`route8Deficit ≤ route8UnifiedEntries.card` (`s·D̃_A ≤ |Ξ̃|`) is removed from
`Route8UnifiedCensusFacts`: it is unprovable, because `Ξ̃` counts only silent unpaid loads while
`rem:unified-covers-exit4` keeps visible exit-(4) supports in the collection. In its place the
staged burden is proven: `Graph.Route8Pressure.stage_burden` gives
`s·D̃_A ≤ |Ξ̃ ∖ P₄| + |P₄|` at every stage where each visible excess load is peeled, from the
staged silent-excess count (`VisibleEntry.card_le_sum_silentExcess_sdiff_add_positiveDeficiency`)
and the two recorded-peel counting lemmas. The descent (`route8PeelingDescentRow`) enforces the
discipline with every peel recorded on the `ExactLedger`: while a visible excess load of a
collection piece is unpeeled, it is peeled through the exit-(4) witness supplied by
`K .route8VisibleExitFourRouting` (`lem:typeA-visible-entry` at the collection: exits
(1)–(3),(5),(6) are standing-invariant contradictions, (7) is excluded, so the witness is the
canonical (Q1) member at that load); otherwise the staged burden plus the census deficit give the
stage deficit, `exists_twoCarrierEntry_staged` produces the two-carrier entry, and a
target-defect entry is peeled (`PeelChain.cons`) or the true survivor goes to [124]
(`route8PeelingTerminalRow`). Exit (4) is a transient state, re-applied and recorded until the
stage closes (rate fails) or only route 8 remains. `K .route8PiecesClassified` states
`thm:branch-kill` exactly; the silent-first surrogate is `SilentClassification`
(`lem:typeA-silent-excess-count`'s hypothesis only) and `route8DeficitRow` is deleted.

**Live gate checklist.**

- [x] **Node [111] exact:** deterministic `route8GlobalSqueezeRow` only
- [x] **Exact branch-kill schema:** `Route8Deficit.PieceClassification` is the contrapositive of
  `thm:branch-kill` (a)/(b); no silent-first strengthening
- [x] **Staged burden proven:** `Route8Pressure.stage_burden`, no flat burden assumed
- [x] **Every peel recorded:** the descent's chain is ledger data; `StageRate` charges every
  recorded peel; visible peels carry their exit-(4) witnesses
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** all six vocabulary sites, including the new
  `route8VisibleExitFourRouting` (idx 338)
- [x] **No illegal carrier/API:** canonical `FactInputs.get`/`AtomicCT.run` rows only
- [ ] **Visible-routing producer:** `K .route8VisibleExitFourRouting`. The Holds is now the
  paper's exact per-port, peeling-parametric statement (`lem:typeA-unpeeled-visible-routing`: an
  overloaded port among unpeeled loads yields an exit-(4) witness at the current peeling whose
  load is one of its visible unpeeled returns); the descent row consumes it directly and is
  kernel-checked against it. The producer's exits-(1)/(2)/(3) arms use existing closures; the
  shared **response-realization theorem is now delivered**
  (`Graph/ResponseRealization.lean`: `declaredState` with registered profiles,
  `canonicalDeclaredState` with baseline inheritance and the descent ⟺ strict-shrinkage
  equivalence, `separationOfDeclared`/`switchReadingOfDeclared` for the germ schedule; builds
  green, not yet imported by consumers). The (5)/(6)/(7) arms need only its per-branch
  `shrinks` strictness witness (`def:proper-quotient-representative`, part of the exit's
  defining data) wired at the exit sites.
- [ ] **Unified-deficit producer:** `K .route8UnifiedDeficit`. **`lem:decorated-envelope-deficit-bound`
  is now proven** (`TypeBEnvelopeCharge.lean`: `decoratedEnvelopeDeficitBound`,
  `envelopeFamilyNegativePart_le`, `envelopeFamilyNegativePart_le_degreeSurplus`, with the
  `GroupedEnvelopes` glue in `DecoratedHandoffEnvelope.lean`); three of four piece cases were
  already derivable. The producer still needs, per handoff core, the `routes`/`unsaturated`
  hypotheses (`lem:typeB-postledger-core-hygiene` + `lem:typeA-receiver-loads` +
  `lem:typeA-unsaturated-discharge` read on the post-ledger remainder) and the fan-assignment
  coverage `Σ_X |A_X| ≤ Σ_h c(𝔉_h)` (`def:typeB-assigned-ledger`); no ledger key packages them
  yet.
- [ ] **Entry-census producer:** `K .route8UnifiedEntryCensus`. Locally provable: `select? =
  some basin` up to a D3 window-label cut-boundary lemma, the Q3↔alternative-(a) bridge and its
  exit-(4) witness, and α ≥ 2 on the minimal arm (delivered:
  `Route8.two_le_essentialCore_card_of_alternatives_refuted`, `Route8CarrierCore.lean`, builds).
  Blocked on the [116]-shared standing-invariant refutations of alternatives (b)/(c)/(d)
  (`cor:uncompressible`, `lem:proper-smearing`, `lem:no-silent-global-smearing`, and a
  `TraceSurvivingSeparator → HandoffProduced` bridge), and on `lem:typeA-unified-carriers`'s
  target-defect half (`lem:typeA-internal-quotient-mixed` routing). Q1/Q2/Q4/Q5 witnesses have
  no Lean bridge to the minimality alternatives.
- [x] **Stage restructure done:** the falsifiable invariant key `route8UnifiedStageRate` is
  deleted; `route8StageRateFailed` (idx 342) records the failed-stage arm;
  `route8StageOutcomeDichotomy` decides the terminal stage exactly as the manuscript's
  procedure does (survivor → [124]; failed rate → the branch-kill closure, Assembly frontier
  `selectedRouteEightStageClosure`); vocabulary builds, both [123] rows probe-elaborate. The
  descent itself now peels per port with every peel recorded (reduced-ledger machinery in
  `VisibleReceiverEntry.lean`: `visibleFirstOrderReduced`/`payableSetReduced`/
  `silentExcessReduced` + `silentExcessReduced_subset` + the reduced
  `lem:typeA-silent-excess-count`; `Route8Pressure.stage_burden` re-proven from them;
  `PeelChain.visible` records a visible unpeeled load) — all kernel-checked, descent row
  probe-elaborates. The failed-stage closure producer (`selectedRouteEightStageClosure`: the
  large-budget net-deficiency cap + `thm:branch-kill` at the failed stage) still needs a
  produced `route8PiecesClassified` and a branch-carried `netDeficiencyCap`.
- [ ] **Composed [123] wiring:** `selectedLargeBudgetPressureCensus` remains the loud frontier
  until the above are produced.
- [ ] **Worktree/HEAD reconciliation (user):** commit `2985ff8` ("Add part IX closure") contains
  a `Route8CarrierCore.lean` [124] no-go block plus `import ExitFourFamily` that now forms an
  import cycle against the worktree topology (`ExitFourFamily → Route8Census →
  Route8CarrierCore`); the worktree keeps the acyclic version.

**Exit criterion.** The framework theorems (response realization,
`lem:decorated-envelope-deficit-bound`) are proven and the descent/terminal architecture is the
manuscript's, kernel-checked end to end. [123] closes into [124] once four producers exist, each
a single-label sealed row on the literal incoming ledger: (1) `route8VisibleExitFourRouting`
(exits (1)–(3) closures + realization with its `shrinks` witness at (5)/(6)/(7)); (2)
`route8UnifiedDeficit` (three cases done in theorems; handoff cores need the hygiene facts
`lem:typeB-postledger-core-hygiene`/`lem:typeA-receiver-loads`/`lem:typeA-unsaturated-discharge`
and the `def:typeB-assigned-ledger` coverage packaged as ledger facts); (3)
`route8UnifiedEntryCensus` (locally provable parts + the [116]-shared standing-invariant
refutations, now unblocked in principle by `ResponseRealization`); (4)
`selectedRouteEightStageClosure` (`route8PiecesClassified` producer + branch-carried
`netDeficiencyCap` + the failed-stage arithmetic).

### Node [144] — bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Exact manuscript diagram output.** bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Manuscript rows.** Label set **L24** (paper page(s): 66, 67, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `sameTokenBottleneckRoutingRow`, run directly by
`selectedBottleneckDischarge` on the incoming `ExactLedger`.

**Current combinator / shared continuation.** The three residual-local `factOnly` class-audit
rows each publish their class audit and the shared `K .homogeneousBottleneckPattern`. The one
anonymous Type-A `factOnly` owner for this label requires that pattern together with
`K .activeSurplusDemands`, `K .sparseSurplusSurvivor`, and the inherited selection,
profile, context, replacement, and uncompressibility facts. Its literal manifest produces
`K .bottleneckRouting` and the survivor specialization `K .typeBHandoff`. The owner is loud
inside its proof, before either output can be committed.

**Primary defect class.** mathematical proof absent at
`lem:same-token-bottleneck-routing`: Lean does not yet obtain the paper-declared connector
configurations from the literal homogeneous pattern. The support now reads the canonical returns
already present in `K .activeSurplusDemands`; no return path is requested from the lemma in
isolation.

**Fresh audit diagnosis.** ❌ LOUD AT THE PAPER'S FIRST DECLARED-CONNECTOR STEP — Each of [140],
[142], and [143] correctly reads its concrete overload witness from the incoming `ExactLedger` and
publishes the manuscript's matching/star in the same token-role fibre. The subsequent Lean code had
diverged from the paper by choosing arbitrary shortest paths from whole-graph connectivity. Those
paths were not the active demands' `R_p` and their construction was circular.

The repaired `routingSupport` instead uses the literal upstream data: capacity-token carrier,
canonical blocker, `T(p)`, `T(q)`, the already canonical `R_p`, `R_q`, and `Γ(p)`, `Γ(q)`. The
two return entries are forced by the paper's own earlier active-demand definition and blocker type
(b): at an open port `Γ(p)=Q_p`, so the canonical return cannot be recovered from `Γ(p)`. No new
path is selected and no numerical datum is supplied. The extra presentation fields, global path
selector, callback label readers, collision/trichotomy wrappers, detached construction theorems,
`GermPair`/`RoutedBottleneck` carriers, invented semantic keys, and conditional handoff row are
deleted. `Parallel` also no longer accepts bare `¬ Diverges`: common-prefix entry is proved from
the configurations' actual landing facts when one finite configuration ends first.

The second source audit confirms why merely supplying `R_p,R_q` does not finish the proof.
`ActiveSurplusDemands` carries enough data to reconstruct each canonical return walk from a selected
endpoint to its centre. In contrast, the current `DeclaredCoordinateSignature` declaration exposes
only coordinate constructors, valued readings, and support unions. It does not construct the
paper-declared connector configuration from the primitive blocker support to a selected `T(p)`, nor
does it provide the graph-derived seven-coordinate routing-label reading. Consequently the existing
Lean declarations do not yet justify the first two objects chosen in the manuscript proof. This is
a mathematical formalization gap, not permission to add a caller-supplied selector or carrier.

The first remaining formula is therefore the manuscript's own one, not a request that the paper
justify the deleted strategy. In the compiled context containing concrete witnesses
`active`, `capacity`, `activationEq`, and `concretePattern`, the sole goal is
`SparseSurplusExit (MinimumDegreeAtLeast data.threshold)
(HasCycleWithLength data.LengthOK) data.LengthOK current.object ∨
SameTokenTypeBHandoffStatement data current.object`. From the concrete token `t`, role `r`, and
matching/star inside `concretePattern`, the proof must select two distinct equal-label edges and the
declared connector configurations belonging to their active-family supports, then follow the
paper's parallel/first-separator alternatives in order. On `K .sparseSurplusSurvivor`, the same
executor eliminates the first arm and publishes only the Type B arm. No whole-graph connectivity
path, extra support entry, caller-supplied bottleneck, undefined selector, or detached quotient
theorem is an admissible substitute.

**What must be implemented or corrected.**

- Complete the already registered mathematical `Holds` proposition, which now states the paper's
  concrete homogeneous-pattern package and exact sparse-exit-or-decorated-Type-B alternative. Do
  not restore a universal theorem about a separately supplied bottleneck.
- Finish the anonymous proof inside `sameTokenBottleneckRoutingRow`. It already reads only the
  literal pattern, survivor, and inherited paper facts through `FactInputs.get`; construct every
  temporary routing/quotient/envelope object locally and return the two exact declared outputs.
- Use `routingSupport` with the ledger's canonical `R_p,R_q`; never select a replacement path. The paper's
  parallel case must follow its attempted-quotient/context/compression/smearing/closed-
  representative alternatives, and the separated case must follow its cubic-switch and fan-safety
  alternatives in that order.
- Append the sparse-exit-or-Type-B fact and its survivor specialization
  with the literal `FactManifest` and `AtomicCT.run` on the same `ExactLedger`. Do not restore any
  helper theorem, callback, side carrier, path selector, or residual trichotomy.
- After that proof, the next loud obligation is downstream: the current node [65] schemas accept a
  canonical negative remainder component or the indexed [177] corridor datum, whereas [144]
  produces the paper's arbitrary connected remainder core with its admissible handoff envelope.
  Route that exact ledger fact through a same-token Type B lane; do not convert it into either
  stronger existing schema.

**Live gate checklist.**

- [ ] **Implemented / reachable:** the exact vocabulary builds, but the anonymous proof has the
  one displayed unsolved outcome
- [x] **Correctly wired:** the exact pattern reaches `sameTokenBottleneckRoutingRow` directly
- [x] **Residual-local proof:** the three class audits concern the literal active object
- [ ] **Correct ledger registration:** the literal two-key manifest is registered, but no routing
  or Type B result can be committed until the proof closes
- [x] **No invented path strategy:** the global path fields, two extra support entries, collision
  wrappers, undefined selector, detached carriers, and conditional row are deleted
- [ ] **Exact manuscript proof:** first absent at selection and reading of the declared connector
  configurations
- [x] **Independent kernel check:** `SameTokenRoutingGerms`, `ObjectCapacityLedger`, and
  `SpineVocabulary` build; the narrow row reports only the displayed unsolved disjunction, and
  searches find no obsolete routing carrier or fake producer

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [162] — dense hot/cold pass: run [22]--[24] and [145]--[157] on the dense residual; [23], [149], [155], [156], [157] close as before; bounded arm of [153] and [146]/[160] arms return to [25]

**Exact manuscript diagram output.** dense hot/cold pass: run [22]--[24] and [145]--[157] on the dense residual; [23], [149], [155], [156], [157] close as before; bounded arm of [153] and [146]/[160] arms return to [25]

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** the `.right` arm of `selectedNearCubicBranch` (Assembly.lean:4164+)

**Current combinator / shared continuation.** terminal closure, Decision.run, AtomicCT.run row; selectedNearCubicBranch.

**Primary defect class.** composed branch still reaches undefined downstream closures.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. The unconsumed hypothesis is the manuscript's own finding: `lem:dense-cold-pass`'s proof says the density sentence is not among the facts the pass uses. The larger residual is sound, and the pass is valid on it precisely because it never reads that sentence. Because [160] tests the supply bound, the residual entered is strictly larger than the manuscript's.

**What must be implemented or corrected.**

- Wire the pass through the repaired [159], [166], and [172] closures without merging sibling histories.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedDenseSameSizeCanonicalSwap`, `selectedDenseJointCodeOverflow`, `selectedBarrierOverlapSerialSystem`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass for the shared [22] substep: the dense ledger uses `selectedBarrierDichotomy` and receives exactly one cap/overflow key
- [x] **No illegal carrier/API:** pass for the shared [22] substep: the duplicate inline decision and extra variable-edge-budget fact are removed
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [ ] **Independent kernel check:** fail: NO: `selectedDenseSameSizeCanonicalSwap`, `selectedDenseJointCodeOverflow`, `selectedBarrierOverlapSerialSystem`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [165] — canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample

**Exact manuscript diagram output.** canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedCanonicalSwapCloses` (Assembly.lean:1481)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedCanonicalSwapCloses, selectedNearCubicBranch.

**Primary defect class.** wrong mathematical branch test or proof strategy.

**Fresh audit diagnosis.** ⚠ DIVERGENT — The manuscript's [165] is the same-size case, closed by refining node [4]'s order to (\|V\|,\|E\|,Φ). The Lean declaration closes the strictly-smaller-vertex-count case, which needs no refinement. The manuscript's actual step is the sibling `K .coldCanonicalSwapSameSize`, whose consumer `selectedDenseSameSizeCanonicalSwap` is an undefined frontier producer — the taint source at Assembly.lean:3493 and 4269. `K .coldCanonicalSwapSmaller` is unsatisfiable on constructed germs, so the decision always takes the frontier arm.

**What must be implemented or corrected.**

- Restore the paper's same-size swap case at this node. The existing strictly-smaller-vertex case is auxiliary and cannot replace the refined-minimality argument.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: DIVERGENT
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [166] — refined lexicographic minimality: \(Q=E\)

**Exact manuscript diagram output.** refined lexicographic minimality: \(Q=E\)

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedNearCubicBranch.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — Q = E appears only as a case assumption; the case the manuscript actually closes is punted to an undefined producer. Missing: a `lexicographicProgress` extended to (vertexCount, edgeCount, Φ). Graph/Progress.lean carries only the first two.

**What must be implemented or corrected.**

- Extend minimal-counterexample progress to `(vertexCount, edgeCount, Φ)`, where `Φ` is the multiset of canonical atom-piece ranks; prove the same-size canonical swap strictly decreases `Φ` and close `E ≠ Q`, leaving `Q = E` as the residual conclusion.
- Create the missing semantic key (including all six vocabulary registrations) and one
  permitted Type-A owner whose executor proves this exact output; do not stage it in a
  standalone theorem or application-local helper.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: no proposition established
- [ ] **Correctly wired:** fail: NO: `selectedDenseSameSizeCanonicalSwap`
- [x] **Residual-local proof:** N/A
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** fail: NO: `selectedDenseSameSizeCanonicalSwap`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [167] — symmetric strand pair: finite two-strand check on the closing lengths \(2\ell\), \(\ell+d\)

**Exact manuscript diagram output.** symmetric strand pair: finite two-strand check on the closing lengths \(2\ell\), \(\ell+d\)

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedNearCubicBranch.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — `TwoStrandEnumeration.lean` exists and is `decide`-checked but is imported only by the aggregate root; no Strategy file, no key, no Assembly declaration mentions it. The manuscript's `survivors 13 40` instantiation is performed nowhere. `coldWindowStubStructureRow`'s doc comment mis-labels itself node [167].

**What must be implemented or corrected.**

- Install and invoke the existing kernel `TwoStrandEnumeration` at the manuscript parameters `survivors 13 40`, publish its survivor classification, and compose it with [168] rather than treating the finite check alone as closure.
- Create the missing semantic key (including all six vocabulary registrations) and one
  permitted Type-A owner whose executor proves this exact output; do not stage it in a
  standalone theorem or application-local helper.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: no proposition established
- [ ] **Correctly wired:** fail: N/A
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** N/A N/A

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [168] — surviving pair attaches only at endpoints: not a selected interior half-edge

**Exact manuscript diagram output.** surviving pair attaches only at endpoints: not a selected interior half-edge

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `coldWindowStubStructureRow` (ColdCorridorRows.lean:731)

**Current combinator / shared continuation.** —; —.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — Faithful for the hypothesis half; neither of `lem:symmetric-pair-endpoint`'s conclusions is stated. Has a producer — the missing annotation is an annotation gap, not a coverage gap. The exclusion of symmetric pairs is asserted only in a prose comment.

**What must be implemented or corrected.**

- State both conclusions of `lem:symmetric-pair-endpoint`, including exclusion of selected interior half-edges, and derive them from the [167] survivor fact plus the active window-stub structure.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [170] — conditional savings additive at every fixed scale?

**Exact manuscript diagram output.** conditional savings additive at every fixed scale?

**Manuscript rows.** Label set **L27** (paper page(s): 125, 126, 128, 129); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `scaleAdditivityDichotomy` (BlockedCompressionRows.lean:34)

**Current combinator / shared continuation.** terminal closure; selectedScaleAdditivityDichotomy.

**Primary defect class.** wrong mathematical branch test or proof strategy.

**Fresh audit diagnosis.** ⚠ DIVERGENT — The second conjunct is [171]'s conclusion bundled into [170]'s decided proposition, so [171] is assumed rather than derived and the no arm fires when only that half fails. [172] is therefore entered under a strictly weaker hypothesis than `lem:barrier-failure-overlap` needs.

**What must be implemented or corrected.**

- Make the decision test only `lem:scale-additivity`. Do not bundle [171]'s compression conclusion into the yes arm; the no key must be exactly the hypothesis needed by `lem:barrier-failure-overlap`.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: `_blocked` bound and discarded
- [ ] **No illegal carrier/API:** partial: `_blocked` bound and discarded
- [ ] **Exact manuscript proof:** partial: DIVERGENT
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [171] — compression closure:\(\|\mathcal B(\mathcal P)\|<1\)

**Exact manuscript diagram output.** compression closure:\(\|\mathcal B(\mathcal P)\|<1\)

**Manuscript rows.** Label set **L27** (paper page(s): 125, 126, 128, 129); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `blockedClassCompressionCloses` (BlockedCompressionRows.lean:101)

**Current combinator / shared continuation.** terminal closure; selectedScaleAdditivityDichotomy.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — The arithmetic is the manuscript's \|𝓑(𝒫)\| < 1, but the compression inequality is read straight off `K .blockedScaleAdditive` rather than proved. Assembly.lean:3336–3339 names `selectedBlockedBarrierCodeInjectivity` and `selectedBlockedBarrierBaseline` as the carrying producers; neither exists in the sources, and neither is on the 14-item list.

**What must be implemented or corrected.**

- Prove the blocked-code injectivity and uncompressed baseline inside the executor, then derive the compression inequality and `|𝓑(𝓟)| < 1`; do not read the desired inequality straight from the [170] key.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [x] **Independent kernel check:** pass: YES for the producer; the arm reaches `selectedDenseJointCodeOverflow`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [172] — fixed-scale overlap system: serial realization and increment arithmetic close

**Exact manuscript diagram output.** fixed-scale overlap system: serial realization and increment arithmetic close

**Manuscript rows.** Label set **L27** (paper page(s): 125, 126, 128, 129); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** —; —.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — Discharged by an undefined producer. `SerialSystemArithmetic.lean` is imported only by the aggregate root; `BarrierOverlapSystem.lean` defines no obstruction and no uncrossing. Even a future producer cannot use `K .blockedBarrierOverlap` as-is: it is ¬(A ∧ B) where the lemma needs ¬A.

**What must be implemented or corrected.**

- Implement the minimal connected barrier-overlap obstruction, the serial window system, all five realizability/uncrossing clauses via `cutStateRepresentative`, and instantiate the existing spectrum arithmetic to obtain the paper's closure/routing alternatives.
- Create the missing semantic key (including all six vocabulary registrations) and one
  permitted Type-A owner whose executor proves this exact output; do not stage it in a
  standalone theorem or application-local helper.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: no proposition established
- [ ] **Correctly wired:** fail: NO: `selectedBarrierOverlapSerialSystem`
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** fail: NO: `selectedBarrierOverlapSerialSystem`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [174] — absorbed-configuration residual: the exact collision fails and the selected cold corridors were charged to high-degree vertices

**Exact manuscript diagram output.** absorbed-configuration residual: the exact collision fails and the selected cold corridors were charged to high-degree vertices

**Manuscript rows.** Label set **L28** (paper page(s): 124, 125); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `exactCollisionDichotomy` (SpineRows.lean:2360), `.inr` arm

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedNetChargeContinuation.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — Exactly ¬`K .netChargeCap`. The C lower bound and the bounded-arm placement are derived nowhere; nothing connects the collision failure to the cold family.

**What must be implemented or corrected.**

- Publish the full absorbed residual: collision failure, the required lower bound, bounded-arm placement, and the charge of selected cold corridors to high-degree vertices. Bare `¬ netChargeCap` is insufficient.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [175] — selected corridor meets a high-degree vertex?

**Exact manuscript diagram output.** selected corridor meets a high-degree vertex?

**Manuscript rows.** Label set **L28** (paper page(s): 124, 125); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `absorbedGermDichotomy` (ColdCorridorRows.lean:524)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedAbsorbedGermResidual.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — The manuscript's [175] is a per-half-edge dichotomy; Lean decides one global question, so on a mixed residual the heavy-centre half-edges are never routed to Type B. Vacuity risk: if the ambient-cubic cold family is empty the no arm is vacuously true.

**What must be implemented or corrected.**

- Replace the global all-or-none question with the manuscript's per-selected-half-edge dichotomy so mixed residuals send heavy-centre incidences to Type B and cubic incidences to the graph-realized branch.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [176] — graph-realized (F5) configuration: closed by [154]--[157], [165]--[168]

**Exact manuscript diagram output.** graph-realized (F5) configuration: closed by [154]--[157], [165]--[168]

**Manuscript rows.** Label set **L28** (paper page(s): 124, 125); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `absorbedGermDichotomy` (ColdCorridorRows.lean:524), `.inl` arm

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedAbsorbedGermResidual.

**Primary defect class.** fact absent from or not wired into the literal branch ancestry.

**Fresh audit diagnosis.** ✅ FAITHFUL-TRIVIAL — The closure is performed in the arm's continuation by precisely the six lemmas the manuscript names, ending in the published `K .coldBranchClosed`. The earlier pass read only the `Decision`'s produced key. Do not read the “closed by [154]–[157], [165]–[168]” annotation as evidence of closure.

**What must be implemented or corrected.**

- Wire the graph-realized arm through the repaired [165]–[168] chain and publish `.coldBranchClosed`; remove `selectedAbsorbedGermBlockedResidual` only after the exact blocked residual is consumed.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedDenseSameSizeCanonicalSwap` and `selectedAbsorbedGermBlockedResidual`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL-TRIVIAL
- [ ] **Independent kernel check:** fail: NO: `selectedDenseSameSizeCanonicalSwap` and `selectedAbsorbedGermBlockedResidual`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.


### Node [178] — pair-code unrealized residual: the entropy count of [131] or of the free side of [137] fails; \cref{lem:pair-failure-overlap} gives a minimal pair overlap obstruction

**Exact manuscript diagram output.** pair-code unrealized residual: the entropy count of [131] or of the free side of [137] fails; \cref{lem:pair-failure-overlap} gives a minimal pair overlap obstruction

**Manuscript rows.** Label set **L29** (paper page(s): 87, 88, 89, 90); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `freePairEntropyDichotomy` (HomogeneousBottleneckRows.lean:510); `blockedPairEntropyDichotomy` (:584)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedStrictSurplusBranch.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — Only the bare negation of the two sandwich statements. `lem:pair-failure-overlap`'s minimal pair overlap obstruction is absent; no key for it exists.

**What must be implemented or corrected.**

- From each exact pair-entropy failure, construct and publish the minimal pair-overlap obstruction. The bare negation keys and discarded prerequisites are not `lem:pair-failure-overlap`.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedSparsePairSerialSystem`
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: both dichotomies bind and discard a required fact
- [ ] **No illegal carrier/API:** partial: both dichotomies bind and discard a required fact
- [ ] **Exact manuscript proof:** partial: WEAKER
- [ ] **Independent kernel check:** fail: NO: `selectedSparsePairSerialSystem`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [179] — serial demand system: uncrossing yields a scale-spanning chain of interfaces with bounded system increments (\cref{lem:pair-system-realizability})

**Exact manuscript diagram output.** serial demand system: uncrossing yields a scale-spanning chain of interfaces with bounded system increments (\cref{lem:pair-system-realizability})

**Manuscript rows.** Label set **L29** (paper page(s): 87, 88, 89, 90); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** —; —.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — No key, no row, no `Produces` manifest mentions a pair serial system. `SerialSystem.Spectrum` is deliberately graph-free and never instantiated. Entirely unimplemented. D_sp and ℓ_ret appear nowhere.

**What must be implemented or corrected.**

- Uncross the pair obstruction into a scale-spanning serial demand system with the manuscript's bounded increments `D_sp` and return length `ℓ_ret`, then publish that system on the same branch ledger.
- Create the missing semantic key (including all six vocabulary registrations) and one
  permitted Type-A owner whose executor proves this exact output; do not stage it in a
  standalone theorem or application-local helper.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: no proposition established
- [ ] **Correctly wired:** fail: NO: `selectedSparsePairSerialSystem`
- [x] **Residual-local proof:** N/A
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** fail: NO: `selectedSparsePairSerialSystem`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [180] — pair increment arithmetic closes: power-of-two hit, or periodic response class routed to a sparse exit or Type B (\cref{lem:pair-system-increment-arithmetic})

**Exact manuscript diagram output.** pair increment arithmetic closes: power-of-two hit, or periodic response class routed to a sparse exit or Type B (\cref{lem:pair-system-increment-arithmetic})

**Manuscript rows.** Label set **L29** (paper page(s): 87, 88, 89, 90); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** —; —.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — The ℕ arithmetic core `Spectrum.exists_pow_realized` is proved, but no `Spectrum` is ever constructed from a graph, `ScaleSpanning` is never discharged, and `S.Realized` is never connected to the target. Do not mistake `SerialSystemArithmetic.lean`'s docstring, which names [172] and [180], for coverage.

**What must be implemented or corrected.**

- Instantiate `Spectrum.exists_pow_realized` on the graph-derived system, connect `System.Realized` to `HasCycleWithLength`, and implement the periodic-response alternative routing to the named sparse exits or Type B.
- Create the missing semantic key (including all six vocabulary registrations) and one
  permitted Type-A owner whose executor proves this exact output; do not stage it in a
  standalone theorem or application-local helper.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: no proposition established
- [ ] **Correctly wired:** fail: NO: `selectedSparsePairSerialSystem`
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** fail: NO: `selectedSparsePairSerialSystem`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

## 6. Validation contract for this ledger

After any node repair:

1. Run `audit_tables.py check --repo-root .`; it must pass with exactly 322 manuscript rows and
   node rows [1]–[180].
2. Run `api_catalog.py check --repo-root .`; any nonzero result must be reproduced in the affected
   node section and both audit rows. Never refresh the allowlist merely to admit the implementation.
3. Build the canonical ExactLedger/manifest/execution targets and all positive and negative fixtures
   listed by the `eg-proof-expansion` workflow.
4. Elaborate the narrow EG owner, then the composed Assembly/StrategyDag target. Record the first
   exact unresolved proposition or unexpected identifier; do not summarize it as a node range.
5. Regenerate the sealed audit and require complete unique fact accounting, nonempty commits, the
   literal predecessor, correct produced keys, correct terminal status, and no sibling-history merge.
6. Recompute the strict failed-node set. It must equal the headings in this file exactly; verified
   nodes receive no prose section.

A fully compliant implementation is reached only when this section set is empty, the public theorem
is produced by the sealed `strategyDag`, the API and table checks pass, and the only remaining axioms
are the explicitly registered external mathematical inputs accepted by the manuscript.

## Appendix A. Manuscript-label sets

These sets name every paper-fact audit row corresponding to the node sections above. Pages and
live implementation/status cells remain in `Assembly_node_audit.md`; a node repair must update all
rows in its set that the repaired fact changes.

### L03 — node(s) [18]

`lem:labels`.

### L04 — node(s) [22], [23]

`lem:p13-window-package`, `prop:p13-density`.

### L08 — node(s) [43], [45]

`def:admissible-rank-quotient`, `def:closed-quotient-representative`, `def:declared-coordinate-signature`, `def:exact-response-profile`, `def:proper-quotient-representative`, `lem:no-silent-global-smearing`.

### L09 — node(s) [44]

`lem:smearing-support-repair`.

### L10 — node(s) [54]

`def:Theta`, `prop:entropy-high-theta`, `prop:two-budget`.

### L12 — node(s) [65], [66], [68], [69], [70], [71], [72], [73], [74], [77], [80], [81], [82], [84]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`.

### L13 — node(s) [67]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:deletion-critical`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`.

### L14 — node(s) [76], [85]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`, `thm:branch-kill`.

### L15 — node(s) [104]

`def:typeA-carrier-deletion-witness`, `def:typeA-channel-spectrum`, `def:typeA-continuation-classes`, `def:typeA-excess-basin`, `def:typeA-exit4-peeling`, `def:typeA-large-budget-deficit`, `def:typeA-receiver-load`, `def:typeA-route8-carriers`, `def:typeA-saturated-exits`, `def:typeA-silent-core-residual`, `def:typeA-support`, `def:typeA-terminal-two-carrier`, `def:typeA-trace-basin`, `def:typeA-visible-load`, `def:typeB-assigned-ledger`, `lem:decorated-envelope-no-double-count`, `lem:density-mersenne`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-common-port-return-cycle`, `lem:typeA-continuation-routing`, `lem:typeA-cubic-switch-absorption`, `lem:typeA-deletion-witness-declared`, `lem:typeA-entry-budget`, `lem:typeA-essential-deletion-witness`, `lem:typeA-exclusion`, `lem:typeA-exit4-discharge`, `lem:typeA-exit4-peeling-charge`, `lem:typeA-exit4-residual-routing`, `lem:typeA-exits-discharged`, `lem:typeA-first-entry`, `lem:typeA-high-degree-handoff`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-port-return`, `lem:typeA-receiver-loads`, `lem:typeA-reduced-silent-residual`, `lem:typeA-route8-burden`, `lem:typeA-saturated-handoff`, `lem:typeA-silent-excess`, `lem:typeA-silent-excess-count`, `lem:typeA-spectral-pressure`, `lem:typeA-threshold-algebra`, `lem:typeA-two-carrier-deletion-canonical`, `lem:typeA-unpeeled-silent-routing`, `lem:typeA-unpeeled-visible-routing`, `lem:typeA-unsaturated-discharge`, `lem:typeA-visible-entry`, `lem:window-handoff-center-accounting`, `prop:typeA-route8-closure-from-nogo`, `thm:typeA-two-carrier-nogo`.

### L16 — node(s) [113], [114], [115], [116], [117], [118], [124]

`cor:typeA-large-budget-closure-open-pressure`, `def:typeA-carrier-deletion-witness`, `def:typeA-exit4-family`, `def:typeA-large-budget-deficit`, `def:typeA-route8-carriers`, `def:typeA-terminal-two-carrier`, `def:typeA-true-route8-residual`, `def:typeB-assigned-ledger`, `lem:app-dense-window-closure`, `lem:app-global-smearing-closure`, `lem:app-typeA-quiet-bound`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-deletion-witness-declared`, `lem:typeA-essential-deletion-witness`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-route8-burden`, `lem:typeA-two-carrier-deletion-canonical`, `prop:typeA-route8-carrier-reduction`, `prop:typeA-route8-closure-from-nogo`, `thm:large-budget-route8-only`, `thm:typeA-two-carrier-nogo`.

### L17 — node(s) [123]

`cor:typeA-large-budget-closure-open-pressure`, `def:typeA-actual-profile-pressure-defects`, `def:typeA-carrier-deletion-witness`, `def:typeA-exit4-family`, `def:typeA-exit4-pressure-token`, `def:typeA-large-budget-deficit`, `def:typeA-open-window-blocker`, `def:typeA-peeling-reduced-ledger`, `def:typeA-pressure-absorbers`, `def:typeA-pressure-ledger`, `def:typeA-primitive-window-overload-excess`, `def:typeA-recorded-window-shadow-hit`, `def:typeA-route8-carriers`, `def:typeA-same-window-open-blocker-cap`, `def:typeA-same-window-overload-triple`, `def:typeA-terminal-two-carrier`, `def:typeA-true-route8-residual`, `def:typeA-two-terminal-pressure-records`, `def:typeA-unified-entries`, `def:typeA-unified-negative`, `def:typeA-window-attachment-shadow`, `def:typeA-zero-shadow-primitive-excess`, `def:typeB-assigned-ledger`, `lem:app-dense-window-closure`, `lem:app-global-smearing-closure`, `lem:app-typeA-quiet-bound`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-deletion-witness-declared`, `lem:typeA-essential-deletion-witness`, `lem:typeA-exit4-finite-descent`, `lem:typeA-final-open-pressure-exhaustion`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-open-pressure-zero-shadow-excess`, `lem:typeA-open-window-blocker-count`, `lem:typeA-peeling-reduced-reduction`, `lem:typeA-pressure-absorber-no-overcount`, `lem:typeA-pressure-defect-split`, `lem:typeA-pressure-is-exit4-peel`, `lem:typeA-pressure-ledger-no-overcount`, `lem:typeA-pressure-records-canonical`, `lem:typeA-pressure-token-two-carriers`, `lem:typeA-primitive-excess-zero-shadow`, `lem:typeA-profile-pressure-dependence-routing`, `lem:typeA-route8-burden`, `lem:typeA-routed-overload-not-open`, `lem:typeA-same-window-cap-overload-excess`, `lem:typeA-singleton-shadow-table`, `lem:typeA-two-carrier-deletion-canonical`, `lem:typeA-unified-burden`, `lem:typeA-unified-carriers`, `lem:typeA-unified-deficit`, `lem:typeA-window-blocker-accounting-audit`, `lem:typeA-window-blocker-numerics`, `lem:typeA-window-shadow-hit-routes`, `prop:typeA-exit4-closure-from-open-pressure`, `prop:typeA-exit4-closure-from-window-blockers`, `prop:typeA-exit4-closure-from-zero-shadow`, `prop:typeA-external-pressure-criterion`, `prop:typeA-external-pressure-reduction`, `prop:typeA-route8-carrier-reduction`, `prop:typeA-route8-closure-from-nogo`, `prop:typeA-unified-reduction`, `thm:large-budget-route8-only`, `thm:typeA-two-carrier-nogo`.

### L24 — node(s) [144]

`cor:forced-homogeneous-same-token-scale`, `cor:homogeneous-same-token-caps-close`, `def:same-token-routing-germs`, `lem:same-token-bottleneck-routing`, `thm:homogeneous-overload-geometric-closure`, `thm:sharp-surplus-overload-audit`.

### L25 — node(s) [147], [154], [156], [157]

`def:cold-bounded-germ`, `def:cold-corridor-first-failure`, `def:cold-same-interface-table`, `def:cold-skeleton-excess`, `def:cold-window-ledger`, `def:surviving-cold-branch`, `lem:cold-bounded-germ-trichotomy`, `lem:cold-corridor-first-failure`, `lem:cold-germ-extraction`, `lem:cold-increment-arithmetic`, `lem:cold-same-interface-table`, `lem:cold-short-self-return-filter`, `lem:cold-window-stub-excess`, `lem:hot-failure-cold-mass`, `thm:cold-branch-quantitative-closure`.

### L26 — node(s) [159], [162], [163], [165], [166], [167], [168]

`def:all-cold-comparison`, `def:neutral-equal-length-germ`, `def:window-realization-test`, `lem:dense-cold-pass`, `lem:dense-deficiency-routing`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, `lem:remainder-glue-injection`, `lem:symmetric-pair-endpoint`, `lem:two-strand-check`.

### L27 — node(s) [170], [171], [172]

`def:barrier-overlap-system`, `def:blocked-class`, `def:serial-window-system`, `lem:barrier-failure-overlap`, `lem:blocked-graphs-compress`, `lem:scale-additivity`, `lem:serial-system-sumset`, `lem:system-increment-arithmetic`, `lem:window-system-realizability`.

### L28 — node(s) [174], [175], [176], [177]

`lem:absorbed-germ-fan-data`, `lem:exact-collision-test`.

### L29 — node(s) [178], [179], [180]

`cor:spine-lower-bound-surplus-estimates`, `def:pair-overlap-system`, `def:spine-lower-bound-deficits`, `lem:pair-count-or-arithmetic`, `lem:pair-failure-overlap`, `lem:pair-system-increment-arithmetic`, `lem:pair-system-realizability`.
