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
- Nodes passing every strict gate: **157**.
- Nodes retained in this ledger: **23**.
- Axiom-audit declarations: **75** = **49 clean** + **26 tainted**; unreported: **0**.
- Loud undefined frontier producers: **12**.

### Loud frontier producers

- `selectedAbsorbedGermBlockedResidual`
- `selectedAbsorbedTypeBFanHeavyContinuation`
- `selectedAbsorbedTypeBFanDegreeFourContinuation`
- `selectedBarrierOverlapSerialSystem`
- `selectedDenseJointCodeOverflow`
- `selectedDenseSameSizeCanonicalSwap`
- `selectedLargeBudgetPressureCensus`
- `selectedRouteEightBudgetEdge`
- `selectedRouteEightUnclassifiedPiece`
- `selectedSparsePairSerialSystem`
- `selectedTypeAVisibleRouteEightImpossible`
- `selectedPatternRoutedBottleneck`

### Cross-cutting framework blockers

- `StrategyDag.lean` contains only presentation-equality examples and no final `strategyDag`; the
  package root still imports the application-local `Assembly.lean`. Full closure therefore lacks
  the sealed topology endpoint required by the framework.
- The common Type B path now retains the raw `[177]` witness through `[72]`/`[81]`, keeps a
  successful indexed B2 entry on `[74]`/`[82]`, and sends only an actual minimal obstruction to
  `[84]`, always on the same monotone `ExactLedger`. The default `SpineRows` check reaches those
  owners and then hits the already retained route-8 `[111]` heartbeat boundary; an uncapped check
  exposes the corresponding later route-8 typing mismatch at lines 5961--5970. This prevents the
  compiled API export but is not a new Type B node or a new remediation section.

### Exact section set

[104], [111], [129], [144], [154], [156], [157], [159], [162], [163], [165], [166], [167], [168], [170], [171], [172], [174], [175], [176], [178], [179], [180].

## 4. Dependency-ordered repair route

1. **Type A and route 8:** repair [104] and route the exact unclassified-census arm at [111].
   The classified route-8 chain [115]–[124] is now kernel-checked on its literal ledgers.
2. **Sparse-surplus accounting:** resolve the manuscript-level missing producer at [129] and the
   missing same-token routing-germ construction at [144]. Nodes [131]–[143], the direct [145]
   handoff, and [147]'s rate conversion now use the literal monotone `ExactLedger` path.
3. **Cold/dense branch:** repair [154], [156], [157], [159], [162]–[172], and [174]–[176].
4. **Pair serial closure:** construct the exact obstruction/system/arithmetic chain [178]–[180].
5. **Sealed endpoint:** only after every node owner is green, express the final topology in
   `StrategyDag.lean`, switch the package root to it, and regenerate the sealed report.

The ordering is diagnostic; it does not authorize a multi-node implementation change. A repair
still stops at its first downstream failure and updates only that label's two audit rows.

## 5. Node-by-node remediation checklists

### Node [104] — uncompressibility contradiction

**Exact manuscript diagram output.** uncompressibility contradiction

**Manuscript rows.** Label set **L15** (paper page(s): 154, 155, 156, 157, 158, 159, 160, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177, 178, 179, 180, 182, 183, 185); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `typeAExitFiveClosed` (TypeAExitRun.lean:282)

**Current combinator / shared continuation.** canonical `Incompatible` terminal; selectedTypeAExitFiveToSeven, selectedTypeAExitFiveToSevenSilent.

**Primary defect class.** mathematical proof absent.

**Fresh audit diagnosis.** ❌ MATHEMATICAL PROOF ABSENT — Node [103] publishes the exact selected-load/trace-basin response quotient and its proper-realization versus trace-response-only cases. A focused kernel probe proves the strongest two consequences assigned by the manuscript: the proper arm constructs `CompressibleSupport ... object basin`, while the response-only arm proves `¬ TargetCompleteMinimal ... basin` and, using the selected-basin equality, `¬ Route8Entry ... load`. The literal [104] ledger supplies hereditary uncompressibility but no route-8-minimality premise. Consequently the first consequence contradicts `K .uncompressible`, whereas the second is only the manuscript's “not an admissible route-8 residual” and does not inhabit the `False` required by the diagram's canonical contradiction terminal.

**What must be implemented or corrected.**

- Preserve the kernel-checked proper-arm conversion: from the selected basin's connected/proper/baseline/smaller realization, construct the exact same-basin `CompressibleSupport` and contradict inherited hereditary uncompressibility.
- Preserve the kernel-checked response-only consequence: failure alternative (b) gives `¬ TargetCompleteMinimal ... basin` and therefore `¬ Route8Entry ... load` for the same selected basin.
- The manuscript must supply a logically valid terminal continuation for that response-only consequence before [104] can be closed. Adding route-8 minimality on a branch tested before route 8, strengthening `cor:uncompressible` to forbid abstract response quotients, or treating non-admissibility as a `False` closure is not authorized by the current paper and must not be introduced in Lean.
- Preserve the exact selected packing, component, receiver, peeling set, eligible load, basin, retained coordinate family, and response quotient in any manuscript-approved correction.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: the response-only case has no paper-supplied `False`
- [ ] **Correctly wired:** fail: the [103]-yes edge requires a contradiction terminal, but the exact second case only excludes route 8
- [x] **Residual-local proof:** pass: both focused consequences are at the literal [103]-yes data
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** fail: the manuscript gives no contradiction after its response-only conclusion
- [ ] **Independent kernel check:** fail for the terminal; pass for a focused probe of the exact `CompressibleSupport ∨ ¬ TargetCompleteMinimal` and `¬ Route8Entry` consequences

**Exit criterion.** Obtain a manuscript-authorized proposition or continuation that turns the
response-only alternative into the diagram's terminal behavior without strengthening an incoming
fact or changing the exit order; then implement it through the literal ledger, update both live
rows from the compiled term, and remove this section only when all seven boxes are checked.

### Node [111] — global squeeze and unified route-8 census classification

**Exact manuscript diagram output.** The negative zero-surplus Type A pieces form the canonical
route-8 collection \(\mathcal X_A\); on the unified correction, every negative piece belongs
extensionally to \(\widetilde\Xi\) and is classified either as a target-complete-minimal route-8
entry or as the prescribed target-defect alternative.

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180,
181, 182, 183, 185, 233, 234, 250, 251); its complete label list is in Appendix A. The
corresponding live row cells are in the paper-fact implementation table; their exact environments
supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8GlobalSqueezeRow` (SpineRows.lean:5076);
`route8PieceClassificationDichotomy` (SpineRows.lean:5802).

**Current combinator / shared continuation.** Canonical `factOnly`/`AtomicCT.run` for the pure
collection and `Decision.run`/`ExactLedger.get` for the unified classification;
`selectedRouteEightResidual` and shared `selectedRouteEightCensus`.

**Primary defect class.** Exact census complement not yet routed.

**Fresh audit diagnosis.** ⚠ PARTIAL — The pure [111] owner is exact and kernel-checked:
it extracts precisely the negative zero-surplus canonical Type A pieces satisfying
`Route8Survives`, publishes their support image, and records the cleared deficit. The unified
correction is also stated exactly as `Route8UnifiedCensusFacts`: extensional membership in
\(\widetilde\Xi\), the ordered route-8/target-defect entry alternatives, and the rate invariant
for every surviving peel stage are all part of the ledger fact. Its classified arm runs the
paper's [113], [123], and [124] chain to contradiction. The complementary decision arm remains
intentionally loud at `selectedRouteEightUnclassifiedPiece`; no false proof or surrogate routing
has been inserted.

**What must be implemented or corrected.**

- Consume the exact `K .route8UnclassifiedPiece` witness from its incoming `ExactLedger` and
  route the exhibited piece according to the paper's branch-kill alternatives: visible-first
  Type A material must enter its prescribed Type A continuation, and a non-bridge Type B piece
  must enter the prescribed Type B continuation.
- Preserve the full incoming ledger and append every fact proved by that routing under its
  canonical semantic key. Do not replace the extensional census equality, entry alternatives,
  or surviving-stage invariant by a weaker disjunction.
- Do not add an application-local carrier, callback, alternate history, detached helper theorem,
  or axiom. Temporary witnesses must remain local to the sealed executor, and all reusable facts
  must be read from and written to the canonical `ExactLedger`.

**Live gate checklist.**

- [ ] **Implemented / reachable:** partial: the exact classified arm is complete; the
  unclassified arm has no producer
- [ ] **Correctly wired:** fail: `selectedRouteEightUnclassifiedPiece`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript statement:** pass
- [ ] **Independent kernel check:** the owners and classified branch pass; composed Assembly
  intentionally stops at `selectedRouteEightUnclassifiedPiece`

**Exit criterion.** Implement the paper-prescribed routing of the exact unclassified-piece
witness on the literal incoming ledger, prove both resulting continuations kernel-check, update
both live audit rows from that compiled term, and remove this section only when all seven boxes
are green.

### Node [129] — full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)

**Exact manuscript diagram output.** full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)

**Manuscript rows.** Label set **L18** (paper page(s): 59, 60, 83, 84); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** No application owner. `Holds .baselineSpineDemand` states the exact
required proposition, and `isBaselineSpineDemand_of_package` is the reusable arithmetic theorem;
`selectedStrictSurplusBranch` stops loudly at the deliberately undefined
`selectedBaselineSpineDemand`.

**Current combinator / shared continuation.** Missing `factOnly`/`AtomicCT.run` producer;
`selectedStrictSurplusBranch` is the first consumer.

**Primary defect class.** exact mathematical producer absent.

**Fresh audit diagnosis.** ❌ LOUD SOURCE GAP — The fabricated empty-support coordinate family,
its zero-deficit proof, the legacy row, and its wrapper have been removed. Lean now states only
the manuscript's required active family and baseline-spine demand. A source audit found that
`def:baseline-spine-demand` only defines this package and every sparse theorem assumes that the
active object admits one; no preceding manuscript lemma constructs a target-testable `𝓘_spine`
or proves `E_spine ≤ C_E n` on the strict branch. The selected sparse continuation therefore keeps
the exact producer undefined instead of feeding chosen zero data to [131]–[138].

**What must be implemented or corrected.**

- Supply a new paper lemma, or identify a currently missing source lemma, that constructs on this
  literal residual a type `Coordinate`, a finite `family : Finset Coordinate`, and
  `coordinateSupport : Coordinate → Finset object.Vertex`, while retaining
  `𝓐₀ = 𝓟_exc`.
- Its complete target is: every `DeclaredQuotient` on that family whose rank quotient is
  `FunctionalOn ↑family` is `LabelInjectiveOn ↑family`, and
  `cubicBaselineBudget n threshold ≤ 2^(family.card + spineDeficit n threshold family.card)`
  together with
  `spineDeficit n threshold family.card ≤ data.surplusScale * n`. The current paper defines and
  assumes this package but does not prove this implication, so Lean must not obtain it by choosing
  an empty family, selecting a deficit, or using a detached carrier.
- Publish the complete value under `K .baselineSpineDemand` with one residual-local `factOnly`
  row that reads all prerequisites through `inputs.get` and is run with `AtomicCT.run`.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: `selectedBaselineSpineDemand` is intentionally undefined
- [ ] **Correctly wired:** fail at the exact missing producer before [130]
- [ ] **Residual-local proof:** no application proof exists
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** pass: the fabricated family/row/wrapper were removed
- [ ] **Exact manuscript proof:** fail: the manuscript assumes, but does not prove, the
  package-to-demand construction
- [ ] **Independent kernel check:** the proposition and generic arithmetic theorem build; the
  selected call is deliberately undefined, while full Assembly import currently stops earlier at
  the separately audited [71]/[80] error

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [144] — bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Exact manuscript diagram output.** bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Manuscript rows.** Label set **L24** (paper page(s): 66, 67, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedBottleneckDischarge` (Assembly.lean:406)

**Current combinator / shared continuation.** Three residual-local `factOnly` audit rows,
each publishing its class-specific audit and the shared `K .homogeneousBottleneckPattern`
atomically; `selectedSparsePressureOverloadCloses` and `selectedBottleneckDischarge`.

**Primary defect class.** exact mathematical producer absent.

**Fresh audit diagnosis.** ❌ LOUD PAPER GAP AFTER AN EXACT PREFIX — Each of [140], [142], and
[143] reads its concrete class-specific overload witness from the incoming `ExactLedger`, derives
the manuscript's matching/star pattern in that same token-role fibre, and atomically publishes both
its audit key and `K .homogeneousBottleneckPattern`. The former [144] implementation did not then
construct the paper's two routing germs and first separator: `CapacityPresentation` supplied those
facts through callback fields, so the alleged `RoutedBottleneck` was assumed rather than proved.
Those callbacks, the fabricated canonical presentation, the routing row, the Type B handoff row,
and both downstream surrogate continuations have been removed. `selectedBottleneckDischarge` now
stops loudly at `selectedPatternRoutedBottleneck`, the first missing manuscript fact.

**What must be implemented or corrected.**

- For every concrete `CapacityPresentation`, `ObjectCapacityLedger`, token `t` in its token set,
  role `r`, and `L_geom` matching or star inside `roleFibre t r`, select two distinct pattern edges
  and two distinct selected demands whose *actual* routing labels agree.
- From the capacity token, the canonical blockers of those two pairs, and their selected and
  response supports, construct two declared connector configurations beginning at the relevant
  primitive blocker anchor and ending in the prescribed selected supports. The construction must
  retain the concrete paths, endpoint labels, boundary profiles, window labels, and suppressed
  chord flag used in the paper's pigeonhole step.
- Prove the exact parallel/first-separator alternative. Parallel configurations must produce an
  actual constructor of `SparseSurplusExit`; separated configurations must supply the first
  separator, switch support and switch reading needed for a concrete `RoutedBottleneck`. Applying
  its exhaustive outcome must then produce the absorbed sparse-exit case or an admissible decorated
  Type B envelope. Do not put any of these facts in a presentation callback.
- Publish every newly proved routing fact under its canonical semantic key with one or more
  `factOnly`/`AtomicCT.run` rows on the literal predecessor; pass the accumulated `ExactLedger`
  forward without reconstructing a cursor or merging sibling histories.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [ ] **Implemented / reachable:** fail: `selectedPatternRoutedBottleneck` is intentionally undefined
- [ ] **Correctly wired:** fail at the exact missing routing-germ producer
- [x] **Residual-local proof:** pass through the three concrete class audits
- [x] **Correct ledger registration:** pass through `K .homogeneousBottleneckPattern`
- [x] **No illegal carrier/API:** pass: the callback fields and fabricated presentation were removed
- [ ] **Exact manuscript proof:** fail: the routing-germ and first-separator construction is absent
- [ ] **Independent kernel check:** the exact prefix builds and the selected call remains
  deliberately undefined; full Assembly import currently stops earlier at [71]/[80]

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [154] — bounded configuration case?

**Exact manuscript diagram output.** bounded configuration case?

**Manuscript rows.** Label set **L25** (paper page(s): 111, 112, 113, 114, 115, 116, 117, 118, 120); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedColdGermTrichotomy` (Assembly.lean:1072); `coldGermTrichotomyRow` (ColdCorridorRows.lean:630)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedColdGermTrichotomy, selectedNearCubicBranch.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL-TRIVIAL — The manuscript's exhaustiveness argument is “G3 is the complement”, asserted in one sentence with no supporting work. Requires only `K .selection` and `K .uncompressible`; nothing ties it to the [153] extracted family.

**What must be implemented or corrected.**

- Tie the bounded-configuration trichotomy to the family extracted at [153]; the current object-wide complement must not be provable without that active residual fact.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** partial: PARTIAL
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL-TRIVIAL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [156] — G2: target defect, exit (4), or handoff

**Exact manuscript diagram output.** G2: target defect, exit (4), or handoff

**Manuscript rows.** Label set **L25** (paper page(s): 111, 112, 113, 114, 115, 116, 117, 118, 120); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `coldGermTrichotomyRow` (ColdCorridorRows.lean:630), keys `.coldGermDistinguished`, `.coldGermRouted`

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedColdGermTrichotomy, selectedNearCubicBranch.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. “Exit (4), or handoff” is the name of the ledger the defect lands in, already excluded by `def:surviving-cold-branch`. The sign guard matches the manuscript's own orientation convention and is what the G3 descent needs. Vacuously true on everything the branch constructs. “exit (4), or handoff” has no formal counterpart.

**What must be implemented or corrected.**

- State and publish the formal exit-(4)-or-handoff conclusion rather than relying on a ledger name, and connect it to the G2 distinguished germ on the active family.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** partial: PARTIAL
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [157] — G3 or same-interface table: compression

**Exact manuscript diagram output.** G3 or same-interface table: compression

**Manuscript rows.** Label set **L25** (paper page(s): 111, 112, 113, 114, 115, 116, 117, 118, 120); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedColdSameInterfaceTable` (Assembly.lean:1100); `coldSameInterfaceTableRow` (ColdCorridorRows.lean:694)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedColdSameInterfaceTable, selectedNearCubicBranch.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. “Nothing constructs a `TableRow`” is the manuscript's shape too — the paper never exhibits a row; the working lemma is “every row is routed” and the consumer negates existentials. `admissible` is `def:admissible-rank-quotient`, cited as a definition at exactly this point. Two of five conjuncts are trivial: `tableBound = Fintype.card Record` is `rfl`, and `row.increment = 0` is immediate from the `equalLength` field.

**What must be implemented or corrected.**

- Retain the manuscript's universal routing form, but instantiate it on the active same-interface family and remove any requirements that are only asserted by the row's data structure.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** partial: PARTIAL
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [159] — dense-packing residual: the no-edge of [158]; \(2^{c_{13}p_{13}\log_2 n}\) exceeds the labelled skeleton class, i.e.\ \(\theta>\theta_{\rm win}\)

**Exact manuscript diagram output.** dense-packing residual: the no-edge of [158]; \(2^{c_{13}p_{13}\log_2 n}\) exceeds the labelled skeleton class, i.e.\ \(\theta>\theta_{\rm win}\)

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `denseOrJointCodeOverflow` (BlockedCompressionRows.lean:64); `blockedClassCompressionCloses` (:101)

**Current combinator / shared continuation.** terminal closure; selectedScaleAdditivityDichotomy.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — The manuscript's single display is recovered only as the left disjunct; `K .windowPackageUnrealized` bundles two manuscript statements. Assembly.lean:3504 admits this in-source.

**What must be implemented or corrected.**

- Split `.windowPackageUnrealized` into the manuscript's realization failure and retained-code statements. Publish the exact skeleton-count overflow here and remove `selectedDenseJointCodeOverflow`.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedDenseJointCodeOverflow`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [ ] **Independent kernel check:** fail: NO: `selectedDenseJointCodeOverflow`

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

### Node [163] — neutral equal-length terminal configuration: second strand graph-realized?

**Exact manuscript diagram output.** neutral equal-length terminal configuration: second strand graph-realized?

**Manuscript rows.** Label set **L26** (paper page(s): 121, 122, 123); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `neutralGermSymmetryDichotomy` (ColdCorridorRows.lean:800)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row, Decision.run; selectedAbsorbedGermResidual, selectedNearCubicBranch.

**Primary defect class.** wrong mathematical branch test or proof strategy.

**Fresh audit diagnosis.** ⚠ DIVERGENT — Lean splits by the canonical order `Precedes`; the graph-realizability of the second strand — the literal diagram question — is never tested, and the `.inr` arm is [166]/[169], not [167]. `germ.Neutral` is the trichotomy's G3, missing `def:neutral-equal-length-germ`'s `increment = 0`; `LengthChanging` exists and is unused.

**What must be implemented or corrected.**

- Decide graph-realizability of the second strand exactly as drawn, require the neutral germ's `increment = 0`, and route the no/yes arms to [165]–[166] and [167] respectively. Canonical order is not the branch test.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: `_structure` bound and discarded
- [ ] **No illegal carrier/API:** partial: `_structure` bound and discarded
- [ ] **Exact manuscript proof:** partial: DIVERGENT
- [x] **Independent kernel check:** pass: YES

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

### L18 — node(s) [129]

`cor:sparse-pair-entropy-saturation`, `def:active-surplus-demands`, `def:baseline-spine-demand`, `def:named-surplus-exits`, `lem:sparse-excess-port-extraction`, `lem:sparse-port-activation`, `lem:surviving-active-family`, `prop:sparse-pair-independence-dichotomy`.

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
