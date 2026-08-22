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
- Nodes passing every strict gate: **137**.
- Nodes retained in this ledger: **43**.
- Axiom-audit declarations: **75** = **49 clean** + **26 tainted**; unreported: **0**.
- Loud undefined frontier producers: **15**.

### Loud frontier producers

- `selectedAbsorbedGermBlockedResidual`
- `selectedAbsorbedTypeBFanHeavyContinuation`
- `selectedAbsorbedTypeBFanDegreeFourContinuation`
- `selectedBarrierOverlapSerialSystem`
- `selectedCubicBottleneckSeparator`
- `selectedDenseJointCodeOverflow`
- `selectedDenseSameSizeCanonicalSwap`
- `selectedLargeBudgetPressureCensus`
- `selectedRouteEightBudgetEdge`
- `selectedRouteEightPeelingSaturatedStage`
- `selectedRouteEightTrueTwoCarrierEntry`
- `selectedRouteEightUnclassifiedPiece`
- `selectedSparsePairSerialSystem`
- `selectedTypeAVisibleRouteEightImpossible`
- `selectedTypeBRoutedEnvelope`

### Cross-cutting framework blockers

- `StrategyDag.lean` contains only presentation-equality examples and no final `strategyDag`; the
  package root still imports the application-local `Assembly.lean`. Full closure therefore lacks
  the sealed topology endpoint required by the framework.
- The requested Type B source boundary uses only the canonical API. The former application helper
  `selectedTypeBMarkedLedger` and its compatibility aliases have been removed; the marked Type B
  chain is now literal typed composition of permitted rows on one monotone `ExactLedger`. The
  repository-wide compiled API catalogue remains stale against the current compiled declarations;
  its protected `.agents` allowlist could not be refreshed from this workspace. The canonical
  boundary scan itself completes before reporting only that generated-catalogue drift.
- Normal Assembly elaboration is intentionally loud at the 15 names above. Any other Lean error is
  an additional defect and must be entered in both live audit rows before work continues.

### Exact section set

[103], [106], [110], [111], [113], [114], [115], [116], [117], [118], [123], [124], [129], [131], [132], [134], [137], [140], [142], [143], [144], [145], [147], [154], [156], [157], [159], [162], [163], [165], [166], [167], [168], [170], [171], [172], [174], [175], [176], [177], [178], [179], [180].

## 4. Dependency-ordered repair route

1. **Type A and route 8:** repair [103], [106], [110]–[118], [123], and [124], using
   the real canonical carrier reading and exact pressure/peeling statements.
2. **Sparse-surplus accounting:** repair [129], [131], [132], [134], [137], [140], [142]–[145],
   and [147], then probe the Type B handoffs.
3. **Cold/dense branch:** repair [154], [156], [157], [159], [162]–[172], and [174]–[177].
4. **Pair serial closure:** construct the exact obstruction/system/arithmetic chain [178]–[180].
5. **Sealed endpoint:** only after every node owner is green, express the final topology in
   `StrategyDag.lean`, switch the package root to it, and regenerate the sealed report.

The ordering is diagnostic; it does not authorize a multi-node implementation change. A repair
still stops at its first downstream failure and updates only that label's two audit rows.

## 5. Node-by-node remediation checklists

### Node [103] — exit 5? target-complete response compression

**Exact manuscript diagram output.** exit 5? target-complete response compression

**Manuscript rows.** Label set **L15** (paper page(s): 154, 155, 156, 157, 158, 159, 160, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177, 178, 179, 180, 182, 183, 185); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `typeAExitFiveDichotomy` (SpineRows.lean:5813)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedTypeAExitFiveToSeven, selectedTypeAExitFiveToSevenSilent.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ SURROGATE-TRIVIAL — The manuscript's exit (5) tests the trace basin's declared coordinates and its discharge is two-case. Lean replaced it with a global compressibility claim the ledger had already decided, which silently deletes the second case. The `by_cases` splits on a proposition the ledger has already decided.

**What must be implemented or corrected.**

- Replace the already-decided global compressibility surrogate with the trace basin's declared-coordinate exit-(5) test and implement both discharge cases from the manuscript.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: SURROGATE-TRIVIAL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [106] — support-dependence branch closes

**Exact manuscript diagram output.** support-dependence branch closes

**Manuscript rows.** Label set **L15** (paper page(s): 154, 155, 156, 157, 158, 159, 160, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177, 178, 179, 180, 182, 183, 185); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `typeAExitSixScopeDichotomy` (SpineRows.lean:5907); instances TypeAExitRun.lean:310,320

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedTypeAExitFiveToSeven, selectedTypeAExitFiveToSevenSilent.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Genuine terminal closure; both arms die, by replacement exclusion and by minimality plus transfer.

**What must be implemented or corrected.**

- Repackage the two already proved terminal arms as residual-local closures at the exact exit-(6) decision ledger; no new mathematical alternative is permitted.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: partial: the two arm propositions are object-level existentials
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [110] — exit (8): route-8 residual profile

**Exact manuscript diagram output.** exit (8): route-8 residual profile

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8ResidualProfileRow` (SpineRows.lean:4486)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** paper control-flow object not represented exactly.

**Fresh audit diagnosis.** ⚠ PLUMBING — Exit (8) is a clause of a definition with no proof; the row re-keys the [107]-no fact. The manuscript's content for this node enters the ledger at [114]. A re-labelling of [109].

**What must be implemented or corrected.**

- Treat [110] as the exact route-8 residual produced by the [107]-no arm and publish only the profile facts the manuscript assigns here. The substantive carrier work remains at [114].
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: PLUMBING
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [111] — global squeeze extracts a route-8 Type A collection $\mathcal X_A$ carrying $D_A(\mathcal X_A)$

**Exact manuscript diagram output.** global squeeze extracts a route-8 Type A collection $\mathcal X_A$ carrying $D_A(\mathcal X_A)$

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8GlobalSqueezeRow` (SpineRows.lean:4517)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** paper control-flow object not represented exactly.

**Fresh audit diagnosis.** ⚠ PLUMBING — The invariant table gives [111] one label, glossed “*defines* the Type A route-8 deficit”. Both quantitative statements about D_A are assigned to [112]/[113]. D_A itself exists as `TypeBEnvelopeCharge.route8Deficit`. No extraction of 𝒳_A exists in the formalization at all.

**What must be implemented or corrected.**

- Construct the selected Type A collection `𝓧_A` and its deficit `D_A(𝓧_A)` from the global squeeze. The existing `TypeBEnvelopeCharge.route8Deficit` definition is not an extraction proof.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: PLUMBING
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [113] — large-budget deficit: $D_A(\mathcal X_A)\ge(1/4-\tau_{\rm win})\|R\|-o(\|R\|)$

**Exact manuscript diagram output.** large-budget deficit: $D_A(\mathcal X_A)\ge(1/4-\tau_{\rm win})\|R\|-o(\|R\|)$

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8LargeBudgetDeficitRow` (SpineRows.lean:4570)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ SURROGATE-TRIVIAL — The manuscript's [113] is a numeric lower bound on D_A with τ_win; Lean conjoins the residual-C branch flag instead. τ_win, D_A and the 0.0873 coefficient occur nowhere in the sources. τ_win appears nowhere in `Spine.Data` or in any `Holds` branch.

**What must be implemented or corrected.**

- Publish the numerical lower bound `D_A(𝓧_A) ≥ (1/4 - τ_win)|R| - o(|R|)` with `τ_win` projected from registered data; remove the residual-C flag surrogate and its redundant requirement.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: the second `Requires` is redundant and does no work
- [ ] **No illegal carrier/API:** partial: the second `Requires` is redundant and does no work
- [ ] **Exact manuscript proof:** partial: SURROGATE-TRIVIAL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [114] — each entry passes to its canonical minimal target-complete response-support core inside the declared $u$-supported response algebra

**Exact manuscript diagram output.** each entry passes to its canonical minimal target-complete response-support core inside the declared $u$-supported response algebra

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8CarrierCoreRow` (SpineRows.lean:4596)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL-TRIVIAL — Core existence, minimality, deletion-defect and forgotten-coordinate are all forced by the canonical minimization that defines 𝒞_ess; the paper says nothing is assumed. The theorem's content is genuine and matches the manuscript; what is missing is the binding of `presented` to the residual's own entry.

**What must be implemented or corrected.**

- Bind `PresentedEntry` to the residual's own selected route-8 entry, then construct the canonical minimal target-complete core locally and publish all externally used core properties.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL-TRIVIAL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [115] — some entry has $\alpha_{\mathcal X}(\xi)\le1$?

**Exact manuscript diagram output.** some entry has $\alpha_{\mathcal X}(\xi)\le1$?

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8SmallCoreCollapseRow` (SpineRows.lean:4626)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. `Alternatives` is continuation-passing over the trace basin's own minimality clause — the paper does not derive the exit disjunction either, it reads it off `def:typeA-trace-basin`. The cut-parity content is proved. The produced fact is never consumed.

**What must be implemented or corrected.**

- Make the `α ≤ 1` decision consume the presented entry and route its two typed arms. Remove the currently dead produced fact only if the exact manuscript continuation needs no key.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: partial: universal over every `PresentedEntry`, never instantiated at a census entry
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [116] — exits (4)--(7) occur

**Exact manuscript diagram output.** exits (4)--(7) occur

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8SmallCoreCollapseRow` (SpineRows.lean:4626)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ SURROGATE-TRIVIAL — The cut-parity mechanism is genuinely formalized, but the statement stops one step short: `Alternatives` is a caller-supplied arbitrary `Prop` gated behind a `minimality` hypothesis that `Route8.PresentedEntry` has no field to supply, and both consumers discard it. Not a faithful schema — `def:typeA-trace-basin` stipulates the (a)–(d) ↔ exits (4)–(7) dictionary in the definition itself, and the exits exist in Lean, so the consequent was expressible. Consequence: because α ≥ 2 is never established, “two-support” in Lean means few private carriers, not the manuscript's two essential incidences. Missing: `alpha ≤ 1 → (ExitFour ∨ Five ∨ Six ∨ Seven)` at the entry's receiver.

**What must be implemented or corrected.**

- Replace caller-supplied `Alternatives` with the exact conclusion `ExitFour ∨ ExitFive ∨ ExitSix ∨ ExitSeven` at the entry's receiver, derived from the trace-basin dictionary and cut parity.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: SURROGATE-TRIVIAL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [117] — some entry has $\pi_{\mathcal X}(\xi)\le2$?

**Exact manuscript diagram output.** some entry has $\pi_{\mathcal X}(\xi)\le2$?

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8CarrierDichotomy` (SpineRows.lean:4774)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** illegal read/write, discarded requirement, or noncanonical carrier.

**Fresh audit diagnosis.** ✅ FAITHFUL — At δ = 3 the condition is π ≤ 2, exactly clause (T4). `route8TwoCarrierReductionRow` is dead code.

**What must be implemented or corrected.**

- Use the route-8 census fact to establish the private-carrier decision `π_𝓧(ξ) ≤ 2`; do not bind and discard the census, and remove the dead duplicate reduction row.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: `K .route8Census` bound and discarded, so this declaration proves none of `prop:typeA-route8-carrier-reduction`
- [ ] **No illegal carrier/API:** partial: `K .route8Census` bound and discarded, so this declaration proves none of `prop:typeA-route8-carrier-reduction`
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [118] — two-support route-8 entry

**Exact manuscript diagram output.** two-support route-8 entry

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8CarrierDichotomy` (SpineRows.lean:4774); `route8EntryKindDichotomy` (:4823)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** fact absent from or not wired into the literal branch ancestry.

**Fresh audit diagnosis.** ✅ FAITHFUL — Faithful for the state itself; clause (T5) is not attached on the live path and its row is dead code. No closed path leaves [118].

**What must be implemented or corrected.**

- Replace the degenerate `PUnit`/empty-essential-core presentation with the real carrier state `ρ_u(B_u)` realized by `CanonicalPiece.cutStateRepresentative`; attach clause (T5) and wire both entry-kind arms.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [ ] **Independent kernel check:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [123] — large-budget demand descent: target-defect entries peel by exit (4); terminal survivor is route 8

**Exact manuscript diagram output.** large-budget demand descent: target-defect entries peel by exit (4); terminal survivor is route 8

**Manuscript rows.** Label set **L17** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `route8PeelingDescentRow` (SpineRows.lean:4881)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedRouteEightResidual.

**Primary defect class.** fact absent from or not wired into the literal branch ancestry.

**Fresh audit diagnosis.** ✅ FAITHFUL — `PeelChain` requires each peel to be a two-carrier target-defect entry at a stage satisfying `StageRate`, with termination by strict decrease. `route8PressureDescentRow` is dead code.

**What must be implemented or corrected.**

- Complete the two missing leaves: prove the exact `1/4` peeling charge at saturated stages and run the arm-independent census rows on non-census entry sites before invoking the descent.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry` and `selectedRouteEightPeelingSaturatedStage`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [ ] **Independent kernel check:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry` and `selectedRouteEightPeelingSaturatedStage`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [124] — local exclusion theorem: no two-support route-8 obstruction

**Exact manuscript diagram output.** local exclusion theorem: no two-support route-8 obstruction

**Manuscript rows.** Label set **L16** (paper page(s): 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 233, 234, 250, 251); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no live declaration)

**Current combinator / shared continuation.** —; —.

**Primary defect class.** mathematical proof or required witness absent.

**Fresh audit diagnosis.** ❌ ABSENT — Both arms call `selectedRouteEightTrueTwoCarrierEntry`. The dead-code chain that would produce it is provably degenerate: one conjunct is a tautology and the sibling arm is its negation. Missing: instantiate `Route8.terminalTwoCarrierNoGo` at the selected census entry. Every ingredient is proved; only the construction and wiring are absent.

**What must be implemented or corrected.**

- Instantiate `Route8.terminalTwoCarrierNoGo` at the selected real census entry, construct the declared deletion witnesses and exit-(4) receiver family, publish closure, and remove the degenerate dead chain.
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
- [ ] **Correctly wired:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry`
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [ ] **Exact manuscript proof:** fail: ABSENT
- [ ] **Independent kernel check:** fail: NO: `selectedRouteEightTrueTwoCarrierEntry`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [129] — full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)

**Exact manuscript diagram output.** full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)

**Manuscript rows.** Label set **L18** (paper page(s): 59, 60, 83, 84); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedBaselineSpineDemand` (Assembly.lean:214); `baselineSpineDemandRow` (SurplusRows.lean:212)

**Current combinator / shared continuation.** AtomicCT.run row; selectedBaselineSpineDemand.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ SURROGATE-TRIVIAL — The manuscript earns E_spine ≤ C_E·n from the window and high-entropy packages, conditionally. Lean fabricates B₀(n) empty-support coordinates so the deficit is identically 0. Load-bearing weakness of the block: [131], [137] and [138] all consume a deficit that was chosen, not derived.

**What must be implemented or corrected.**

- Replace the fabricated empty-support baseline with the manuscript's derived active family `𝓐₀ = 𝓟_exc` and prove `E_spine ≤ C_E n` from the window and high-entropy packages.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: SURROGATE-TRIVIAL
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [131] — free-pair entropy sandwich: \(\|\Pi_{\rm free}\|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)

**Exact manuscript diagram output.** free-pair entropy sandwich: \(\|\Pi_{\rm free}\|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)

**Manuscript rows.** Label set **L19** (paper page(s): 82, 86); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedMixedSparseSpineDependence` (:254), `selectedExactCubicBaselineBudget` (:280), `selectedIncrementalSkeletonRoom` (:307), `selectedSkeletonDominates` (:335)

**Current combinator / shared continuation.** AtomicCT.run row, terminal closure; selectedExactCubicBaselineBudget, selectedIncrementalSkeletonRoom, selectedMixedSparseSpineDependence, selectedSkeletonDominates, selectedStrictSurplusBranch.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. `freeCount_le_of_sandwich` is invoked twice on the live path. And the case split is the manuscript's own: tex:1044 calls the [131] and free-side-[137] entropy counts “branch tests, exactly as at [158]”. The declaration that states the sandwich carries no EG-NODE annotation; the only annotated declaration containing it is the tainted umbrella.

**What must be implemented or corrected.**

- Publish the already used free-pair entropy sandwich from its own residual-local row rather than only through the tainted strict-surplus umbrella.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [ ] **Residual-local proof:** partial: MIXED
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [132] — blocked-pair routing: exit or canonical blocker?

**Exact manuscript diagram output.** blocked-pair routing: exit or canonical blocker?

**Manuscript rows.** Label set **L20** (paper page(s): 60, 61, 62, 63, 64, 65, 82, 86); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedBlockedPairRoutingDichotomy` (Assembly.lean:363)

**Current combinator / shared continuation.** composition; selectedBlockedPairRoutingDichotomy.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ WEAKER — In `∃ pair ∈ pairs, P` the binder `pair` does not occur free in `P`; the statement is `pairs.Nonempty ∧ (a blocker exists somewhere)`, not “π has a blocker”. The proof picks an arbitrary member. Discards `FunctionalOn`; the manuscript's circuit argument runs on a functional quotient. The per-pair attribution [134] is built on rests on a non-pair-specific certificate.

**What must be implemented or corrected.**

- Make the blocker existential depend on the bound pair `π`, retain `FunctionalOn`, and publish the per-pair exit-or-canonical-blocker alternative.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: WEAKER
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [134] — canonical blocker ledger: each blocked pair gets one \(B_\pi\) and one capacity token

**Exact manuscript diagram output.** canonical blocker ledger: each blocked pair gets one \(B_\pi\) and one capacity token

**Manuscript rows.** Label set **L21** (paper page(s): 60, 61, 62, 63, 64, 65); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedCanonicalPairFacts` (Assembly.lean:404); `canonicalPairLedgerRow` (SurplusRows.lean:642)

**Current combinator / shared continuation.** AtomicCT.run row; selectedCanonicalPairFacts.

**Primary defect class.** mathematical statement weakened or replaced by a surrogate.

**Fresh audit diagnosis.** ⚠ SURROGATE-TRIVIAL — `def:canonical-blocker-ledger` ranges over pairs of distinct demands; `DemandActivation.blockers` unions over `pair ×ˢ pair` with no distinctness filter, so the diagonal makes every pair blocked and Π_free empty. Counting identities are faithful; the blocked/free split they partition is degenerate. Clause (f) is structurally absent (`chordObstructions := fun _ => ∅`); (d)/(e) are installed on exactly one pair.

**What must be implemented or corrected.**

- Remove diagonal self-pairs from blocker construction, implement clause (f) instead of `chordObstructions := ∅`, and install clauses (d)/(e) for every blocked pair rather than one witness.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: SURROGATE-TRIVIAL
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [137] — coupled excess \(D_{\rm all}>0\)?

**Exact manuscript diagram output.** coupled excess \(D_{\rm all}>0\)?

**Manuscript rows.** Label set **L22** (paper page(s): 65, 66, 68, 69, 70, 71, 73, 76, 77, 79, 80, 81); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedRoleFibrePartition` (Assembly.lean:1322)

**Current combinator / shared continuation.** AtomicCT.run row, terminal closure; selectedRoleFibrePartition, selectedStrictSurplusBranch.

**Primary defect class.** fact proved detached from the literal active residual.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. The verdict graded one of three covering declarations. `coupledExcessDichotomy` performs the D_all > 0 decision, matching the caption arm for arm; `RoleFibrePartitionStatement` is a combinatorial identity, unconditional in the manuscript too. Its declared requirement is a discarded binding. The actual `D_all > 0?` decision (`coupledExcessDichotomy`, HomogeneousBottleneckRows.lean:642) is faithful but reachable only inside the tainted umbrella.

**What must be implemented or corrected.**

- Run the faithful `D_all > 0` decision as its own residual-local node after the exact [129]–[136] accounting, and remove the unused declared prerequisite from the partition row.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [ ] **Residual-local proof:** fail: NO
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [140] — window-incidence geometric audit: homogeneous matching/star

**Exact manuscript diagram output.** window-incidence geometric audit: homogeneous matching/star

**Manuscript rows.** Label set **L23** (paper page(s): 65, 66, 67, 68, 69, 70, 71, 73, 76, 77, 79, 80, 81, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `windowIncidenceAuditRow` (HomogeneousBottleneckRows.lean:90)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedSparsePressureOverloadCloses.

**Primary defect class.** illegal read/write, discarded requirement, or noncanonical carrier.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. `lem:same-token-matching-star` is proved for an arbitrary graph and instantiated three times, and `cor:homogeneous-same-token-caps-close` says so. One term proving all three instances is the faithful mirror. Unconsumed, but the content reaches [137] and [144] by two other routes. Never consumed. Its own docstring concedes “Nothing about the class is used in the proof.”

**What must be implemented or corrected.**

- Instantiate the matching/star theorem on the active window-incidence class and either publish a consumed conclusion or remove this dead audit-only row and represent the manuscript use at its actual consumer.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: partial: universal over all presentations
- [ ] **Correct ledger registration:** partial: `Requires` bound and discarded
- [ ] **No illegal carrier/API:** partial: `Requires` bound and discarded
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [142] — remainder-surplus geometric audit: homogeneous matching/star

**Exact manuscript diagram output.** remainder-surplus geometric audit: homogeneous matching/star

**Manuscript rows.** Label set **L23** (paper page(s): 65, 66, 67, 68, 69, 70, 71, 73, 76, 77, 79, 80, 81, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `remainderSurplusAuditRow` (HomogeneousBottleneckRows.lean:112)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedSparsePressureOverloadCloses.

**Primary defect class.** illegal read/write, discarded requirement, or noncanonical carrier.

**Fresh audit diagnosis.** ✅ FAITHFUL — Re-checked against the manuscript's proof: the earlier WEAKER/DIVERGENT verdict does not hold. Same as [140]: one class-agnostic lemma, three instantiations. Never consumed.

**What must be implemented or corrected.**

- Do the same residual-local instantiation for the remainder-surplus class; the current class-agnostic theorem and unused requirement do not certify this node.
- Prove the node value inside the atomic executor from `inputs.current` and semantic-key reads
  through `inputs.get`; eliminate an ignored object argument, detached universal proof, or
  requirement not tied to the literal incoming residual.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [ ] **Residual-local proof:** fail: partial:
- [ ] **Correct ledger registration:** partial: `Requires` bound and discarded
- [ ] **No illegal carrier/API:** partial: `Requires` bound and discarded
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [143] — primitive blocker-support geometric audit: homogeneous matching/star

**Exact manuscript diagram output.** primitive blocker-support geometric audit: homogeneous matching/star

**Manuscript rows.** Label set **L23** (paper page(s): 65, 66, 67, 68, 69, 70, 71, 73, 76, 77, 79, 80, 81, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `primitiveClassOverloadRow` (HomogeneousBottleneckRows.lean:156)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedSparsePressureOverloadCloses.

**Primary defect class.** paper control-flow object not represented exactly.

**Fresh audit diagnosis.** ⚠ PLUMBING — The [141]-no arm already carries the primitive-class verdict; this row hands the same proposition to the audit under the required name. The manuscript has no corresponding step. Never consumed.

**What must be implemented or corrected.**

- Do not create new mathematics for an audit-only re-key absent from the manuscript. Either remove the redundant row and wire the [141]-no fact directly, or identify and publish the exact manuscript proposition it is meant to represent.
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.
- Give the owner a literal nonempty `FactManifest`; consume every declared requirement, return
  exactly `Produces`, and commit with `AtomicCT.run`. Remove unused requirements and every
  custom wrapper/carrier on this path without deleting valid mathematical content.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass
- [x] **Residual-local proof:** pass
- [ ] **Correct ledger registration:** partial: the audit row's `Requires` is bound and discarded
- [ ] **No illegal carrier/API:** partial: the audit row's `Requires` is bound and discarded
- [ ] **Exact manuscript proof:** partial: PLUMBING
- [x] **Independent kernel check:** pass: YES

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [144] — bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Exact manuscript diagram output.** bottleneck discharge: sparse exit, Type B, or near-cubic spine

**Manuscript rows.** Label set **L24** (paper page(s): 66, 67, 91, 93, 94); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedBottleneckDischarge` (Assembly.lean:518)

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedBottleneckDischarge.

**Primary defect class.** fact absent from or not wired into the literal branch ancestry.

**Fresh audit diagnosis.** ✅ FAITHFUL — The caps arm genuinely closes; the pattern arm's routing is proved by the manuscript's own pigeonhole, and `RoutedBottleneck.outcome` is a real theorem. Reached identically from all three of [139]/[141]/[143]'s arms, so the class dispatch is inert.

**What must be implemented or corrected.**

- Implement `selectedTypeBRoutedEnvelope` and `selectedCubicBottleneckSeparator`: construct the switch reading with `cutStateRepresentative`, present its quotient/replacement support, and route each exact outcome into Type B or closure.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: NO: `selectedTypeBRoutedEnvelope` and `selectedCubicBottleneckSeparator`
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass: FAITHFUL
- [ ] **Independent kernel check:** fail: NO: `selectedTypeBRoutedEnvelope` and `selectedCubicBottleneckSeparator`

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [145] — cold-branch continuation from the no-edge of [22], after the spine estimate

**Exact manuscript diagram output.** cold-branch continuation from the no-edge of [22], after the spine estimate

**Manuscript rows.** Label set **L25** (paper page(s): 111, 112, 113, 114, 115, 116, 117, 118, 120); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `selectedColdWindowLedgerSplit` (Assembly.lean:786); `coldWindowLedgerSplitRow` (ColdCorridorRows.lean:72)

**Current combinator / shared continuation.** AtomicCT.run row, terminal closure, Decision.run; selectedColdWindowLedgerSplit, selectedNearCubicBranch.

**Primary defect class.** paper control-flow object not represented exactly.

**Fresh audit diagnosis.** ⚠ PLUMBING — A diagram continuation box; both labels are definitions. The hot/cold split is formalized once, at [22]. The quantitative half of `def:cold-window-ledger` is not here.

**What must be implemented or corrected.**

- Keep the box as the no-edge continuation of [22], but publish the quantitative cold-window-ledger facts at their actual nodes and verify the literal predecessor instead of assigning extra mathematics to [145].
- Follow the cited manuscript proof and replace the current weaker, divergent, or bookkeeping
  schema with the exact displayed proposition and alternatives. Preserve their order and scope.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired:** pass: on a probed stub-free closure
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [ ] **Exact manuscript proof:** partial: PLUMBING
- [x] **Independent kernel check:** pass: YES; arm probed stub-free

**Exit criterion.** Reinspect the declaration body and call site, update this node row and every
listed paper-fact row from the compiled term, run the table/API checks, and remove this section
only when all seven boxes are checked. A later compiler failure is recorded as downstream unless
that later node has its own independently failing audit row.

### Node [147] — route-8 private-incidence collision closes

**Exact manuscript diagram output.** route-8 private-incidence collision closes

**Manuscript rows.** Label set **L25** (paper page(s): 111, 112, 113, 114, 115, 116, 117, 118, 120); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** — (no kernel-clean declaration)

**Current combinator / shared continuation.** terminal closure, Decision.run, AtomicCT.run row; selectedNearCubicBranch.

**Primary defect class.** fact absent from or not wired into the literal branch ancestry.

**Fresh audit diagnosis.** ✅ FAITHFUL-TRIVIAL — The re-routing is the manuscript's own treatment: “If θ < 1/78, then τ(θ) < 3/13 by def:cold-window-ledger; this is exactly the private-support inequality used in thm:large-budget-route8-only, so the route-8 branch closes” (tex:7309). The Part XI caption says the *existing* inequality closes at [147]; there is no separate private-carrier argument to be missing. The conversion is not free — `route8RateFromColdBelowRow` discharges the boundary-incidence supply reading. Covered only by the tainted umbrella.

**What must be implemented or corrected.**

- Give the faithful rate conversion a kernel-clean owner outside the tainted umbrella and close the exact skeleton-budget corner through `selectedRouteEightBudgetEdge` if it remains after using the exact budget.
- Run the repaired owner on the literal typed predecessor, select the correct `Decision` arm,
  and pass its exact output ledger forward without reconstructing a cursor or merging siblings.
- Build the narrow owner and an independent branch probe. The node is not green while its
  producer or composed arm reaches any undefined frontier name shown in the kernel cell below.

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [ ] **Correctly wired:** fail: N/A
- [x] **Residual-local proof:** N/A
- [x] **Correct ledger registration:** N/A
- [x] **No illegal carrier/API:** N/A
- [x] **Exact manuscript proof:** pass: FAITHFUL-TRIVIAL
- [ ] **Independent kernel check:** N/A N/A

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

### Node [177] — decorated handoff fan data at the heavy centre \(z\): continue at Type B [65]

**Exact manuscript diagram output.** decorated handoff fan data at the heavy centre \(z\): continue at Type B [65]

**Manuscript rows.** Label set **L28** (paper page(s): 124, 125); its complete label
list is in Appendix A. The corresponding live row cells are in the paper-fact implementation
table; their exact environments supply the inherited quantifiers and hypotheses.

**Current Lean owner.** `absorbedGermFanEnvelopeRow` (ColdCorridorRows.lean:676), run on
`absorbedGermDichotomy`'s `.inr` ledger in `selectedAbsorbedGermResidual`

**Current combinator / shared continuation.** terminal closure, AtomicCT.run row; selectedAbsorbedGermResidual.

**Primary defect class.** first downstream branch theorem missing; the selected [177]
fact, its [65] ledger write, and node [68]'s exact degree split are repaired.

**Fresh audit diagnosis.** ✅ EXACT [177] FACT AND DIRECT [65] ENTRY REPAIRED —
`K .typeBFanEntry` now has the paper's two literal input forms: a canonical assigned
Type B support, or the indexed absorbed-corridor handoff family. On the all-heavy arm,
`absorbedGermFanEnvelopeRow` writes the latter alternative directly. For every selected
half-edge it chooses `z ∈ J`, proves `degree z > data.threshold`, proves every
neighbour of `z` has degree `data.threshold`, and constructs the geometric decorated
handoff datum from the two distinct corridor incidences and the two simple separated
connector tails, with `H = {z}` and `card K_z = 2`. The row neither requests nor invents
a maximal packing, canonical negative core, or zero-surplus equality. There is no private
key, conversion theorem, compatibility wrapper, callback, or second history.

`SpineVocabulary` and `ColdCorridorRows` kernel-check, and independent probes run [177],
read `K .typeBFanEntry` back with `ExactLedger.get`, and run [68]'s sealed
`Decision.run`. The repaired `typeBFanDegreeDichotomy` now case-splits the two literal
forms of `TypeBFanEntryStatement`. It preserves the canonical support on the ordinary
arm. On the absorbed arm it retains the complete indexed corridor family and decides
whether one actual centre satisfies
`data.threshold + 1 < degree centre`; on the other branch, [177]'s strict lower bound
and the negated heavy alternative give
`degree centre = data.threshold + 1` by arithmetic. Both results are published under
the two semantic [68] keys on the exact incoming ledger. No literal `4` or `5` is used;
the EG presentation supplies `threshold = 3`.

The selected [177] continuation now runs [67] and [68] directly on that ledger and
matches the resulting `Decision` arms. The first broader failure is therefore node [69]:
`typeBFanLocalDichotomyRow` proves its local alternative only for the canonical support
form and does not yet consume the indexed absorbed heavy-centre family. The later [79]
degree-four profile and [70] fan-certificate rows have the analogous second-input work,
but neither is needed to establish the exhaustiveness or ledger correctness of [68].

**What must be implemented or corrected.**

- No additional fact is needed to connect [177] through [65], [67], and [68]. The exact
  ledger route and [68] decision are implemented.
- The next paper-labelled obligation is [69]'s heavy-arm local dichotomy. Its statement must
  consume `AbsorbedGermFanHeavyCentreStatement` directly, retain the indexed half-edge,
  centre, incidences, tails, and envelope witness, and publish [69]'s exact two semantic
  alternatives. It must not coerce the absorbed family into a canonical remainder support.
- The later [79] and [70] rows require the same two-input audit on their respective branches;
  those are downstream facts, not missing premises of [68].

**Live gate checklist.**

- [x] **Implemented / reachable:** pass
- [x] **Correctly wired at [177]→[65]→[67]→[68]:** pass: direct semantic-key writes and
  reads on the literal `.inr` ledger
- [x] **Residual-local proof:** pass
- [x] **Correct ledger registration:** pass
- [x] **No illegal carrier/API:** None found
- [x] **Exact manuscript proof:** pass for [177]'s case-(ii) output, direct [65] entry, and
  [68]'s exhaustive heavy/degree-four split
- [x] **Independent [68] kernel check:** the [177] owner, exact-ledger read probe, and focused
  sealed-`Decision.run` probe pass; the broader build fails first at downstream node [69]

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

### L12 — node(s) [65], [66], [68], [69], [70], [71], [72], [73], [74], [77], [81], [82], [84]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`.

### L13 — node(s) [67]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:deletion-critical`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`.

### L14 — node(s) [76], [85]

`cor:compatible-pair-typeB-routing`, `cor:degree-four-local-activation`, `cor:heavy-center-local-dichotomy`, `def:closed-fan-window-pair`, `def:decorated-fan-envelope`, `def:decorated-typeB-envelope-support`, `def:direct-cycle-free-closed-pair`, `def:fan-closed-port`, `def:fan-compatible-open-ports`, `def:heavy-center-triangular-port`, `def:marked-typeB-fan`, `def:open-port-suppression`, `def:surplus-ports`, `def:triangular-fan-core`, `def:typeB-bridge-statements`, `def:typeB-candidate-ledger`, `def:typeB-fan-safe`, `def:typeB-hybrid-incidence`, `def:typeB-ledger-carriers`, `def:typeB-multiclosed-residual`, `def:typeB-overlap-obstruction`, `def:typeB-residual-mass`, `def:typeB-window-incidence-profile`, `lem:compatible-pair-fan-closure`, `lem:cycle-rank`, `lem:decorated-envelope-deficit-bound`, `lem:decorated-envelope-with-route8-core`, `lem:decorated-fan-admissibility`, `lem:fan-certificate`, `lem:heavy-center-triangular-alternative`, `lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`, `lem:triangular-cross-shoulder`, `lem:triangular-first-landing`, `lem:triangular-port-return`, `lem:triangular-shoulder-completion`, `lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-to-overlap`, `lem:typeB-bridge-with-route8-core`, `lem:typeB-direct-fan-window-cycles`, `lem:typeB-exclusion`, `lem:typeB-global-local-reflection`, `lem:typeB-hybrid-B1`, `lem:typeB-hybrid-incidence-budget`, `lem:typeB-maximal-completion`, `lem:typeB-multiclosed-budget`, `lem:typeB-postledger-core-hygiene`, `lem:typeB-two-window-cycles`, `prop:fan-closed-port-typeB-routing`, `prop:triangular-port-typeB-routing`, `prop:typeB-bridge-reduction`, `prop:typeB-bridge-sublinear`, `prop:typeB-global-local-bridge`, `thm:branch-kill`.

### L15 — node(s) [103], [106]

`def:typeA-carrier-deletion-witness`, `def:typeA-channel-spectrum`, `def:typeA-continuation-classes`, `def:typeA-excess-basin`, `def:typeA-exit4-peeling`, `def:typeA-large-budget-deficit`, `def:typeA-receiver-load`, `def:typeA-route8-carriers`, `def:typeA-saturated-exits`, `def:typeA-silent-core-residual`, `def:typeA-support`, `def:typeA-terminal-two-carrier`, `def:typeA-trace-basin`, `def:typeA-visible-load`, `def:typeB-assigned-ledger`, `lem:decorated-envelope-no-double-count`, `lem:density-mersenne`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-common-port-return-cycle`, `lem:typeA-continuation-routing`, `lem:typeA-cubic-switch-absorption`, `lem:typeA-deletion-witness-declared`, `lem:typeA-entry-budget`, `lem:typeA-essential-deletion-witness`, `lem:typeA-exclusion`, `lem:typeA-exit4-discharge`, `lem:typeA-exit4-peeling-charge`, `lem:typeA-exit4-residual-routing`, `lem:typeA-exits-discharged`, `lem:typeA-first-entry`, `lem:typeA-high-degree-handoff`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-port-return`, `lem:typeA-receiver-loads`, `lem:typeA-reduced-silent-residual`, `lem:typeA-route8-burden`, `lem:typeA-saturated-handoff`, `lem:typeA-silent-excess`, `lem:typeA-silent-excess-count`, `lem:typeA-spectral-pressure`, `lem:typeA-threshold-algebra`, `lem:typeA-two-carrier-deletion-canonical`, `lem:typeA-unpeeled-silent-routing`, `lem:typeA-unpeeled-visible-routing`, `lem:typeA-unsaturated-discharge`, `lem:typeA-visible-entry`, `lem:window-handoff-center-accounting`, `prop:typeA-route8-closure-from-nogo`, `thm:typeA-two-carrier-nogo`.

### L16 — node(s) [110], [111], [113], [114], [115], [116], [117], [118], [124]

`cor:typeA-large-budget-closure-open-pressure`, `def:typeA-carrier-deletion-witness`, `def:typeA-exit4-family`, `def:typeA-large-budget-deficit`, `def:typeA-route8-carriers`, `def:typeA-terminal-two-carrier`, `def:typeA-true-route8-residual`, `def:typeB-assigned-ledger`, `lem:app-dense-window-closure`, `lem:app-global-smearing-closure`, `lem:app-typeA-quiet-bound`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-deletion-witness-declared`, `lem:typeA-essential-deletion-witness`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-route8-burden`, `lem:typeA-two-carrier-deletion-canonical`, `prop:typeA-route8-carrier-reduction`, `prop:typeA-route8-closure-from-nogo`, `thm:large-budget-route8-only`, `thm:typeA-two-carrier-nogo`.

### L17 — node(s) [123]

`cor:typeA-large-budget-closure-open-pressure`, `def:typeA-actual-profile-pressure-defects`, `def:typeA-carrier-deletion-witness`, `def:typeA-exit4-family`, `def:typeA-exit4-pressure-token`, `def:typeA-large-budget-deficit`, `def:typeA-open-window-blocker`, `def:typeA-peeling-reduced-ledger`, `def:typeA-pressure-absorbers`, `def:typeA-pressure-ledger`, `def:typeA-primitive-window-overload-excess`, `def:typeA-recorded-window-shadow-hit`, `def:typeA-route8-carriers`, `def:typeA-same-window-open-blocker-cap`, `def:typeA-same-window-overload-triple`, `def:typeA-terminal-two-carrier`, `def:typeA-true-route8-residual`, `def:typeA-two-terminal-pressure-records`, `def:typeA-unified-entries`, `def:typeA-unified-negative`, `def:typeA-window-attachment-shadow`, `def:typeA-zero-shadow-primitive-excess`, `def:typeB-assigned-ledger`, `lem:app-dense-window-closure`, `lem:app-global-smearing-closure`, `lem:app-typeA-quiet-bound`, `lem:typeA-carrier-cut-parity`, `lem:typeA-carrier-deletion-exit`, `lem:typeA-deletion-witness-declared`, `lem:typeA-essential-deletion-witness`, `lem:typeA-exit4-finite-descent`, `lem:typeA-final-open-pressure-exhaustion`, `lem:typeA-internal-quotient-mixed`, `lem:typeA-one-terminal-collapse`, `lem:typeA-open-pressure-zero-shadow-excess`, `lem:typeA-open-window-blocker-count`, `lem:typeA-peeling-reduced-reduction`, `lem:typeA-pressure-absorber-no-overcount`, `lem:typeA-pressure-defect-split`, `lem:typeA-pressure-is-exit4-peel`, `lem:typeA-pressure-ledger-no-overcount`, `lem:typeA-pressure-records-canonical`, `lem:typeA-pressure-token-two-carriers`, `lem:typeA-primitive-excess-zero-shadow`, `lem:typeA-profile-pressure-dependence-routing`, `lem:typeA-route8-burden`, `lem:typeA-routed-overload-not-open`, `lem:typeA-same-window-cap-overload-excess`, `lem:typeA-singleton-shadow-table`, `lem:typeA-two-carrier-deletion-canonical`, `lem:typeA-unified-burden`, `lem:typeA-unified-carriers`, `lem:typeA-unified-deficit`, `lem:typeA-window-blocker-accounting-audit`, `lem:typeA-window-blocker-numerics`, `lem:typeA-window-shadow-hit-routes`, `prop:typeA-exit4-closure-from-open-pressure`, `prop:typeA-exit4-closure-from-window-blockers`, `prop:typeA-exit4-closure-from-zero-shadow`, `prop:typeA-external-pressure-criterion`, `prop:typeA-external-pressure-reduction`, `prop:typeA-route8-carrier-reduction`, `prop:typeA-route8-closure-from-nogo`, `prop:typeA-unified-reduction`, `thm:large-budget-route8-only`, `thm:typeA-two-carrier-nogo`.

### L18 — node(s) [129]

`cor:sparse-pair-entropy-saturation`, `def:active-surplus-demands`, `def:baseline-spine-demand`, `def:named-surplus-exits`, `lem:sparse-excess-port-extraction`, `lem:sparse-port-activation`, `lem:surviving-active-family`, `prop:sparse-pair-independence-dichotomy`.

### L19 — node(s) [131]

`def:sparse-pair-response`, `lem:sparse-pair-dependence-exit`, `prop:sparse-entropy-sandwich-with-blockers`.

### L20 — node(s) [132]

`def:canonical-blocker-ledger`, `def:canonical-sparse-blocker-order`, `def:capacity-token-ledger`, `def:primitive-sparse-blocker-carrier`, `def:sparse-pair-response`, `def:surplus-blockers`, `lem:canonical-blocker-ledger-no-overcount`, `lem:capacity-token-supply`, `lem:primitive-carrier-supply`, `lem:sparse-pair-dependence-exit`, `lem:token-ledger-no-overcount`, `prop:sparse-entropy-sandwich-with-blockers`.

### L21 — node(s) [134]

`def:canonical-blocker-ledger`, `def:canonical-sparse-blocker-order`, `def:capacity-token-ledger`, `def:primitive-sparse-blocker-carrier`, `def:surplus-blockers`, `lem:canonical-blocker-ledger-no-overcount`, `lem:capacity-token-supply`, `lem:primitive-carrier-supply`, `lem:token-ledger-no-overcount`.

### L22 — node(s) [137]

`cor:coupled-single-graph-overload-budget`, `cor:forced-same-token-scale`, `cor:numerical-single-graph-budget`, `cor:quantified-homogeneous-class-overload`, `cor:quantitative-homogeneous-overload`, `cor:same-token-pattern-caps-close`, `def:homogeneous-token-charge`, `def:same-token-blocker-roles`, `def:same-token-patterns`, `lem:capacity-token-high-load`, `lem:exact-surplus-pair-charge-partition`, `lem:same-token-matching-star`, `prop:single-graph-sparse-pressure-routing`, `thm:sharp-classwise-homogeneous-token-budget`, `thm:tokenized-surplus-accounting-closure`.

### L23 — node(s) [140], [142], [143]

`cor:coupled-single-graph-overload-budget`, `cor:forced-homogeneous-same-token-scale`, `cor:forced-same-token-scale`, `cor:homogeneous-same-token-caps-close`, `cor:numerical-single-graph-budget`, `cor:quantified-homogeneous-class-overload`, `cor:quantitative-homogeneous-overload`, `cor:same-token-pattern-caps-close`, `def:homogeneous-token-charge`, `def:same-token-blocker-roles`, `def:same-token-patterns`, `def:same-token-routing-germs`, `lem:capacity-token-high-load`, `lem:exact-surplus-pair-charge-partition`, `lem:same-token-bottleneck-routing`, `lem:same-token-matching-star`, `prop:single-graph-sparse-pressure-routing`, `thm:homogeneous-overload-geometric-closure`, `thm:sharp-classwise-homogeneous-token-budget`, `thm:sharp-surplus-overload-audit`, `thm:tokenized-surplus-accounting-closure`.

### L24 — node(s) [144]

`cor:forced-homogeneous-same-token-scale`, `cor:homogeneous-same-token-caps-close`, `def:same-token-routing-germs`, `lem:same-token-bottleneck-routing`, `thm:homogeneous-overload-geometric-closure`, `thm:sharp-surplus-overload-audit`.

### L25 — node(s) [145], [147], [154], [156], [157]

`def:cold-bounded-germ`, `def:cold-corridor-first-failure`, `def:cold-same-interface-table`, `def:cold-skeleton-excess`, `def:cold-window-ledger`, `def:surviving-cold-branch`, `lem:cold-bounded-germ-trichotomy`, `lem:cold-corridor-first-failure`, `lem:cold-germ-extraction`, `lem:cold-increment-arithmetic`, `lem:cold-same-interface-table`, `lem:cold-short-self-return-filter`, `lem:cold-window-stub-excess`, `lem:hot-failure-cold-mass`, `thm:cold-branch-quantitative-closure`.

### L26 — node(s) [159], [162], [163], [165], [166], [167], [168]

`def:all-cold-comparison`, `def:neutral-equal-length-germ`, `def:window-realization-test`, `lem:dense-cold-pass`, `lem:dense-deficiency-routing`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, `lem:remainder-glue-injection`, `lem:symmetric-pair-endpoint`, `lem:two-strand-check`.

### L27 — node(s) [170], [171], [172]

`def:barrier-overlap-system`, `def:blocked-class`, `def:serial-window-system`, `lem:barrier-failure-overlap`, `lem:blocked-graphs-compress`, `lem:scale-additivity`, `lem:serial-system-sumset`, `lem:system-increment-arithmetic`, `lem:window-system-realizability`.

### L28 — node(s) [174], [175], [176], [177]

`lem:absorbed-germ-fan-data`, `lem:exact-collision-test`.

### L29 — node(s) [178], [179], [180]

`cor:spine-lower-bound-surplus-estimates`, `def:pair-overlap-system`, `def:spine-lower-bound-deficits`, `lem:pair-count-or-arithmetic`, `lem:pair-failure-overlap`, `lem:pair-system-increment-arithmetic`, `lem:pair-system-realizability`.
