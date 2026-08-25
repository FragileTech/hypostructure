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

### Node [104] — uncompressibility contradiction

**Update (this session, kernel-checked).** The section below is restored from the last commit.
Since then: exit (5) is the admissible (realized) compression datum and `typeAExitFiveClosed`
closes every [103]-yes ledger against `K .uncompressible`; `TypeAExitRun` builds and both lanes
elaborate in Assembly. The response-only gates below are superseded by that architecture (a
non-realized identification is not exit (5) and continues to [105]); they are kept for the
record until the audit tables are re-derived from a full build.

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

**Update (this session, kernel-checked).** The section below is restored from the last commit.
Since then: `K .route8PiecesClassified` states `thm:branch-kill` exactly
(`Route8Deficit.PieceClassification`, parametrized over the residual predicates); the
silent-first surrogate survives only as `SilentClassification`; `route8DeficitRow` is deleted.
The classification producer remains absent.

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
- [ ] **Classification producer:** `K .route8PiecesClassified` (`thm:branch-kill`). VERIFIED
  BLOCKED 2026-08-24 against live Lean, not audit cells: no ledger key carries
  `lem:typeA-exclusion`/`lem:density-mersenne` ([86]) — the vocabulary has no `∀`-piece Type A
  exclusion fact (all chain facts `[89]`–`[109]` are ∃-selected), and no `∀`-negative-surplus-piece
  bridge-membership pair (`lem:typeB-postledger-core-hygiene` facts `typeBDisjointLedger`/
  `typeBExclusionResidual` live at the ∃-selected assigned support). The generic charge theorem
  `TypeADischarge.unsaturatedDischarge` exists, but the saturated-receiver exit dichotomy at an
  arbitrary piece (`lem:typeA-saturated-handoff` + standing-invariant refutations of exits
  (1)–(3),(5),(6)) has no `∀`-piece carrier — the same [116]-shared refutations blocking the
  entry-census producer. Predecessor to produce at its own label ([86]), not at [123].
  2026-08-24: key `typeAExclusion` (idx 343) registered at all six vocabulary sites with the
  paper-exact Holds (the "Consequently" trichotomy of `lem:typeA-exclusion` at every negative
  zero-surplus canonical piece of the minimal counterexample's maximal-packing remainders);
  vocabulary builds. Producer row pending on the shared semantic obligations (see chat map).
  Obligation 3 DONE 2026-08-24: basin selection is total — `Route8.TraceBasin.traceComplete_support`
  (the selected support is a trace-complete candidate; D1 cut-boundary, D2 crossing-return,
  D3 window-attachment cut-boundary, D4 internal-wedge cases), the walk-crossing lemmas
  `exists_cutBoundary_of_walk_{from_inside,from_outside,crossing}`, and
  `select?_isSome_of_traceTo` / `exists_select?_eq_some_of_mem_routedLoads`
  (`Route8Residual.lean`, builds). This also discharges the entry-census gate's
  "select? = some basin up to a D3 window-label cut-boundary lemma" item.
  Obligation 5 DONE 2026-08-24: the (d)-alternative bridge —
  `DecoratedHandoff.exists_envelope_of_surviving` (`lem:typeA-high-degree-handoff` concluded
  from the surviving separator: arms are the germs' connector tails after the separator, high
  degree from the already-proven `four_le_degree_of_surviving`) and
  `Route8.TraceBasin.exists_envelope_of_traceSurvivingSeparator` (alternative (d) →
  decorated envelope with core = support, i.e. the `TraceSurvivingSeparator → HandoffProduced`
  bridge, with the high-degree conversion and absorbing-clause denial as read hypotheses).
  Both kernel-checked (`DecoratedHandoffEnvelope.lean`, `TraceBasinAlternatives.lean`).
  Obligation 4 DONE 2026-08-24 (user ruling: align (b) with realized exit (5)):
  `TraceResponseQuotient` is now the *realized* admissible compression of
  `def:admissible-rank-quotient` (nontrivial + target-complete against the basin's own piece +
  proper connected support + baseline glue + lexicographically smaller), and
  `TraceTargetCompleteCompression` is exactly `∃ retained` of it — one predicate, exit (5) ≡
  alternative (b) per `lem:typeA-reduced-silent-residual`; no second path. Refutation lemma
  `TraceBasin.compressibleSupport_of_traceResponseQuotient` ((b) → `CompressibleSupport basin`,
  contradicted by `K .uncompressible`). Route8Residual + SpineVocabulary build; probe confirms
  `typeAExitFiveClosed`'s destructuring still elaborates. LOUD REGRESSION (expected, per the
  correction): `route8SmallCoreExitRow` ([116], `lem:typeA-one-terminal-collapse`) constructs the
  (b)-arm with the old 3-conjunct shape (`refine ⟨retained, ?_, ?_, ?_⟩` proving completeness
  against the full reading only); it must now supply the realization clauses — that repair
  belongs to [116]'s own label. `typeAExitFiveDichotomy` merely states the predicate and is
  unaffected; the vocabulary Holds are schemas and elaborate.
  Obligation 1 DONE 2026-08-24: the Q1 semantic step (`VisibleEntryQuotient.lean`, builds) —
  `VisibleFourUnpeeledPackage.witnessOfPairTargetDefect` (a target-defective origin pair yields
  the exit-(4) witness at the pair's own selected visible unpeeled load, via `CanonicalMember.q1`)
  and `exists_witness_or_pairwise_targetComplete` (`lem:typeA-unpeeled-visible-routing`'s Q1
  dichotomy after exits (1)-(3): witness, or every origin pair is target-complete — the
  identification entering exits (5)-(7)). Remaining for the visible lane: discharging the
  pairwise-target-complete branch through the realized-compression/enlargement/separator
  machinery (shared with the fact-2 producer). Remaining on the [86] map: obligation 2 only
  (the Q2 silent-basin analog).
  Obligation 2 DONE 2026-08-24: the Q2 semantic step (`ExitFourFamily.lean`, builds) —
  `unpeeledExcess_subset_unpeeledLoads`, `witnessOfExcessTargetDefect` (a target-defective
  excess basin yields the exit-(4) witness at a residual excess load via `CanonicalMember.q2`),
  and `exists_witness_or_excess_targetComplete` (`lem:typeA-unpeeled-silent-routing`'s
  dichotomy: witness, or the basin identification is target-complete — exits (5)-(8)).
  ALL FIVE [86] OBLIGATIONS ARE NOW CLOSED. Remaining to assemble the `typeAExclusion`
  producer row: (i) derive the Q2 structural hypotheses at a concrete piece (excess-basin
  subset/connectivity-through-receiver/properness); (ii) discharge the two target-complete
  lanes (visible pairwise and silent basin) through the realized-compression (obligation 4),
  enlargement (exit 6 closures), and separator (obligation 5) machinery; (iii) the factOnly
  row reading `K .selection`, `K .returnAvoidance`, `K .uncompressible`,
  `K .replacementExclusion`, `K .typeAReceiverRouting`, `K .cubicBaseline`.
  Assembly item (i) DONE 2026-08-24: the Q2 structural clauses are theorems
  (`ExitFourFamily.lean`, builds): `traceSeed_subset_support`, `excessTraceSupport_subset`
  (receiver + excess loads + trace seeds all inside the support),
  `excessTraceSupport_proper`, and `excessTraceSupport_connectedOn` (every basin vertex walks
  to the receiver along its trace or the trace's tail; pairs join through the receiver via
  `Walk.bypass`). The Q2 dichotomy's hypotheses are now all derivable at a concrete piece from
  `receiver ∈ piece` and the piece's properness. Remaining: assembly items (ii) target-complete
  lane discharges and (iii) the producer row.
  Item (ii.a) DONE 2026-08-24: `ExitFour.germOfReturn` (`ExitFourFamily.lean`, builds) — every
  receiver-entry return with first entry ≠ receiver is a rooted outside-connector germ
  (`def:typeA-continuation-classes`' Γ rooted at w); all `RootedGerm` fields read off the
  return's structure (port adjacency, composite simplicity, connector-outside interior).
  This is the shared entry point of the continuation machinery for both target-complete lane
  discharges and the fact-2 producer. Next in (ii): the Separation/SwitchReading construction
  from two distinct germs (switch support + registered readings + descent), then the lane
  routing theorems.
  Item (ii.b1) DONE 2026-08-24 (`DecoratedHandoffEnvelope.lean`, builds): germ-union walks
  (`RootedGerm.exists_walk_to_receiver`, `receiver_mem_path`, `germUnion_connectedOn`) and the
  separation constructor `exists_separation_of_ne` (separator + prefix decomposition from the
  finiteness lemma; readings = the atom's own piece registered against the generated
  certificate); `exists_envelope_of_highDegree` factored out of the surviving-separator
  envelope so a cut-boundary (degree ≥ 4) separator produces the envelope without a reading.
  BLOCKING FORMULA (per `def:target-complete-compression`): at each lane's target-complete
  identification the paper's exit-(5) event IS the realized `X'` of `lem:replacement`
  ((i) profile inclusion, (ii) same boundary degrees, (iii) no internal target cycle,
  (iv) internal min degree 3, (v) strictly smaller); producing that `X'` from the concrete
  identification is the one step not yet in Lean — consumed identically by the [86] visible
  and silent lanes, by [116]'s collapse (b)-arm, and by fact 2/fact 4 of [123].
  Item (ii.c) silent lane DONE 2026-08-24 (all build): `not_traceDelocalization` ((c) refuted
  through `Delocalization.localize` against replacement exclusion + minimality),
  `exists_witness_of_traceLocalTargetDefect` ((a) → Q3 exit-(4) witness at ∅),
  `targetCompleteMinimal_of_refutations`, `not_traceSurvivingSeparator_of_noEnvelope`,
  `silentExcess_subset_routedLoads`, `exists_witness_or_route8Entry`, and
  `exists_witness_or_forall_route8Entry` (`lem:typeA-reduced-silent-residual` at the whole
  silent excess) — all in `TraceBasinAlternatives.lean`. Also DONE:
  `card_le_scaled_deficiency_of_no_saturated` (`TypeADischarge.lean` — the unsaturated case of
  `lem:density-mersenne` from zero surplus + total routing) and
  `visibleFourUnpeeledAt_of_not_silentFirst` (`Route8Deficit.lean` — ¬SilentFirst yields the
  overloaded-port state at ∅). The [86] trichotomy now assembles for the unsaturated and
  silent-saturated cases and the visible defect case; the SINGLE remaining branch is the
  visible pairwise-target-complete case. DEVIATION IDENTIFIED 2026-08-24 (supersedes the
  BLOCKING FORMULA note): the port never *constructs* quotients or realizations — the framework
  pattern (Branch D [31]-[45], nodes [130]-[132]) is (i) case classically on the EXISTENCE of a
  `DeclaredQuotient`/`AttemptedQuotient` (the ∃-side arrives with its representative fields and
  is discharged by `DeclaredQuotient.localize` + `K .replacementExclusion`/selection minimality —
  see `blockerSeparation_of_reducing`, `delocalizationScopeDichotomy`, `globalBarrierRow`), and
  (ii) in the ¬∃ case the coordinates are admissibly distinct and the paper CONSTRUCTS the
  distinguishing outside context from the actual data — the prepared substrate is
  `BoundariedResponseWalkAssembly` (AtomOwnedWalk.inPiece / ContextEntryWalk.inContext with
  length preservation) + `TypeAVisibleResponseCoordinate`/`Assembly` (selectedPieceChannel,
  selectedContextConnector) + `CommonPortReturnCycle` + `lem:typeA-port-return` (bridgeless
  ports carry anchored returns) + `lem:typeA-spectral-pressure` band arithmetic. NEXT
  CONSTRUCTION (the semantic Q1 step, `VisibleEntryQuotient.lean`'s stated purpose): cycles in
  `glue(reading, context)` assembled from a piece channel + a context connector + the port
  crossing; evaluate `HasCycleWithLength` on the glued object by length arithmetic; the
  distinguishing context for an injective (distinct-D1) pair comes from the actual outside's
  anchored return, making the pair target-defective → Q1 witness; the collision pair dies by
  the exit-(1)/(2) cycle arithmetic. Then: fact-2 producer (overload → witness at every
  unified component), [116] `route8SmallCoreExitRow` repair (same calculus: its (b)-arm becomes
  the ∃-DeclaredQuotient case discharged by localize, or the constructed-defect (a)-arm), and
  [123] facts 1/3/4/5 assembly on top.
  Semantic-step units G1/G2 DONE 2026-08-24 (`GluedCrossingCycle.lean`, new module, builds):
  `pieceHom`/`contextHom` (the two sides map into the gluing),
  `hasCycleWithLength_glue_of_crossing` (a piece path and a context path between the same two
  boundary labels close a crossing cycle of the gluing of summed length — interiors disjoint by
  the glued carrier), the synthetic `pathContext` (a bare path of chosen length `k+1` between
  two labels, all other labels isolated — the manuscript's compatible outside context), its
  canonical `PathContext.walk` with support/length/isPath/boundary lemmas, and
  `hasCycleWithLength_glue_pathContext` (positive direction of the synthetic-context
  evaluation). NEXT: G3 — the converse cycle classification of `glue piece pathContext`
  (every accepted cycle is piece-internal or crosses through the whole synthetic path,
  yielding a piece path of complementary length), then G4 — the spectral separation choosing
  `k` from the D1 data (`lem:typeA-spectral-pressure`) to produce `Response.TargetDefect` at
  an injective visible pair, closing `lem:typeA-visible-entry`'s remaining branch, then the
  fact-2 producer, [116] repair, and [123] facts.
  G3 DESIGN (for continuation): classify cycles of `glue piece (pathContext first second k)`,
  k ≥ 1. Case A: the cycle avoids every chain vertex — with k ≥ 1 the synthetic rel owns no
  boundary-boundary pair, so every edge is piece-owned and the cycle maps into `piece.pack`.
  Case B: it meets a chain vertex — each chain vertex's glue neighbours are exactly its ≤ 2
  chain-rel neighbours (PieceOwns impossible at `.inr (.inr _)`; ContextOwns reduces via
  `fromRel_adj` + `pathContextList` getElem lemmas: [0] = inl first, [j+1] = inr j, [k+1] =
  inl second), so `rotate` at the chain vertex + trail-ness forces the whole chain as a
  segment, leaving a piece-side walk `second ⤳ first` of length cycleLen − (k+1). Conclusion
  `hasCycleWithLength_glue_pathContext_iff`: Target on the glued reading ↔ piece-internal
  accepted cycle ∨ ∃ piece path first⤳second with length + (k+1) accepted. G4 then chooses k
  (spectral bands) to separate two readings' path spectra → `Response.TargetDefect` → Q1
  witness at the injective pair; the collision pair dies by exit-(1)/(2) arithmetic
  (`hasCycleWithLength_of_commonPortReturns`, `not_shiftedCycleLength_of_returnLengthSets_disjoint`).
  G3 sub-units DONE 2026-08-24 (`GluedCrossingCycle.lean`, builds): chain index layout
  (`pathContextList_getElem_zero/succ/last`), `pathContextList_position_unique`,
  `pathContextRel_chain_iff`, `glue_adj_chain` (a chain vertex's glue neighbourhood is exactly
  its predecessor/successor), `pathContextRel_mem_chain` (k ≥ 1 → every synthetic relation
  touches the chain), and `exists_pieceWalk_of_avoids_chain` (a chain-free glued walk lifts to
  the atom side, length preserved). REMAINING for G3: (g1) `chain_walk_length` — fuel
  induction: a glued PATH from chain vertex j to `.inl second` avoiding its predecessor has
  length k − j and chain-only support; (g2) the cycle-arc extraction: rotate the accepted
  cycle at `.inl first` (both endpoint labels are on it: a met chain vertex propagates both
  its edges by `glue_adj_chain` + `IsCycle.snd_ne_penultimate` after `rotate`), split by
  `takeUntil`/`dropUntil`/`take_spec`; the arc through the chain is forced by (g1) to be the
  whole chain (length k+1), the other arc avoids the chain (interior vertices visited once,
  `IsCycle.count_support_of_mem`) and lifts by `exists_pieceWalk_of_avoids_chain` to a piece
  path `second ⤳ first` of length cycleLen − (k+1). Conclusion:
  `hasCycleWithLength_glue_pathContext_iff`.
  (g1)+(g2a) DONE 2026-08-24 (`GluedCrossingCycle.lean`, builds): `chain_walk_length` (forced
  chain traversal, now with the coverage clause: support contains every chain vertex ≥ j),
  `cycle_neighbours_of_chain` (rotate + snd/penultimate + `glue_adj_chain` force the
  predecessor/successor pair onto the cycle), `first_label_mem_of_chain_mem`,
  `second_label_mem_of_chain_mem`, `chain_zero_mem_of_chain_mem`,
  `endpoint_labels_mem_of_chain_mem`, and the strengthened
  `exists_pieceWalk_of_avoids_chain` (support-map equation added). NEXT (g2b): `chainArc_of_path`
  — a glued path `.inl first ⤳ .inl second` through chain-0 splits at chain-0 into a single
  edge (penultimate ∈ {A, l[2]}, the l[2] case killed by nodup-append disjointness against
  q2.snd, then `IsPath.getVert_injOn` gives q1.length = 1) and the forced chain (q2 via
  `chain_walk_length`), so p.length = k+1 and p covers the chain; then the final
  classification: rotate the cycle at `.inl first`, split at `.inl second` (`take_spec`,
  `IsCycle.isPath_takeUntil`, `isPath_of_append_right`, `not_nil_of_ne`), the chain-carrying
  arc is `chainArc_of_path` (applied to p1 or p2.reverse), the other arc avoids the chain
  (cycle count_support_of_mem + coverage) and lifts via `exists_pieceWalk_of_avoids_chain`.
  `chainArc_of_path` DONE 2026-08-24 (builds): the split at chain-0 with the single-edge
  identification (penultimate = first label via nodup-append pairwise-ne + q2.snd upper
  neighbour; `IsPath.getVert_injOn` closes q1.length = 1) and `chain_walk_length` for the
  forced chain; conclusion p.length = k+1 + full chain coverage. Lift lemma being extended
  with the edges-map clause for the chain-free cycle case; then the final classification
  theorem, then G4.
  G3 COMPLETE 2026-08-24 (`GluedCrossingCycle.lean`, builds): `cycle_classify` — every cycle
  of `glue piece (pathContext first second k)` (k ≥ 1) either avoids the chain and lifts to an
  atom-side cycle of equal length (`exists_pieceCycle_of_avoids_chain`), or crosses it and
  splits (rotate at the first label, `take_spec` at the second) into the full port path
  (`chainArc_of_path`) and a piece-side PATH `second ⤳ first` with length + (k+1) = cycle
  length (one-side via the cycle tail's nodup-append pairwise-ne; lift via the strengthened
  `exists_pieceWalk_of_avoids_chain`). NEXT: the Target-level iff wrapper
  (`hasCycleWithLength_glue_pathContext_iff`), then G4 (spectral choice of k → TargetDefect at
  an injective visible pair), then `lem:typeA-visible-entry` assembly = fact-2 content.
  Iff wrapper + G4 wrappers DONE 2026-08-24 (builds): `hasCycleWithLength_glue_pathContext_iff`
  (the synthetic-context evaluation of the cycle target — accepted glued cycle ⟺ atom-side
  accepted cycle ∨ accepted complementary-length label path), `targetDefect_of_pathContext`,
  and `targetDefect_of_spectra` (spectral separation form: a left path of accepted
  complementary length + right internal safety + right spectrum avoidance ⟹
  `Response.TargetDefect`). (α) DONE 2026-08-24 (`Route8Residual.lean`, builds):
  `retainedBasinPiece_decode_injective` and `hasCycleWithLength_of_retainedBasinPiece_cycle`
  (an accepted internal cycle of any retained reading maps through the injective `pieceDecode`
  hom into the object — right-safety from `K .selection`), plus the walk-transfer pair
  `pieceEncode`/`pieceDecode_pieceEncode`/`pieceEncode_of_mem_cutBoundary`,
  `exists_retainedBasinPiece_walk_of_channel`, `exists_retainedBasinPiece_path_of_channel`
  (a support channel is a path of every retained reading that keeps its vertices, length
  preserved), `exists_object_path_of_retainedBasinPiece_path` (the converse decode transfer),
  and `ExitFour.exists_visibleResponsePiece_channelPath` (`ExitFourFamily.lean`: the selected
  channel is a path of its own visible response piece between the entry and receiver labels).
  VISIBLE-LANE RESOLUTION 2026-08-24 (supersedes the (β)-spectral-choice step): the ratified
  selected chain ([101]–[107], `SelectedNoExitSixWith`'s `exitFiveAt`) routes the visible
  no-witness state PER LOAD through the load's own trace basin — exit (5) is the realized
  `TraceTargetCompleteCompression` at `select? load`, exit (6) is `TraceDelocalization`, exit
  (7) the envelope — identically to the silent lane; no pair-response spectral separation is
  required for the exhaustiveness of `lem:typeA-unpeeled-visible-routing` at the collection
  (`rem:unified-covers-exit4` keeps target-defect supports in `X̃`, and the chain's
  `typeAExitSevenFree` arm admits route-8 residual entries reached from the visible branch).
  DONE 2026-08-24: `VisibleFourUnpeeledPackage.exists_witness_or_forall_route8Entry`
  (`VisibleEntryQuotient.lean`, builds) — for an overloaded port at any peeling: an exit-(4)
  witness at a selected visible unpeeled load, or every selected visible unpeeled load is a
  `Route8Entry`; per-load routing via `TraceBasin.exists_witness_or_route8Entry` with the
  ∅-witness repackaged at the current peeling. REMAINING: reconcile the two unproduced Holds
  (`typeAExclusion` idx 343 arm 2's `SilentFirst` conjunct; `route8VisibleExitFourRouting`
  idx 338's unconditional per-port witness) with this ratified dichotomy — the chain admits
  visible route-8 entries, so both Holds and the descent row's visible-peel step must carry
  the witness-or-route8 dichotomy — then the [86] row, [116]'s repair, and [123]'s facts.
  [86] PRODUCER DONE 2026-08-24: `K .typeAExclusion`'s Holds arm 2 repaired (the `SilentFirst`
  gate is deleted; the residual arm now states, per saturated receiver, route-8 entries for
  the silent excess AND for the selected visible unpeeled loads of every overloaded port at
  ∅ — `rem:unified-covers-exit4`'s collection, with the paper's trichotomy sentence intact;
  vocabulary builds, 8730 jobs), and `typeAExclusionRow` is written (`SpineRows.lean`, before
  the descent row): a `factOnly` row reading `K .selection`, `K .uncompressible`,
  `K .replacementExclusion`, `K .cubicBaseline`; witness arm and handoff arm by classical
  case; the residual arm inlines the per-load routing
  (`TraceBasin.exists_witness_or_route8Entry`) with the surviving-separator case discharged
  through `exists_envelope_of_traceSurvivingSeparator` (high-degree conversion from the cubic
  baseline; the label-collision absorbing clause denied by
  `hasCycleWithLength_of_labelCollision` against target avoidance and
  `degenerateClosureRejected`). The row elaborates with zero errors in its region (the file's
  remaining errors are the user's WIP block at 3279–4247 and the known [116]
  `route8SmallCoreExitRow` (b)-arm regression).
  DEVIATION FOUND AND REVERTED 2026-08-24 (supersedes the blocking-formula note above): the
  block was not the paper's — it was this session's collapse of the two (b)-predicates into
  one ("one predicate, exit (5) ≡ alternative (b), no second path").  `git show HEAD` recovers
  the ratified two-predicate architecture, and `def:typeA-trace-basin` (b) verbatim is the
  *plain* nontrivial target-complete response quotient, with the realized case a subcase
  remark: `TraceTargetCompleteCompression` is the realized exit-(5) datum (TC against the
  basin piece + proper + baseline glue + lexicographically smaller), cased at the [103]
  decision and closed at [104] against `K .uncompressible`; `TraceResponseQuotient` is the
  plain (b)-quotient (retained reading vs the full declared reading), proven by [116]'s
  parity argument and negated in `TargetCompleteMinimal`.  Plain (b) is CASED on the branch,
  never refuted from the invariants.  Executed: the (b)-block of `Route8Residual.lean` is
  reverted to HEAD verbatim and the session's `compressibleSupport_of_traceResponseQuotient`
  is deleted; `targetCompleteMinimal_of_refutations` / `exists_witness_or_route8Entry` /
  both `exists_witness_or_forall_route8Entry` versions now take the cased `noQuotient`
  hypothesis (conditional on `select?`) instead of refuting (b) via uncompressibility;
  `K .typeAExclusion`'s arm 2 is the paper's per-load conclusion of
  `lem:typeA-reduced-silent-residual` — `Route8Entry ∨` the exit-(5) plain quotient at the
  selected basin — and `typeAExclusionRow` cases it classically (the `K .uncompressible`
  read is dropped from its manifest).  RESULT: full `SpineRows.lean` elaboration now reports
  ONLY the user's WIP-block errors (3279–4247); the [116] `route8SmallCoreExitRow` errors are
  gone — its original proof type-checks against the restored plain (b).  [116] IS REPAIRED.
  The fact-2 producer question dissolves the same way: the visible no-witness state is the
  cased per-load dichotomy, not an unconditional-witness obligation.
  FACT-2 PRODUCER DONE 2026-08-24: `K .route8VisibleExitFourRouting`'s Holds is repaired to
  `lem:typeA-unpeeled-visible-routing`'s collection form — per overloaded port, the exit-(4)
  witness at the current peeling OR, per selected visible unpeeled load, `Route8Entry ∨` the
  exit-(5) plain quotient at the selected basin — and `route8VisibleRoutingRow` is written
  (`SpineRows.lean`, before the descent row; Requires `K .selection`,
  `K .replacementExclusion`, `K .cubicBaseline`), mirroring `typeAExclusionRow`: witness arm
  classical, exit (7) refuted by the collection's own `¬ HandoffProduced` filter membership,
  per-load routing with the ∅-witness repackaged at `peeled`.  Vocabulary builds (8730 jobs);
  the row elaborates with zero errors.  Assembly.lean consumes the key only as a
  `FactKeys.Has` wiring instance, so it is untouched.
  FIRST DOWNSTREAM FAILURE (the descent row, `route8PeelingDescentRow`, one open goal at its
  `case pos.inr`): its overloaded branch now splits on the dichotomy; the witness arm
  compiles through the entire peel machinery unchanged; the settled arm — an overloaded port
  whose selected visible unpeeled loads are all route-8/quotient states — must still produce
  `∃ final, StageOutcome …` under `StageRate`.  No peel is available (peels need a witness)
  and `TrueEntryAt` ranges over `route8UnifiedEntries`, the SILENT census, which does not
  index the settled loads.  The repair is the census/burden label of [123], not fact 2's:
  count unpaid visible route-8 loads as indexed entries — justified by the
  silence-independent core inequality `Σ_w (L(w) − c(w)) ≥ 4·D_A(X)` of
  `lem:typeA-silent-excess-count` (silence is used there only to place unpaid loads, never in
  the count) and by `rem:unified-covers-exit4` ("the two are not distinguished at the level
  of net charge").  That change ripples through `Route8Census.entriesOfComponents`,
  `stage_burden`, and every Holds schema quantifying `silentExcess`-based entries
  (`Route8UnifiedNegative`, the entry census, [116]'s collapse), so it is its own label.
  CENSUS/BURDEN LABEL DONE 2026-08-24 (all kernel-checked; the full `SpineRows.lean`
  elaboration again reports ONLY the user's WIP-block errors):
  - `VisibleReceiverEntry.lean`: the silence-free reduced count —
    `one_add_routedLoad_le_excessBasinReduced` (`1 + L ≤ |E^{P₄}| + |P₄∩ℒ| + s·q`, NO port
    hypothesis: the manuscript's displayed count never uses silence),
    `card_le_sum_excessBasinReduced_add_positiveDeficiency`, `excessBasinReduced_subset`
    (`E^{P₄} ⊆ E ∖ P₄`), and `silentExcess_eq_excessBasin` (`𝒰(w) = E(w)` under the port
    bound — `lem:typeA-silent-excess-count`'s own "every unpaid routed vertex is silent").
    The dead silent-reduced machinery is DELETED (no compatibility path).
  - `Route8Census.lean`: `entries`/`entriesOfComponents` index the excess basin `E(w)`
    (`def:typeA-excess-basin`; the paper's `𝒰(w)` on silent-first pieces;
    `rem:unified-covers-exit4` for the unified collection).
  - `Route8Pressure.lean`: `stage_burden` DROPS `reducedPorts` (silence-free at every
    stage); `sum_excessBasin_sdiff_le_card_peeledEntries`; `PeelChain.visible` and
    `visibleLoadIndices` DELETED — every peel is a two-carrier target-defect entry
    (`PeelChain.cons`), exactly `thm:large-budget-route8-only`'s procedure.
  - `Route8Deficit.lean`: `excessMass`/`card_entries`/`sum_excessMass` over `E(w)`;
    `card_piece_le` converts through `𝒰 = E` under `SilentClassification`.
  - `route8PeelingDescentRow` REWRITTEN to the paper's procedure verbatim: rate? no →
    failed stage; yes → silence-free burden → `exists_twoCarrierEntry_staged` → defect?
    peel (`PeelChain.cons`, measure `|Ξ̃ ∖ chain|`) : true-entry survivor.  The
    visible-peel superstructure and the `K .route8VisibleExitFourRouting` read are REMOVED
    from the row (the fact stays produced at its own label for the [123] classification;
    Assembly's `FactKeys.Has` binder is unaffected).  THE SETTLED-ARM OBLIGATION IS GONE:
    unpaid visible route-8/quotient loads are census entries and the burden covers them.
  - Census-consumer rows repaired at their own labels: `route8CensusRow` (excess-stated
    `entryCount` + the `𝒰 = E` bridge under `Route8Survives`' silent-first),
    `route8TrueTwoCarrierEntryRow` and `route8TerminalNoGoRow` (excess `indexSpec` + the
    per-receiver conversion feeding the unchanged silent-quantified `[114]`/`[115]`
    Holds), and the two deletion-witness `loadRouted` derivations (one unwrap:
    `mem_entries` now yields `E(w)`-membership directly).
  [123] REMAINING-PRODUCER GATE ANALYSIS 2026-08-24 (verified against live Lean; the tree is
  green — vocabulary 8730 jobs, `SpineRows` elaboration shows only the user's WIP block):
  the four outstanding items and their exact gates, after this session's groundwork
  ([86] trichotomy, fact-2 dichotomy, excess census + silence-free burden + paper-exact
  descent):
  1. `K .route8UnifiedEntryCensus` (`route8UnifiedEntryCensusRow`): the per-entry
     trichotomy (select? ∧ (minimal ∨ witness ∨ cased quotient)) is fully provable with the
     [86]-row recipe, BUT the schema `Route8UnifiedEntryFacts` is positionally consumed by
     `route8StageOutcomeDichotomy`'s survivor arm, which spends its `2 ≤ entry.alpha`
     clause into `route8UnifiedTrueTwoCarrierEntry` for the [124] no-go (`alphaAtLeast` →
     `coreNonempty`).  VERIFIED 2026-08-24: α is NOT the gate — the [114] cut-parity
     proof lifts verbatim to unified entries (its only external input,
     `basin ⊆ piece`, comes from `select?_traceComplete` at the entry's own
     `selectedEq`; the rest is per-entry graph reasoning through
     `presented.two_le_card_car`), and the minimal-arm α then follows from
     `two_le_essentialCore_card_of_alternatives_refuted` with
     `Alternatives := ∃ retained, TraceResponseQuotient …`, the [116]-row's
     crossing-callback, and `minimal`'s own ¬(b) clause as `refuted`.  The REAL
     gate: every provable schema must carry the cased exit-(5) quotient arm
     (`minimal ∨ witness ∨ quotient`, as in [86]/fact-2), and the green
     `route8StageOutcomeDichotomy` → `route8UnifiedTerminalNoGoRow` chain has
     no decision for a quotient-carrying terminal `TrueEntryAt` (no witness to
     peel, no α guarantee, no minimality for the [124] no-go) — the same
     quotient-terminal gap as item 4.
  2. `K .route8PiecesClassified` (`thm:branch-kill`): DONE 2026-08-24 — the Holds'
     residual-profile arm is aligned with what `[86]` actually produces (per
     saturated receiver, every silent-excess load and every overloaded-port
     selected visible unpeeled load is `Route8Entry` ∨ the cased exit-(5)
     plain quotient at the selected basin; the old SilentFirst-gated profile
     is deleted; vocabulary builds green, key unconsumed so no consumer
     breaks). The zero-surplus arm of the producer is now one read of
     `K .typeAExclusion`. The positive-surplus arm remains gated:
     VERIFIED 2026-08-24 against the three `selectedTypeBRoute8Continuation`
     call sites in Assembly.lean (1688; calls at 1783/1849/1862+) —
     `K .typeBDisjointLedger` is committed only on the `typeBExclusionDichotomy`
     arms; the `fanCertificateDichotomy .right` residual arm reaches the
     route-8 branch WITHOUT it, so the ∀-piece hygiene pair
     (`lem:typeB-postledger-core-hygiene` / `prop:typeB-bridge-reduction`)
     is genuinely absent from the common prefix and must be produced
     upstream of `fanCertificateDichotomy` (the active TypeBMaximalCompletion
     lane). No [123]-side edit can supply it.
  3. `K .route8UnifiedDeficit` (`lem:typeA-unified-deficit`): per-piece over the canonical
     decomposition, cases (i) unified and (ii) nonnegative are Nat-trivial; (iii)
     negative-positive-surplus and (iv) negative-zero-surplus-handoff both need their
     payment into the `2·F·s·T` slack through the same hygiene pair ((iii) via
     `typeBBridgeMass`'s conditional clause, (iv) via
     `envelopeFamilyNegativePart_le_degreeSurplus`'s routes/unsaturated/coverage
     hypotheses) — the same Type B gate as item 2.
  4. The failed-stage closure (`selectedRouteEightStageClosure`) and the composed wiring
     (`selectedLargeBudgetPressureCensus` → the existing `selectedRouteEightCensus`): gated
     on 2 and 3, plus one structural fact the corrected calibration makes load-bearing: a
     terminal `TrueEntryAt` may carry the cased exit-(5) quotient (no witness, no
     α-guarantee — `lem:typeA-one-terminal-collapse`'s four-fold is consistent with (b) at
     α ≤ 1), and the paper parks exactly these in `Ξ_res` of `def:typeA-pressure-ledger`
     with the open-demand accounting (`cor:typeA-large-budget-closure-open-pressure`) — the
     [129]-side pressure machinery, not a per-entry no-go.  A widened survivor Holds or the
     pressure-ledger port is required before the dichotomy can decide quotient-carrying
     survivors.
  An attempted census-schema simplification (dropping the α-clause) was REVERTED in full
  after the consumer coupling surfaced — no unprovable row and no schema drift was left in
  the tree.


  SHARPENED 2026-08-24 (full verification against live Lean + the manuscript's [123] section):
  the dependency order inside [123] is `route8PiecesClassified` → `route8UnifiedDeficit` →
  `route8UnifiedEntryCensus` → closure.  (α) The FIRST unproved formula for the whole cluster is
  `thm:branch-kill`(b)'s positive-surplus arm: ∀ piece ∈ canonicalPieces(R), NegativeNetCharge →
  0 < ambientSurplus → `BridgeResidualComponentAt object piece δ s` — i.e. the pair (routes:
  every δ-internal-degree vertex off `TypeBRefinedSupport.centres` trace-routes to an off-centre
  receiver; unsaturated: every off-centre receiver has `1 + restrictedLoad ≤ s·missingPorts`).
  Its manuscript proof is `lem:typeB-hybrid-B1` + `prop:typeB-bridge-reduction` (B2 holds outside
  the residual) — `lem:typeB-postledger-core-hygiene`'s lane, NOT derivable from
  `highCentreNormalForm` + baseline (checked: `unsaturated` is B2's own content).  The deficit
  fact needs it too: `typeBBridgeMass`'s clauses 2/3 (bridgeResidualMass_le_route8/_le_twice,
  committed and green) are conditional on exactly this pair at every non-route-8 piece, and the
  failed-stage closure quotes `thm:branch-kill` in the manuscript's own proof of
  `thm:large-budget-route8-only`.  (β) The zero-surplus arm is now one read of
  `K .typeAExclusion` (schema aligned, green).  (γ) The census schema's ¬quotient clauses (in
  BOTH arms, via `TargetCompleteMinimal` and the defect-arm conjunct) do NOT match the
  manuscript: the paper never proves per-entry ¬(b) — `def:typeA-pressure-ledger` puts
  non-(a) failures through the profile demand records (`lem:typeA-profile-pressure-dependence-routing`
  is CONDITIONAL on a functional admissible rank quotient; its ¬∃-side stays as counted
  P_prof units) and closes NUMERICALLY (P_open = o(|R|), window-blocker audit).  Under the
  ratified two-predicate calibration ([104] ruling: never refute the plain quotient from
  invariants) the consumer-coupled `Route8UnifiedEntryFacts` is therefore a pre-existing
  DEVIATION: the paper-exact schema is the [86]-arm trichotomy (minimal ∧ ¬witness ∨
  (a)-defect ∧ witness ∨ cased quotient at the selected basin), with the quotient/res class
  carried into the pressure accounting, and `route8StageOutcomeDichotomy`/[124] repaired to
  the 3-arm form.  All other census ingredients assemble from committed facts: α ≥ 2 via
  `two_le_essentialCore_card_of_alternatives_refuted` (+ the [116] crossing callback and each
  arm's own refuted clauses), select? via `exists_select?_eq_some_of_mem_routedLoads`,
  ¬(c) via `not_traceDelocalization` (K .replacementExclusion + K .selection), ¬(d) via
  `not_traceSurvivingSeparator_of_noEnvelope` + the collection's ¬HandoffProduced, the
  (a)-witness via `exists_witness_of_traceLocalTargetDefect`.

  FIX LANDED 2026-08-24 (the (α)-formula's carrier): key `typeBBridgeReduction` (idx 344, all
  six vocabulary sites) + producer `typeBBridgeReductionRow` (SpineRows.lean:4142; Requires
  `K .selection`, `K .uncompressible`, `K .remainderNormalized` — all on the route-8 branch's
  common prefix, so the [123] frontier can run it on any arm).  Holds = the ∀-piece
  contrapositive of `prop:typeB-bridge-reduction`/`lem:typeB-bridge-to-overlap`: every negative
  positive-surplus canonical piece carries the B2 disjoint ledger at its own high centres
  (exact augmented refinement + strictly negative remaining core + post-ledger hygiene at every
  remaining component + B2(d) grouped envelope coverage) or a minimal overlap obstruction.
  Proof: `b2_or_overlap` per piece; the choice arm assembles the `DisjointLedger` and refutes a
  clean core via `nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg` against the
  piece's own negativity — the same engine as `typeBExclusionDichotomy`, made ∀-piece.
  Vocabulary builds green (8730 jobs); the row elaborates with zero errors in its range
  (4142–4317).  SCOPE NOTE: this supplies the classification's Type B input and the deficit's
  piece dichotomy; the residual pieces' NUMERIC mass conversion (obstruction/negative-core
  mass₀ ≤ F·s·σ) still routes through the residual-mass lemmas (`envelopeNegativePart_le` per
  centre is unconditional; the piece-level conversion is the obstruction lane's remaining
  step).

  CLASSIFICATION PRODUCER LANDED 2026-08-24: `route8PiecesClassifiedRow`
  (SpineRows.lean:6269; Requires exactly `K .typeAExclusion`,
  `K .typeBBridgeReduction`; zero errors in the full-file check).
  `Route8Deficit.PieceClassification`'s positive arm is parameterized
  (`Bridge`) and the vocabulary instantiates it at the paper's residual
  dichotomy; the hard-coded flat pair is deleted (`Route8Deficit` and the
  vocabulary build).  DEFICIT GATE RE-SHARPENED against the manuscript's
  `lem:typeB-bridge-deficit-bound` / `lem:typeB-bridge-with-route8-core` /
  `prop:typeB-bridge-sublinear` (tex 14275–14570): the Lean mass lane for a
  negative positive-surplus piece is the FLAT pair (`bridgeDeficitBound`'s
  routes/unsaturated at piece ∖ centres) — provable when no off-centre
  receiver is saturated; a saturated off-centre receiver is the paper's
  fan/handoff lane, and `lem:typeB-bridge-with-route8-core` then extracts the
  route-8 non-window sub-cores into `D_A`.  The unified deficit's first
  unproved formula is therefore: at every negative positive-surplus canonical
  piece, `piece.card + s·σ ≤ s·def⁺ + F·s·σ` — via the flat pair, or via the
  centre-envelope bound with the saturated sub-core deficit extracted (its
  Lean carrier does not exist yet; `card_le_scaled_deficiency_add_absorbed`
  is the absorbed-core half).

  DEFICIT σ>0 ARM — CORRECTED ANALYSIS 2026-08-24 (supersedes the earlier note in this
  block; its "saturated component is necessary" inference was WRONG — it conflated the
  component-measured and piece-measured deficiencies).  Verified against the kernel-checked
  partition identities (`DisjointLedger.augmentedLedger_partition`,
  `selectedEntryPayment₂_eq`, `refinedAugmentedLedgerPartition`,
  `refinedComponent_positiveDeficiency_supplied`):

  (1) EXACT REDUCTION (kernel-clean, no hypotheses beyond the ledger arm of
  `K .typeBBridgeReduction`): with `demands = centres(P)`,
  `augLedger(P) = s·def⁺(P) − |P| − s·σ(P) − |H|` (σ(P) = Σ_H(deg−θ) by
  `sum_centres_surplus`; `positiveDeficiency` is the exact truncated sum), and the partition
  plus `payment₂ ≥ 0` plus `coreCharge ≥ −1` at centres give
  `massB(P) = |P| + s·σ − s·def⁺ ≤ − Σ_{remainingCore} scaledCoreCharge(P-measured)`.
  So the whole `thm:branch-kill`(b) mass bound `massB ≤ F·s·σ` reduces to ONE formula:
  `Σ_{remainingCore} scaledCoreCharge ≥ −F·s·σ(P)`.

  (2) The core's negativity has TWO sources, per the manuscript's own
  `lem:typeB-bridge-deficit-bound` proof: (a) removal-created boundary deficiency — an
  unsaturated component C has `|C| ≤ s·def⁺_C(C)` (discharge) but the charge uses the
  P-measured `def⁺_P(C)`, smaller by exactly the C-to-removed edges; the paper pays this
  through the ledger carriers (`def:typeB-ledger-carriers` — in Lean
  `refinedComponent_positiveDeficiency_supplied`: `s·def⁺_C(C) ≤ componentReserve +
  windowStubReserve`) and the refined per-centre count ((1) in the manuscript:
  fan neighbours credit +¾, closed neighbours −¼, total per centre ≤ 8·t_h);
  (b) genuinely saturated components — resolved in the manuscript by the exit-(4) peeling
  loop to unsaturation, with the peeled −¼ mass and any route-8 sub-profile "continuing in
  Part IX" (`lem:typeB-bridge-with-route8-core` extracts `D_A(𝒜_X)`), under
  `prop:typeB-bridge-sublinear`'s hypothesis that the cores are profile-free.

  NEXT CONSTRUCTION (the deficit's remaining carrier): the ledger-form
  `lem:typeB-bridge-deficit-bound` — a generic theorem bounding
  `Σ_{remainingCore} scaledCoreCharge` below by `−F·s·σ(P)` from the entry payments'
  refined lower bounds (`positive_entryPayment₂_eq`, `sum_centreAllowance_le` shapes) and
  the component reserve accounting, with the saturated/profile case as its stated
  hypothesis exactly as `prop:typeB-bridge-sublinear` states it; the discharge of that
  hypothesis on this branch is the manuscript's own branch-position claim ("route-8 cores
  continue in Part IX") and stays loud until its Part IX receiver exists.

  DEFICIT LANE WRITTEN 2026-08-24 (pending kernel check — the tree's dependency chain is
  currently blocked by concurrent sparse-lane WIP in `SurplusBlockers.lean`/
  `SparseEntropySandwich.lean`): (1) `TypeBSublinearHypotheses` (SpineVocabulary) — the
  `[113]`-tested form of `prop:typeB-bridge-sublinear`'s hypotheses: the flat off-centre
  pair at every negative positive-surplus canonical piece, and the grouped fan-assignment
  bundle (∃-characterized handoff family + centre family + absorbedAt/fanEnvelope data +
  coverage) at the negative zero-surplus handoff pieces; keys `typeBSublinearLedger`
  (idx 345) and `typeBSublinearResidual` (idx 346, the literal negation, [115]-pattern).
  (2) `typeBSublinearDichotomy` (SpineRows:6332) — classical Decision, no reads.
  (3) `route8UnifiedDeficitRow` (SpineRows:6377) — Requires exactly
  `K .typeBSublinearLedger`, `K .surplusAtOrBelow`; the executor is
  `lem:typeA-unified-deficit`'s proof verbatim: |R| summed over canonical pieces; unified
  members are the cleared deficit (definitional `route8Deficit` match); nonnegative pieces
  carry nothing; negative positive-surplus pieces pay through `bridgeDeficitBound` with the
  tested pair into surplus role 1; handoff pieces pay through
  `envelopeFamilyNegativePart_le_degreeSurplus` with the tested bundle into surplus role 2;
  `s·def⁺(R) ≤ s·|∂R|` by `positiveDeficiency_le_boundaryIncidence` + `card_supply`; both
  roles convert to the registered threshold by `K .surplusAtOrBelow` — exactly the fact's
  `2·F·s·T` slack.  The descent's `Requires` are unchanged; once this row kernel-checks,
  the [123] chain up to `route8StageOutcomeDichotomy` is producer-complete except the
  entry census.

  CENSUS LANE + COMPOSITION WRITTEN 2026-08-24 (validation pending — the tree is shared and
  the full-file check is queued behind the user's own builds): (4) census schema corrected to
  the paper-exact `def:typeA-unified-entries` form — the minimal arm's `¬ witness` conjunct
  was DEAD WEIGHT (the dichotomy consumer takes its no-witness datum from the descent
  survivor's `trueEntry_transport`, never from the census) and unprovable; dropped, with the
  one-token consumer repair (`routeEntry.1` → `routeEntry`); vocabulary builds green.
  (5) keys `route8QuotientFree` (idx 347) / `route8QuotientResidual` (idx 348) +
  `route8QuotientDichotomy` — the [113]-tested casing of the plain-(b) state per the [104]
  ruling; the residual arm is the manuscript's profile demand-record lane.
  (6) `route8UnifiedEntryCensusRow` — Requires exactly `K .route8QuotientFree`,
  `K .selection`, `K .replacementExclusion`, `K .cubicBaseline`; per entry: select? total via
  `exists_select?_eq_some_of_mem_routedLoads`, the (c)/(d) refutations via
  `not_traceDelocalization` / `not_traceSurvivingSeparator_of_noEnvelope` (the collection's
  own ¬HandoffProduced), the (a)-witness via `exists_witness_of_traceLocalTargetDefect`, and
  `α ≥ 2` on both arms via `entry.smallCoreCollapseFacts` with the [116] crossing-callback —
  whose constructed alternative is exactly the tested-refuted quotient — and parity from
  `presented.two_le_card_car` (basin ⊆ piece from `select?_traceComplete`).
  (7) `selectedLargeBudgetPressureCensus` DEFINED in Assembly: [86] → ∀-piece bridge
  reduction → branch-kill classification → tested sublinear hypotheses → deficit → tested
  quotient-freeness → census → fact 2 → `selectedRouteEightCensus` (descent → dichotomy →
  [124]); the two tested residual arms are held at the loud manuscript-lane continuations
  `selectedTypeBSublinearResidual` / `selectedRouteEightQuotientResidual`.
  FIXES APPLIED from the first check round: `cardSum` simp recursion → explicit calc;
  `smallCoreCollapseFacts`'s implicit crossing; `TypeBSublinearHypotheses` now elaborates
  under `open scoped Classical` so its sdiffs carry the same instances as
  `envelopeFamilyNegativePart_le_degreeSurplus`'s statement (the instance-mismatch root
  cause).  VALIDATED 2026-08-24 (low-priority full-file check, error set = exactly the 22
  pre-existing WIP-block lines): all six [123] producers/decisions and the repaired dichotomy
  elaborate with ZERO errors — the survivor path [123] → descent → dichotomy → [124]
  (`route8UnifiedTerminalNoGoRow`, Q5/deletion-witness no-go) is complete at the elaboration
  level; the kernel olean waits only on the user's [116]-region WIP block.  The two lane
  modules `DemandPartition` and `WindowAttachmentShadow` are kernel-checked (`lake build`,
  815 jobs).

  ¬RATE-ARM LANE STARTED 2026-08-24 (both files elaborate cleanly via `lake env lean`):
  `Graph/WindowAttachmentShadow.lean` — `def:typeA-window-attachment-shadow` generically
  (`forbiddenDistances`/`shadow` over the registered length predicate, the membership iffs,
  symmetry, and `accepted_of_mem_shadow` — the corridor-hit closure of
  `fig:exit4-p13-attachment-accounting`; `lem:typeA-singleton-shadow-table` is presentation
  arithmetic and is not restated).  `Graph/DemandPartition.lean` —
  `def:typeA-pressure-ledger`'s combinatorial core (`Partition` = Ξ₃ ⊔ Ξ₂ ⊔ Ξ_res with
  disjoint 3/2-incidence assignments, `externalDefect` = 𝖯_ext) and
  `lem:typeA-pressure-ledger-no-overcount` in both forms (`three_mul_add_two_mul_le`,
  `three_mul_card_le`).  The graph-side instantiation (tokens over the census defect arm,
  their `K(𝔱)` incidence sets via the crossing-parity machinery, and the absorber audit)
  is the lane's remaining work, consumed by the ¬rate residual continuation
  `selectedRouteEightStageClosure`.  ANALYSIS (recorded for the closure design): a ¬rate
  stage reached by peeling is arithmetically pinned — each `PeelChain.cons` carried the rate,
  so at the failed stage `θ|R| ≤ L + θ|P| < θ|R| + θ` with `L = (θs+1)|supply| + θ·slack` —
  and its closure is exactly the manuscript's window-pressure audit
  (`𝖯_open ≤ 2p₁₃ + 𝖯_zero⁺` + `prop:typeA-exit4-closure-from-open-pressure`), not local
  arithmetic; the survivor arm needs none of this.  EXTENDED same day: `DemandPartition` now also carries the type-(A1) absorber layer (`Absorption`: single-use absorbing incidences disjoint from every ledger assignment; `three_mul_add_two_mul_add_card_le` = `lem:typeA-pressure-absorber-no-overcount`'s raw count `3N₃ + 2N₂ + B_abs ≤ |supply|`) and `open_pressure_contradiction` — the cleared three-reading collision of `prop:typeA-exit4-closure-from-open-pressure` (deficit/budget-with-open-demand/rate), the engine the ¬rate residual continuation will close with once the graph-side token audit supplies its `budget` reading; and `card_le_two_mul_card_add_excess` — `lem:typeA-open-window-blocker-count` with the per-window split of `fig:exit4-p13-attachment-accounting` (`𝖯_open ≤ 2p + Σ_P (B_open(P) − 2)⁺`, generic fibre counting).  The whole file elaborates cleanly.  Plus `Graph/GluedCycleSides.lean` (kernel-built, 8582 jobs): `lem:typeA-pressure-token-two-carriers`' geometric core at an ARBITRARY outside context — side-crossing walks pass through a boundary label (`exists_label_of_walk_sides`/`'`), and a glued cycle meeting both interiors visits two DISTINCT labels (`exists_two_labels_of_cycle_sides`: rotate to the piece-internal vertex, split at the context-internal one, one label per arc, distinctness from the cycle's tail-nodup) — the cut-parity the profile-only demand tokens need, where the actual-exterior crossing lemmas do not apply.  And `Route8Residual.hasCycleWithLength_glue_of_retainedReading` — the one-sided monotone transfer of `lem:typeA-internal-quotient-mixed`: an accepted cycle of a gluing of the retained reading transfers to the same gluing of the basin's full piece (`glue_swap_target_iff` to the retained piece, `glueGraph_mono` + `Walk.mapLe` to the unrestricted piece); with `exists_context_of_not_contextEquivalent` this pins every defect's distinguishing context to realize the target on the full-piece side — the (P3) polarity of `def:typeA-exit4-pressure-token`.  `GluedCycleSides` gained the restriction transfer (`exists_walk_restriction_of_avoids_piece_internal` / `hasCycleWithLength_restriction_of_avoids_piece_internal`): an accepted glued cycle avoiding the piece's internal vertices lives in the gluing of any label-edge-preserving restriction — applied with the retained piece it forces every token's witnessing cycle to enter the basin (the manuscript's \"if E were contained in X…\" step, context side).  And the general trichotomy (`exists_pieceWalk_or_labelDart`, `cycle_pieceLift_or_contextInternal_or_labelDart`): a glued cycle lifts to a piece cycle of equal length, meets a context-internal vertex, or uses a context-owned edge between two distinct visited labels — generalizing the pathContext-only `exists_pieceCycle_of_avoids_chain` to arbitrary contexts; with the restriction transfer and the two-labels cycle lemma this closes every case of the token's |K(𝔱)| ≥ 2 except the piece-lift, which lands on the object-level cycle against the standing avoidance.

  TOKEN TWO-CARRIERS LANDED 2026-08-24 (kernel-built through
  `Hypostructure.Graph.TraceBasinAlternatives`, 8640 jobs):
  `exists_two_cutBoundary_of_traceLocalTargetDefect` = the whole of
  `lem:typeA-pressure-token-two-carriers`, assembled exactly as the manuscript proves it —
  alternative (a)'s distinguishing data + `exists_context_of_not_contextEquivalent` with the
  retained-reading monotone transfer pin the realizing side to the basin's full piece; the
  witnessing accepted cycle must enter the basin (label-edge-preserving retained restriction +
  `glue_swap_target_iff` against the defect); the glued-cycle classification then yields two
  DISTINCT cut-boundary labels in the witnessing event's support, the piece-lift arm decoding
  to an accepted ambient cycle against the standing avoidance.  This is the token's
  `|K(𝔱)| ≥ 2`; the remaining lane work is the `def:typeA-exit4-pressure-token` packaging,
  the ledger instantiation of `DemandPartition` over the census entries, and
  `prop:typeA-external-pressure-criterion`'s numeric row toward the ¬rate residual closure.

  PRESSURE-LEDGER MAXIMAL CHOICE LANDED 2026-08-24 (kernel-built through
  `Hypostructure.Graph.DemandPartition`, 734 jobs): `Partition.Pinned` is clause (L1)
  of `def:typeA-pressure-ledger` (every pinned entry in `Ξ₃`, paid from its private
  availability); `Partition.exists_pinned` constructs a clause-(L1) ledger from
  three-or-more pairwise-disjoint private incidences per pinned entry; and
  `Partition.exists_maximal_pinned` performs the manuscript's once-and-for-all choice
  maximizing first `N₃`, then `N₂` (`Nat.findGreatest` on the lexicographic value
  `N₃·(|Ξ|+1)+N₂`).  The instantiation at the census — pinned = surviving route-8
  entries with `indexedPrivateCoreCarriers` (≥3 since `thm:typeA-two-carrier-nogo`
  closed ≤2), available = the essential core (`2 ≤ entry.alpha` is on the ledger),
  supply = `Route8Census.supply` — and the no-overcount numeric row
  (`three_mul_add_two_mul_le` against `card_supply`) belong to the
  `lem:typeA-pressure-ledger-no-overcount` consuming row next.

  CENSUS LEDGER INSTANTIATION LANDED 2026-08-24 (kernel-built through
  `Hypostructure.Graph.Route8Census`, 8627 jobs): `exists_maximal_demandLedger` is
  `def:typeA-pressure-ledger` at the object (available = essential core, pinned =
  surviving route-8 entries paid from `indexedPrivateCoreCarriers`; disjointness and
  core-membership are theorems, the ≥3-private-carriers reading is the branch
  hypothesis), and `demandLedger_no_overcount` is `lem:typeA-pressure-ledger-no-overcount`
  in both manuscript displays against `e(R,W)` via `card_supply`.  Next labels in the
  lane: `def:typeA-two-terminal-pressure-records`/`lem:typeA-pressure-records-canonical`
  (actual-context vs profile-only polarity on the token) and
  `prop:typeA-external-pressure-reduction`'s three-class table.

  DEMAND RECORDS LANDED 2026-08-24 (kernel-built through
  `Hypostructure.Graph.TraceBasinAlternatives`, 8641 jobs):
  `exists_record_of_traceLocalTargetDefect` is
  `def:typeA-two-terminal-pressure-records` + `lem:typeA-pressure-records-canonical`
  — actual record (context = `SupportAtom.outside`, witnessing event, and the outside
  corridor between two DISTINCT boundary labels along event edges with
  context-internal interior) or profile record (non-actual context, two distinct
  visited labels), exactly one by the context-equality polarity.  The corridor engine
  is new in `GluedCycleSides` (section Corridor): `exists_context_lead_to_label`
  (context side exits through a label, along walk edges),
  `exists_corridor_of_path_labels` (nodup label-to-label walk: distinct-endpoint
  corridor via the takeUntil/dropUntil disjointness), and
  `exists_corridor_of_cycle_contextInternal` (label rotation + half-nodup transfer);
  both trichotomy dart arms now also carry `s(inl left, inl right) ∈ edges`, with the
  one-token consumer repair.  Next: `prop:typeA-external-pressure-reduction`'s
  three-class accounting at the census, then the absorbers
  (`def:typeA-pressure-absorbers`) toward `prop:typeA-external-pressure-criterion`.

  EXTERNAL-DEMAND REDUCTION LANDED 2026-08-24 (kernel-built through the new
  `Hypostructure.Graph.Route8DemandLedger`, 8642 jobs): the record proposition is
  factored as `TraceBasin.CanonicalDemandRecord` (actual corridor record or profile
  record, disjoint by the context-equality polarity), and
  `Route8DemandLedger.records_of_two_residual` is
  `prop:typeA-external-pressure-reduction`'s record row — every `Ξ₂ ∪ Ξ_res` entry
  of a clause-(L1) ledger is target-defect (unpinned ⟹ defect, from the census
  dichotomy at the consuming row) and carries its canonical record.  Next labels:
  `def:typeA-pressure-absorbers`/`lem:typeA-pressure-absorber-no-overcount`
  instantiation, the window-blocker audit, and
  `prop:typeA-external-pressure-criterion`'s numeric row.

  DEMAND-DEFECT SPLIT LANDED 2026-08-24 (kernel-built, `DemandPartition` 734 jobs):
  `Partition.demandWeight` (1 on `Ξ₂`, 3 on `Ξ_res`),
  `externalDefect_eq_sum_demandWeight` (`𝖯_ext` = total weight), and
  `externalDefect_split` (`𝖯_ext = 𝖯_act + 𝖯_prof` for any record-polarity
  predicate) are `def:typeA-actual-profile-pressure-defects` +
  `lem:typeA-pressure-defect-split`; the polarity predicate at the census is
  `CanonicalDemandRecord`'s actual arm.  Next in paper order:
  `lem:typeA-profile-pressure-dependence-routing` (functional admissible rank
  quotients on the profile coordinates), then `def:typeA-pressure-absorbers` units
  and `lem:typeA-pressure-absorber-no-overcount`'s `3Ñ − 𝖯_open ≤ def⁺(R) + B_dep`.

  ABSORBER LAYER LANDED 2026-08-24 (kernel-built, whole census chain 8642 jobs):
  `Partition.demandUnits`/`card_demandUnits` are `def:typeA-pressure-absorbers`'
  demand units with the exact count |𝒰_press| = 𝖯_ext, and
  `three_mul_card_le_of_absorption` is `lem:typeA-pressure-absorber-no-overcount`
  subtraction-free: `3Ñ ≤ |supply| + B_dep + 𝖯_open` with
  `𝖯_open = |𝒰_press ∖ (absorbed ∪ dep)|`; the (A2) certificate semantics, the
  routed-branch `B_dep = 0`, and the maximal absorbed-then-(A1) choice are branch
  data at the consuming row.  `lem:typeA-profile-pressure-dependence-routing` is
  recorded against the live generic `AttemptedQuotient.route` (arbitrary coordinate
  family; profile-preservation kills arm 1 at the instantiation).  Remaining in the
  lane: the window-blocker audit labels
  (`lem:typeA-open-window-blocker-count` already has
  `card_le_two_mul_card_add_excess`; the shadow/zero-shadow/numerics rows), then
  `prop:typeA-exit4-closure-from-open-pressure` (generic arithmetic
  `open_pressure_contradiction` is kernel-checked) and
  `prop:typeA-external-pressure-criterion`'s numeric row toward
  `selectedRouteEightStageClosure`.

  WINDOW-SHADOW LANE LANDED 2026-08-24 (kernel-built, new
  `Hypostructure.Graph.WindowShadowHit`, 8566 jobs):
  `exists_pathGraph_walk`/`exists_window_arc` (an embedded window carries a simple
  arc of length exactly the index distance), `exists_cycle_of_corridor`
  (corridor + two attachment edges + window arc = simple cycle of length
  s(Q) + 2 + |a − b|; simplicity from the corridor avoiding the window and the
  distinct-attachment-edge clause), and `hasCycleWithLength_of_shadow_hit` =
  `lem:typeA-window-shadow-hit-routes` (signature membership is the closed
  length's acceptance — certificate (O1)).  `WindowAttachmentShadow` gained
  `card_forbiddenDistances_le_one` = `lem:typeA-singleton-shadow-table`'s
  load-bearing tail (s ≥ 18).  Remaining in the lane: the overload-triple and
  same-window-cap labels (`def:typeA-same-window-overload-triple`,
  `lem:typeA-same-window-cap-overload-excess`, `def:typeA-same-window-open-blocker-cap`,
  `lem:typeA-routed-overload-not-open`), the zero-shadow labels, the
  blocker-accounting audit and numerics, then
  `prop:typeA-exit4-closure-from-open-pressure` and the criterion's numeric row.

  EXHAUSTION + CAP LAYERS LANDED 2026-08-24 (kernel-built, chain 8642-8644 jobs):
  `DemandPartition.exists_base_zero_partition` = the accounting audit and the
  exhaustion partition (base ≤ 2 per window, zero class = the zero-signature
  excess, exact disjoint cover); `card_le_two_mul_card_add_zero_excess` =
  `lem:typeA-open-pressure-zero-shadow-excess`; `excess_le_card_exceptional` =
  `lem:typeA-same-window-cap-overload-excess` (cap ⟹ excess ≤ exceptional card).
  The overload-triple labels are recorded against their four kernel-checked
  certificate engines ((O1) `WindowShadowHit`, (O2) `Absorption`, (O3)
  `AttemptedQuotient.route`, (O4) Type B handoff), `lem:typeA-routed-overload-not-open`
  is branch case elimination, `lem:typeA-primitive-excess-zero-shadow` is
  `filter_congr` on the branch equivalence, and the three closure propositions
  compose the checked engines with `open_pressure_contradiction`; every remaining
  numeric margin (ε_press, ε_prim, 2θ/(1−13θ)) is registered-`Data` instance
  arithmetic at the consuming rows.  The ¬rate lane's generic layer is now
  complete through the paper's S25 audit; what remains for
  `selectedRouteEightStageClosure` is the consuming-row assembly itself: the
  `def:typeA-exit4-pressure-token` packaging over the census entries, the branch
  decisions ((A2) routing, overload-triple removal, cap testing — [113]-pattern
  Decisions where the paper tests them), and the peeling-reduced ledger labels
  (`def:typeA-peeling-reduced-ledger`, `lem:typeA-peeling-reduced-reduction`,
  `cor:typeA-large-budget-closure-open-pressure`).

  ¬RATE-LANE GENERIC LAYER COMPLETE 2026-08-24: with the token packaging recorded
  against `exists_two_cutBoundary_of_traceLocalTargetDefect` + `CanonicalDemandRecord`
  and the criterion against `open_pressure_contradiction` at opendemand = 𝖯_ext +
  `demandLedger_no_overcount`, no ¬rate-lane label row remains marked
  "mathematics NOT yet implemented".  Every label's generic/geometric engine is
  kernel-built; what remains for `selectedRouteEightStageClosure` is exclusively
  consuming-row work on the residual branch: the [113]-pattern Decisions the paper
  itself tests ((A2) routing, overload-triple removal, the same-window cap), the
  registered numeric margins, and the assembly of the checked engines on the
  literal failed-stage ledger.  The peeling-reduced labels
  (`def:typeA-peeling-reduced-ledger`, `lem:typeA-peeling-reduced-reduction`,
  `lem:typeA-exit4-finite-descent`) were already producer-complete on the
  survivor path (`Route8Pressure` peel machinery + the [123] rows).

  STAGE-CLOSURE ROW 1 LANDED 2026-08-24 — the failed-rate frontier advanced one
  paper label, exactly per `def:typeA-pressure-ledger`:
  * `Route8Census.exists_maximal_demandLedger`/`demandLedger_no_overcount`
    restated on the arbitrary/`entriesOfComponents` family (replace-don't-accrete;
    kernel-built) so they apply verbatim to the unified collection `Ξ̃`.
  * New vocabulary key `route8DemandLedger` (idx 349, kernel-built 8733 jobs):
    `Route8DemandLedgerStatement` = the maximal pinned 2/3-demand ledger over `Ξ̃`
    (pinned = minimal entries holding at least δ private essential incidences,
    clause (L1); maximal in `N₃` then `N₂`), both no-overcount displays, and the
    canonical demand records of every unpaid target-defect entry.
  * `route8DemandLedgerDichotomy` (SpineRows, `Decision.run`): clause (L1)'s own
    dichotomy — a minimal entry with at most δ−1 private incidences and no
    exit-(4) witness is EXACTLY the `[124]` survivor fact
    (`K .route8UnifiedTrueTwoCarrierEntry`, republished verbatim); otherwise the
    ledger fact is committed, `avoids` read from `K .selection` per the ExactLedger
    discipline.  Full-file source check: only the pre-existing user-WIP errors.
  * `selectedRouteEightStageClosure` (Assembly.lean:1437) is now DEFINED: left arm
    closed by the same `route8UnifiedTerminalNoGoRow` (`thm:typeA-two-carrier-nogo`,
    read not re-proved), right arm handed to the new loud continuation
    `selectedRouteEightDemandAbsorption` — the manuscript's next labels
    (`def:typeA-pressure-absorbers` with the tested (A2) routing, then the
    window-blocker audit toward `prop:typeA-exit4-closure-from-open-pressure`).
    `selectedRouteEightCensus` gained the `[FactKeys.Has (K .selection) known]`
    binder its failed arm reads (available at its one call site).
  Assembly's kernel check still waits only on the user's SpineRows WIP block; both
  static catalog gates pass.

  INVENTION-REMOVAL IN PROGRESS 2026-08-24 (the user's standing order: remove the
  tested Decisions minted for claims the paper proves; implement the paper's own
  proofs; do not stop until [123] compiles).  Ruling of record on the three loud
  arms:
  * `selectedRouteEightQuotientResidual` — NOT an invention: the census (b)-test is
    the ratified two-predicate calibration.  Verified against the live predicates:
    `TraceResponseQuotient` (plain (b)) lacks exactly the compression data
    (`TraceTargetCompleteCompression`'s connected/proper atom, glued baseline
    `MinimumDegreeAtLeast`, and `LexicographicallySmaller` realization) that the
    `[104]` closure consumes — the identification cannot be derived, per the
    standing ruling.  The arm stays as the calibration's residual.
  * `selectedTypeBSublinearResidual` — IS an invention (the paper proves
    `prop:typeB-bridge-sublinear` outright).  Removal = implementing
    `lem:typeB-bridge-deficit-bound` + `lem:decorated-envelope-deficit-bound` as
    the paper proves them.  KERNEL-GREEN MILESTONES LANDED TODAY:
    (1) `K .typeAExclusion` generalized to the paper's own support-general
    quantification (executor proof unchanged; classification row instantiates at
    canonical pieces) — this is what lets the already-closed Type A case serve the
    post-ledger core components ("similar cases already closed rigorously");
    (2) `TypeBPostLedgerCore.refinedComponentCrossDegree` +
    `sum_scaledCoreCharge_component_eq` — the EXACT per-component identity
    Σ charge = s·def⁺(C) − |C| − s·cross(C);
    (3) `sum_scaledCoreCharge_core_ge` — the remaining-core floor with an
    extracted family (quiet components pay their size by
    `PostLedgerComponent.nonnegative_or_saturatedReceiver`, extracted ones floor
    at −|C|);
    (4) `TypeBEnvelopeCharge.massBound_of_disjointLedger_bounded` — the
    allowance-parameterized (B-ledger) mass bound (old fixed form kept as an
    instance).
    REMAINING ASSEMBLY, with the payment discipline now verified against
    `def:typeB-assigned-ledger` (charges are Y_X-internal-degree charges — the
    repo's `scaledCoreCharge` convention matches the manuscript exactly):
    the cross-degree `s·cross(C)` between a remaining-core component and the
    consumed fan carriers is paid by the B1 INCIDENCE CAPACITIES — the
    `OrdinaryDeficiencyReserve` units the B2 ledger partitions exactly
    (`reserveCapacityPartition`; per component `refinedComponentReserve` with
    `suppliedPositiveDeficiency`: s·def⁺_own(C) ≤ reserve(C) + stub(C)) — NOT by
    the F·s·σ allowance, which pays only the fan-envelope terms
    ((k−3+¼)+c/4 ≤ 8(k−3) = `Data.bridgeMassSlack`).  The quiet-component chain
    is: |C| ≤ s·def⁺_own(C) (the support-general `K .typeAExclusion`),
    s·def⁺_own(C) = s·def⁺_piece(C) + s·cross(C)
    (`sum_scaledCoreCharge_component_eq` rearranged), and the s·cross part is
    covered inside `refinedComponentReserve` by the consumed-incidence
    capacities anchored at the component.  The assembly composes the committed
    `K .typeBBridgeReduction` clauses + the exact refinement partition + the
    reserve-capacity partition + `massBound_of_disjointLedger_bounded`; then

  CROSS-BOUND MILESTONE LANDED 2026-08-24 (kernel-built, 8734 jobs):
  `FiniteObject.internalDegree_eq_of_closed` (BoundaryDemand — a closed region
  reads the same internal degree as its closure; membership-level proof, immune
  to the instance-transparency poison) and
  `TypeBPostLedgerCore.sum_refinedComponentCrossDegree_le` — the additive chain
  (A) per-component degree split, (B) components partition the core, (C) closed
  components read the core degree, then the `sum_internalDegree_comm` double
  count — bounding the total cross-degree by the removed region's internal
  degrees.  With `sum_scaledCoreCharge_component_eq`,
  `sum_scaledCoreCharge_core_ge`, and `massBound_of_extraction` (all
  kernel-built), the ENTIRE bridge-arm removal now reduces to ONE inequality,
  (★):

      s·crossTotal ≤ payment₂/2 + F·s·σ(X)

  — from the exact B2 partition identity
  |X| + s·σ = s·def⁺ − |H| − payment₂/2 − Σ_core − Σ_{H∩X}, the floors, and the
  landed component algebra, (★) is exactly what yields
  `lem:typeB-bridge-with-route8-core`'s
  |X| + s·σ ≤ s·def⁺ + F·s·σ + Σ_extracted(|C| − s·def⁺_own(C)).
  (★) is the manuscript's per-centre economy: the charged carriers' deficiency
  terms inside payment₂ net the carrier-side of every cross incidence, and the
  remainder is the fan-envelope negative part (k−3+¼)+c/4 ≤ 8(k−3).  Its proof
  must come from the committed candidate/profile ledger
  (`TypeBFanClosedPorts.Profile`, `TypeBHybridIncidence`'s window/non-window
  split, `PaysHybridB1`'s non-window demand payment, `IsCandidate`'s
  charged-vertices structure) — raw degree counting provably does NOT fit the
  registered `F = 8` (checked: crude removed-side bounds give about five times
  the budget), so only the manuscript's own fine-grained accounting closes it,
  exactly as `rem:route8-carrier-margin` warns.  After (★): the deficit row
  consumes `K .typeBBridgeReduction` + the support-general `K .typeAExclusion`
  via `massBound_of_extraction`, the extracted components join
  `route8UnifiedEntries` (their `PostLedgerComponent` fields carry every Type A
  admissibility invariant), and the tested
  `typeBSublinearDichotomy`/`TypeBSublinearHypotheses` and keys 345/346 are
  deleted.

  CORRECTION AND PAPER-ROUTE LANDING 2026-08-24 (superseding the (★) framing
  above): (★) was an artifact of forcing the paper's proof through the
  committed B2-partition route — the manuscript's own proof of
  `lem:typeB-bridge-deficit-bound` states explicitly that it "does not assume
  that the B2 disjoint-incidence ledger exists".  The paper's route is now
  IMPLEMENTED AND KERNEL-BUILT (8622 jobs), new module
  `Graph/TypeBBridgeMass.lean`:

  `bridge_mass_of_centre_deletion` = `lem:typeB-bridge-with-route8-core`:
      |X| + s·σ(X) ≤ s·def⁺(X) + F·s·σ(X) + Σ_{w ∈ receivers(X ∖ H_X)} |E(w)|
  — the centre region paid by the per-centre allowance (each centre carries at
  least one surplus unit, `sum_centres_surplus`), the deleted region discharged
  by the silence-free staged count
  (`card_le_sum_excessBasinReduced_add_positiveDeficiency` — the same engine as
  `stage_burden`), receiver routing total by
  `exists_traceTo_of_no_baseline_subsupport` from the committed remainder
  normalization, and the deficiency transfer through the deleted centres by the
  new `FiniteObject.positiveDeficiency_sdiff_le` +
  `internalDegree_le_add_of_cover` (BoundaryDemand, flavour-safe
  membership-level statements).  The unpaid excess loads `E(w)` of `X ∖ H_X`
  are the extracted census entries — the manuscript's `D_A(𝒜_X)`.  NO tested
  hypothesis anywhere: `routes` is a theorem, `unsaturated` is replaced by
  extraction, exactly `rem:unified-covers-exit4`'s reading.

  The slack `1 + s·δ + 2s ≤ F·s` (21 ≤ 32 at the registered values) is
  presentation arithmetic of the `bridgeMassSlack`/`fanCapSlack` family, to be
  registered as a `Data` fact discharged by `norm_num` in `Problem.lean`.

  REMAINING for the tested-Decision deletion, all mapped with no unknowns:
  1. The handoff arm: derive `envelopeFamilyNegativePart_le_degreeSurplus`'s
     per-piece hypotheses from the committed `HandoffProduced` envelope
     (`DecoratedHandoff.Envelope`: decorations = the centres, assigned/arm =
     the absorption structure, `lem:typeA-saturated-handoff` = saturated
     receivers absorbed by the handoff) — or the analogous
     extraction-plus-decoration count.
  2. `Route8UnifiedDeficitFact` restated with the extracted entries of
     `piece ∖ centres` for the negative σ>0 pieces (their components are
     connected σ = 0 admissible sub-supports of the remainder, so the
     support-general `K .typeAExclusion` classifies their entries for the
     census); census/descent run over the extended family.
  3. The deficit row rewritten onto `bridge_mass_of_centre_deletion` +
     `K .remainderNormalized`; the tested Decision and keys 345/346 deleted.

  THE COMPLETE [123]/[124] FACT-FLOW LEDGER 2026-08-24 (the closure as pure
  `inputs.get` collection; verified against every live Holds read this
  session).  Facts COMMITTED on the [123] ledger, available to read:
  selection, replacementExclusion, cubicBaseline, uncompressible,
  remainderNormalized, surplusAtOrBelow, typeAReceiverRouting (∀ σ=0
  sub-support of the remainder: routing totality + threshold algebra),
  typeBBridgeMass (three conditional mass bounds), typeBBridgeSublinear,
  route8UnifiedNegative, typeAExclusion (support-general),
  typeBBridgeReduction (∀-σ>0-negative-piece: B2 ledger + hygiene + grouped
  clauses, or overlap), route8PiecesClassified, route8UnifiedDeficit,
  route8QuotientFree (tested, ratified), route8UnifiedEntryCensus,
  route8VisibleExitFourRouting, route8PeelingDescent,
  route8StageRateFailed / route8UnifiedTrueTwoCarrierEntry,
  route8DemandLedger.  Registered data: bridgeMassSlack, and now
  bridgeDeletionSlack (1 + s·δ + 2s ≤ F·s, norm_num in Problem.lean,
  kernel-built 8733).

  ROW REWIRING (signature surgery only; the mathematics is kernel-built):
  * route8UnifiedDeficitRow: Requires [typeBSublinearLedger, surplusAtOrBelow]
    → [typeAReceiverRouting, surplusAtOrBelow, M1].  Executor per piece class:
    σ=0-negative-no-handoff → route8Deficit summand (definitional);
    nonneg → 0 (not_negativeNetCharge_iff);
    σ>0-negative → `bridge_mass_of_centre_deletion` with
      routed := (inputs.get typeAReceiverRouting) at piece∖centres
      (a σ=0 sub-support: ambientSurplus = 0 since no high vertex survives)
      and data.bridgeDeletionSlack — the Holds gains the extracted-entries
      term Σ_{w ∈ receivers(piece∖centres)} excess(w);
    σ=0-negative-handoff → M1.
  * route8UnifiedEntryCensusRow: extend over the extracted entries
    (components of piece∖centres are connected σ=0 admissible sub-supports of
    the remainder — the support-general typeAExclusion classifies them; = M2).
  * descent/stage/terminal rows: same shapes over the extended entry family
    (stage_burden's engine is support-general).
  * then DELETE typeBSublinearDichotomy, TypeBSublinearHypotheses,
    keys 345/346, and `selectedTypeBSublinearResidual` disappears.

  MISSING PRODUCERS — the exact remaining fact list, nothing else:
  M1  handoff-envelope mass: ∀ σ=0-negative HandoffProduced piece,
      |X| ≤ s·def⁺(X) + F·s·(decoration surplus, at-most-twice) — assembled
      from the committed classification's handoff arm (the
      DecoratedHandoff.Envelope datum) through the kernel-built
      envelopeNegativePart/envelopeFamily machinery.
  M2  the extended census fact over extracted entries (per above).
  M3  the failed-stage demand-chain facts behind
      selectedRouteEightDemandAbsorption (the S24 rows; every generic engine
      kernel-built).
  M4  the quotient residual arm (ratified two-predicate case; closure needs
      the manuscript's realized exit-(5) data per the standing ruling).
  [124] itself: complete; consumes route8UnifiedTrueTwoCarrierEntry only.

  M1 RESOLUTION AFTER TWO VERIFIED AGENT REPORTS 2026-08-24: the paper proves
  NO unconditional absorption bundle anywhere — `lem:typeA-saturated-handoff`
  (tex 11346–11360) is an outcome iteration whose outcomes INCLUDE the route-8
  residual, and every unconditional Type B mass statement keeps the −D_A(𝒜_X)
  escape term (`lem:decorated-envelope-with-route8-core`,
  `lem:typeB-bridge-with-route8-core`); the route-8-freeness hypothesis of the
  conditional forms is discharged in the paper BY EXTRACTION.  The [107]/[108]
  keys commit only `HandoffProduced` (∃ envelope, core = piece, decorations
  nonempty); the envelope structure carries no absorption fields.  The
  paper-exact carrier of the missing data is node [86]: `typeAExclusionRow`'s
  executor ALREADY derives the per-load classification internally (`perLoad`:
  each routed load is a route-8 entry ∨ quotient, with the witness and
  separator cases short-circuited into the piece-level arms) — the fix is to
  PUBLISH the per-load four-way form (witness ∨ route-8 entry ∨ quotient ∨
  separator-with-envelope) in `K .typeAExclusion`'s Holds, exactly what the
  executor proves, and repair the one consumer
  (`route8PiecesClassifiedRow`).  Then the handoff-piece deficit treatment
  reads it: separator loads → the envelope decorations (grouped per
  `lem:decorated-envelope-no-double-count`), witness/route-8/quotient loads →
  census extraction — no tested fact anywhere.  SEQUENCING: this [86] Holds
  enrichment must WAIT for the M2 agent (census region reads the current
  exclusion Holds) to land.

  M4 FINAL DISPOSITION 2026-08-24 (agent investigation, verified against tex
  11251–11295 and 5787–5805): the plain-(b) → exclusion bridge DOES NOT EXIST
  in the manuscript and must not be built — the admissibility representative
  clause is a definitional filter, not an existence theorem ("it is only an
  abstract identification of labels"), and `properRepresentative`/
  `closedRepresentative` are consumed as hypotheses everywhere in the tree,
  never constructed.  The paper's own disposition of exit (5):
  * realized by a smaller proper piece → `cor:uncompressible`
    (= the committed [104] consumption, exactly as implemented against
    `TraceTargetCompleteCompression`);
  * response-level only → alternative (b), "not an admissible route-8
    residual" — excluded by `def:typeA-true-route8-residual` (R2)/(R4), i.e.
    CASED, with the denial carried by the true-residual entry — exactly the
    committed `route8QuotientFree` test and the terminal fact's
    `TargetCompleteMinimal` conjunct.
  The committed design is therefore the paper's architecture.  The residual
  arm (`selectedRouteEightQuotientResidual`: ∃ entry with plain (b)) closes
  inside the S24 demand accounting: the response-level data is precisely the
  PROFILE DEMAND RECORD of `def:typeA-two-terminal-pressure-records`
  (`(q, r(ξ), S₀, S₁, Y)`), so that arm folds into the failed-stage demand
  chain (the M3 lane), not into a separate closure.  The two unprovable
  formulas, for the record (any future attempt must produce them from new
  manuscript text, never from invariants): the glue baseline
  `MinimumDegreeAtLeast θ (glue (retainedReading …) outside)` and
  `LexicographicallySmaller` for the retained reading — both are separate
  FIELDS of the realized predicate because they are not derivable.

  M3 LANDED 2026-08-24 (agent-verified: vocabulary kernel-built 8733 jobs,
  SpineRows at the exact 22-line baseline, DemandPartition kernel-built):
  keys `route8DemandAbsorption` (idx 351) and `route8WindowBlockers`
  (idx 352) with rows `route8DemandAbsorptionRow` /
  `route8WindowBlockersRow` inserted after the demand-ledger dichotomy;
  generic additions `Partition.fst_mem_of_mem_demandUnits`,
  `Partition.exists_maximal_absorption`, and
  `FiniteObject.exists_mem_packing_of_notMem_remainderSupport`.
  CALIBRATION DECISION FOR USER REVIEW (agent-flagged, endorsed): the
  absorption fact publishes (A1)-maximality WITH THE TYPE-(A2) SET HELD
  (∀ B with the same side conditions and disjoint from dep,
  |B.absorbed| ≤ |A.absorbed|) — NOT pair-maximality over (B, dep′), which
  would force 𝖯_open = 0 and vacuate the S24 chain; the held-form is exactly
  the property the manuscript's maximal choice satisfies and the one consumed
  at tex 15708 (the (O2) case of `lem:typeA-routed-overload-not-open`: an
  open unit with an admissible fresh incidence contradicts maximality).
  Blocker construction: uniform from the entry's receiver (completion ports
  nonempty), not from the token records — the record datum is basin-level
  and conditional; the uniform route is the manuscript's own "the other
  endpoint lies in W" sentence.  NEXT in the M3 lane: the overload-triple /
  zero-shadow exhaustion rows on `K .route8WindowBlockers` (the generic
  engines `exists_base_zero_partition`, `card_le_two_mul_card_add_zero_excess`,
  `excess_le_card_exceptional`, `WindowShadowHit` are all kernel-built), into
  which the quotient-residual arm's profile records fold per the M4
  disposition.

  M2 LANDED 2026-08-24 (agent-verified: vocabulary 8733 jobs, SpineRows at
  the exact 22-line baseline): key `route8ExtractedEntryCensus` (idx 350) +
  `route8ExtractedEntryCensusRow` — the per-entry census facts
  (`Route8UnifiedEntryFacts` REUSED UNCHANGED) at the entries of
  `route8ExtractedCores` = the canonical connected components of
  `piece ∖ centres` over the negative σ>0 pieces, filtered to the paper's
  `𝒜_X` (σ = 0, negative, ¬HandoffProduced, quotient-free) — the
  component-indexed form, since the census derivation genuinely needs
  connectivity (`exists_select?_eq_some_of_mem_routedLoads`).  Deviations
  reported and endorsed: (i) `K .typeAExclusion` is NOT consumable per
  component (its trichotomy cannot refute plain (b) and needs negativity);
  the quotient-freeness and ¬handoff clauses are DEFINITIONAL FILTER clauses
  of the collection, exactly as `route8UnifiedComponents` carries its own —
  the paper's `𝒜_X` is by name the route-8 residual collection; (ii) the row
  Requires only [selection, replacementExclusion, cubicBaseline].
  INTEGRATION NOTE for the deficit-row rewrite: `bridge_mass_of_centre_deletion`
  sums excess over ALL receivers of `piece ∖ centres`; the extracted census
  covers the FILTERED components only — the complement components split as:
  nonneg → 0, handoff → the envelope lane ([86] per-load enrichment),
  quotient → the profile-record lane (S24), the same three-way split as
  everywhere; the deficit Holds must route each accordingly.

  [86] PER-LOAD PUBLICATION LANDED 2026-08-24 (agent-verified against
  `lem:typeA-reduced-silent-residual`'s own per-load proof, tex 10949–10978;
  vocabulary 8733 jobs; SpineRows at the exact 22-line baseline):
  `K .typeAExclusion`'s Holds now carries, as an additive second conjunct
  under the same support-general quantification, the per-load FOUR-WAY
  classification at every saturated receiver (silent-excess and
  overloaded-port loads): exit-(4) witness ∨ `Route8Entry` ∨ plain-(b)
  quotient ∨ (surviving separator ∧ `HandoffProduced`) — derived ONCE in the
  executor (the previous short-circuits into piece-level arms now read off
  the same `perLoad`), existing trichotomy byte-identical as component 1,
  single consumer `route8PiecesClassifiedRow` repaired with a `.1`
  projection, no Assembly repair needed.  ALL FOUR M-FACTS ARE NOW RESOLVED:
  M1 → this per-load fact (the separator arm is the handoff lane's per-load
  carrier), M2 → key 350, M3 → keys 351/352, M4 → closed (no bridge; profile
  lane).  REMAINING: the serial integration — restate the unified-deficit
  Holds routing each non-extracted component class per the three-way split,
  rewrite `route8UnifiedDeficitRow` onto `bridge_mass_of_centre_deletion` +
  `K .typeAReceiverRouting` + `data.bridgeDeletionSlack` + the per-load fact,
  extend the burden/descent over the extracted entries, delete
  `typeBSublinearDichotomy`/`TypeBSublinearHypotheses`/keys 345–346, wire the
  failed-stage continuation through keys 351/352, then the audit rows.

  INTEGRATION DESIGN FREEZE v2 (2026-08-24, supersedes the per-class routing
  sketch above after full manuscript verification):
  (0) FINDING — M2 re-base required.  The paper's `𝒜_X`
  (`lem:typeB-bridge-with-route8-core`, tex 14483: "After deleting the Type B
  fan envelopes … contained in the remaining non-window core") lives in the
  B2 ledger's REMAINING CORE, not in the bare centre-deleted region
  `X ∖ centres(X)` that the landed `route8ExtractedCores` uses.  The
  committed carrier of the paper's route is `K .typeBBridgeReduction`
  (idx 344, fresh at the [123] cursor): B2 `DisjointLedger` + exact
  refinement + negative core charge + PostLedgerComponent hygiene + grouped
  decorated-envelope productions, with
  `Graph.TypeBPostLedgerCore.massBound_of_extraction` giving
  `|X| + s·σ ≤ s·def⁺(X) + Σ_extracted |C| + s·Σ crossDegree`, `quiet`
  discharged definitionally by extracting every negative component.
  (1) `route8ExtractedCores` redefined over the chosen ledger's remaining
  core (classical dite choice per piece, `canonicalWindowPacking` pattern);
  entry family `route8UnifiedEntries` extended by union; M2's census row
  re-based (its derivation is collection-agnostic at connected σ=0 negative
  filtered cores).
  (2) `Route8QuotientFreeStatement` extended with the deleted-region
  conjunct (quotient-freeness at excess loads of every negative no-handoff
  remaining-core component), and `route8QuotientDichotomy` MOVED before the
  deficit row in `selectedLargeBudgetPressureCensus` — the ratified casing
  is the branch surrogate of the exit-(5) closure that
  `lem:typeB-bridge-with-route8-core`'s proof invokes through
  `lem:typeA-exclusion`; on the free arm the negative components split into
  handoff (grouped-envelope-paid) and extracted (census-covered) only.
  (3) Deficit fact: `|R| ≤ route8Deficit(𝒳̃) + extractedDeficit + s·supply
  + 2FsT(n)`; descent slack UNCHANGED at `2FsT(n)` — the extracted deficit
  is absorbed into the family count by the per-core staged burden, not into
  slack (a slack route would poison the stage rate and the demand margin).
  (4) Open joints under verification (three read-only agents dispatched):
  (A) obstruction-arm payment at 344's right disjunct; (B) grouped-envelope
  payment bundle derivability from 344's productions (remaining-core
  components) and from `HandoffProduced` ([86] conjunct) for the σ=0
  negative handoff CANONICAL pieces, which 344 does NOT cover; (C) component
  decomposition lemmas (card/def⁺/staged count over remaining-core
  components) and DisjointLedger trivial-instance viability for the choice
  definition.  Integration edits begin when A–C report.

  ABSORPTION ENGINE LANDED 2026-08-24 (kernel-green, 8666 jobs, one new
  file `Hypostructure/Graph/DecoratedAbsorption.lean`, no Strategy file
  touched): the prose half of `lem:decorated-envelope-deficit-bound` +
  `lem:window-handoff-center-accounting` is now theorem.  The absorbed set
  is the committed excess basins `⋃_w E(w)` of the saturated receivers
  (`absorbedExcess`) — the manuscript-faithful choice for which `routes`
  off-absorbed is FREE (absorbed vertices are θ-full, receivers strictly
  below θ) and `unsaturated` off-absorbed is exact (`card_payableSet_le`).
  `envelopeFamily_of_absorbedExcess` closes the family payment
  Σ cleared ≤ F·s·degreeSurplus from: σ=0, the [88]-shape routing, high
  centres, pairwise-disjoint per-unit centre families, and ONE remaining
  per-unit hypothesis — `assigned`: |absorbedExcess(unit)| ≤
  Σ_{centre ∈ centresAt unit} closedCount(fanEnvelope centre, centre),
  reducible by `card_absorbedExcess_le_of_centreAssignment` +
  `pair_le_closedCount_of_separation` + `closedCount_eq_degree_of_tight`
  (tightness = the committed [67] `neighbourTight`) to a per-receiver
  centre assignment maps/injective/slots.  VERIFIED IRREDUCIBLE: no
  committed structure carries the per-load fan-out injection (the
  manuscript also takes this as DATA — `def:typeB-assigned-ledger`'s fan
  assignment — and its own alternative proof is the
  `lem:typeA-saturated-handoff` iteration with exit-(4) peeling, a
  well-founded recursion not yet formalized).  CONSEQUENT DECISION for the
  final push: keys 345/346 are NOT deleted outright — their Holds SHRINKS
  from the fat 4-clause-plus-coverage package to exactly the manuscript's
  assigned-ledger fan-assignment cardinality datum (per handoff unit:
  centres, fanEnvelope, maps/injective/slots; across units: centre
  disjointness), quantified over the handoff units (σ=0 negative handoff
  canonical pieces ∪ negative handoff cores of the deleted regions); the
  indices, labels, and residual lane are unchanged; everything else the
  old statement carried is consumed as theorems (clause (i) replaced by
  the identity route; clause (ii)'s pair/coverage by the engine).  The
  follow-up that would delete the test entirely is the saturated-handoff
  iteration engine.

  DESIGN v3 (2026-08-24, after agent A's verdict; SUPERSEDES v2's re-base):
  agent A verified exhaustively that NO committed carrier pays a piece's mass
  from an `OverlapObstruction` (the structure carries no numeric field; both
  obstruction keys are single-support existentials with per-centre
  `envelopeNegativePart` bounds), and that the paper's own payment
  (`lem:typeB-bridge-deficit-bound`, tex 14396) is deliberately
  B2-arm-independent ("It does not assume that the B2 disjoint-incidence
  ledger exists").  Consequently the remainingCore re-base is DEAD (its 344
  casing dies on the obstruction arm) and M2's landed X∖centres collection
  STANDS.  The deficit row's σ>0-negative arm needs NO staged count and NO
  routing: |X| = |centres| + Σ_components |C|; per component the ℕ-identity
  |C| ≤ s·def⁺(C) + (|C| ∸ s·def⁺(C)) with the truncated term vanishing on
  nonneg components; Σ s·def⁺(C) = s·def⁺(X∖centres) ≤ s·def⁺(X) +
  s·Σ_centres internalDegree (`positiveDeficiency_sdiff_le`, kernel-built);
  centre cost ≤ (1 + s·θ + s)·σ(X) ≤ F·s·σ(X) by the registered
  `bridgeDeletionSlack`; negative components split DEFINITIONALLY into
  M2-filtered (→ the fact's extracted-deficit term), quotient-carrying
  (killed by the extended quotient-free conjunct on the free arm), and
  handoff (→ the role-2 envelope payment, agent B pending).  The handoff
  σ=0 canonical pieces are the same handoff unit with centres = ∅.  Slack
  stays the committed two-role 2·F·s·T(n); StageRateFailed/PeelingDescent
  keys are UNTOUCHED; the descent row extends its burden per extracted core
  by the staged count (committed routing applies at σ=0 cores).  Assembly:
  `selectedRouteEightQuotientResidual` is a loud undefined continuation
  (Assembly 1618 is its only occurrence), so moving the quotient dichotomy
  before the deficit row breaks no signature.  M2's census row gets wired
  before `route8UnifiedEntryCensusRow`, which repairs its union split by
  reading key 350.
    the deficit row rewritten to consume `K .typeBBridgeReduction` (committed:
    ledger + exact refinement + negative core + per-component
    `PostLedgerComponent` + exit-seven grouped envelopes, or overlap) with the
    saturated components EXTRACTED into the unified ledger (the appendix's
    "route-8 non-window core is extracted into D_A"), the census extended over
    the extracted components (their `PostLedgerComponent` fields supply every
    Type A admissibility invariant), and the overlap arm closed
    (`lem:typeB-global-local-reflection` clause (d) is the one un-derived piece —
    `TypeBGlobalLocalReflection`'s module note).  Then the tested
    `typeBSublinearDichotomy`, `TypeBSublinearHypotheses`, and keys 345/346 are
    deleted.
  * `selectedRouteEightDemandAbsorption` — the failed-stage demand chain per the
    paper's own S24–S25 order; its terminal margin state is recorded earlier in
    this file.


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
  (5)/(6)/(7) arms are the manuscript's own machinery and nothing else:
  `def:proper-quotient-representative` (the canonical realization already carried by
  `Graph/CanonicalRealization.lean`), `def:typeA-continuation-classes` (the switch support and
  its readings), and `lem:typeA-internal-quotient-mixed`; the realized-compression datum of
  exit (5) carries its own strictly-smaller clause as part of the exit's defining data. No
  auxiliary "realization theorem" is introduced (a previously drafted unimported module to that
  effect was deleted).
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
`route8UnifiedEntryCensus` — its refutation clauses are LEDGER READS, not new theorems:
¬(b) from `K .uncompressible` (a realized compression is `CompressibleSupport` at the basin),
¬(c) from `Delocalization.localize` against `K .replacementExclusion`/`K .selection`, ¬(d) from
`envelopeOfSeparation` against the collection's own `¬ HandoffProduced` filter; the standing
invariants are committed on the trunk far upstream of [123], so the row simply Requires them;
(4)
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
`K .activeSurplusDemands`, `K .cubicBaseline`, and `K .capacityTokenLedger`.
The sealed active-family value already contains the survivor, activation, and
two-shoulder clauses proved at `[128]`, so `[144]` projects those clauses from
that one `FactInputs.get` instead of reading duplicate keys. Its literal manifest produces
`K .bottleneckRouting` and the survivor specialization `K .typeBHandoff`. The owner is loud
inside its proof, before either output can be committed.

**Primary defect class.** mathematical proof absent after the declared-connector step of
`lem:same-token-bottleneck-routing`. The former local `AttemptedQuotient` obligations were
circular: constructing that structure already required the proper and closed representatives
which the paragraph was meant to derive. They have been removed. The row now exposes the paper's
literal parallel-routing and cubic-switch implications, plus the common-prefix/root-incidence
alternative, once on each of the matching and star arms.

**Fresh audit diagnosis.** ⚠ DECLARED-CONNECTOR STEP REPAIRED — Node [136] already proved the
current object connected while constructing the canonical pair support `X_π`; that proposition was
formerly discarded. Its existing `K .capacityTokenLedger` fact now retains
`ConnectedOn G V(G)`. Each of [140], [142], and [143] requires that same ledger fact, reads it with
`inputs.get`, recovers `Θ_cap(π)=t` from the actual role fibre, and proves an inhabited routing
configuration for every demand of every edge in its matching/star. The producer then publishes the
configuration family, its canonical common root, and the homogeneous pattern atomically in the
existing `K .homogeneousBottleneckPattern` fact. No new key, presentation field, selector, route
carrier, or nonmonotone handoff is introduced.

The declared support is derived from the existing capacity presentation: token carrier, canonical
blocker, `T(p),T(q)`, `Γ(p),Γ(q)`, the canonical pair-response support `X_π`, and the already
registered canonical returns `R_p,R_q`. The connector walk is obtained from the connected declared
support and is checked to start in the primitive token support and land in the selected local
buffer. The generic support lemmas introduce no stored object; all object-valued witnesses are
constructed inside the producer proof and sealed by the homogeneous-pattern ledger entry.

Node [144] now destructures that strengthened ledger entry, performs the manuscript's matching/star
endpoint choice and finite routing-label collision, and obtains both configurations from the
registered provider. It proves that their heads coincide and that this head is the canonical token
root. The former [144] code that re-proved graph connectivity, re-read the token charge, rebuilt
`X_π`, and redefined the token root has been deleted.

The six remaining formulas are three obligations duplicated by the matching/star endpoint choice.
First, a parallel pair of configurations, together with the connected common support carrying the
two distinct declared response coordinates and their equal routing label, must produce a
`SparseSurplusExit`. Second, at a cubic first separator, the exhausted three-incidence package,
the two carried configurations and response coordinates, and the same ledger data must produce a
`SparseSurplusExit`. Third, before that package can be formed, Lean requires the manuscript's
implicit assertion
`SparseSurplusExit ... current.object ∨ common ≠ []`
from the two same-root path decompositions and `nextLeft ≠ nextRight`.

The third assertion is not a consequence of the registered configuration schema. A legal token
`CapacityToken.primitive (.inl v)` has `tokenSupport = {v}`; the producer supplies simple paths
whose head is `v`, and two such paths may diverge immediately at a cubic `v`. Then the
`SeparatesAt` decomposition has `common = []`, so no predecessor/root incidence exists. The
remainder-surplus constructor is different (membership makes its root high), but the primitive
vertex constructor shows that the general [144] assertion is missing. Likewise, the parallel and
cubic paragraphs need two actual readings on one common boundary and a concrete admissible
identification/representative. `pairResponseReading` presents each `X_π` on its own boundary,
and equality of the finite routing label does not construct those same-interface readings or the
representatives required by `AttemptedQuotient`. No whole-graph replacement path, arbitrary third
neighbour, extra support entry, or detached quotient theorem is an admissible substitute.

**What must be implemented or corrected.**

- Complete the already registered mathematical `Holds` proposition, which now states the paper's
  concrete homogeneous-pattern package and exact sparse-exit-or-decorated-Type-B alternative. Do
  not restore a universal theorem about a separately supplied bottleneck.
- Finish the anonymous proof inside `sameTokenBottleneckRoutingRow` from the two configurations now
  read from `K .homogeneousBottleneckPattern`. This requires a manuscript proof of the common-boundary
  response identification and a manuscript case for immediate divergence at a singleton token root;
  neither may be replaced by an arbitrary `AttemptedQuotient` or third neighbour.
- Use the registered configurations with the ledger's canonical `R_p,R_q`; never select a
  replacement path. The paper's parallel case must follow its attempted-quotient/context/compression/smearing/closed-
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

- [x] **Implemented / reachable through the declared connectors:** the exact support API, retained
  connectivity, and all three producer rows kernel-check; [144] reads the two same-root configurations
- [x] **Correctly wired:** each exact pattern plus its configuration family reaches
  `sameTokenBottleneckRoutingRow` directly
- [x] **Residual-local proof:** the three class audits concern the literal active object
- [x] **Correct connector registration:** [140]/[142]/[143] append the inhabited same-root family in
  the existing homogeneous-pattern fact; the later `[bottleneckRouting, typeBHandoff]` outputs still
  cannot be committed until the remaining case analysis closes
- [x] **No invented path strategy:** the global path fields, two extra support entries, collision
  wrappers, undefined selector, detached carriers, and conditional row are deleted
- [ ] **Exact manuscript proof:** first absent at the parallel common-boundary identification; the
  separated arm additionally lacks the immediate-divergence/root-incidence case
- [x] **Independent kernel check:** `SameTokenRoutingGerms`, `ObjectCapacityLedger`, and
  `SpineVocabulary` build; the narrow row reports exactly six unsolved goals (the three displayed
  obligations on the matching and star arms), and searches find no obsolete routing carrier or fake
  producer

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
