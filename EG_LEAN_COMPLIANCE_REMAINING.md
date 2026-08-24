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
