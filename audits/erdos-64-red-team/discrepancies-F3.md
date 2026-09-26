# Lean versus paper: registered discrepancies, family F3 (Route 8)

Format as in `lean-vs-paper-discrepancies.md`.  Every entry names the node,
the paper argument with tex lines, the Lean argument with its declarations,
and why the Lean is at least as strong.

## [113]: the large-budget deficit is tested, not asserted

- **Paper** (diagram tex:1129, box `[113]` between `[112]` and `[114]`;
  `rem:why-unified` tex:17529--17560). The diagram draws `[113]` as a box, but
  `rem:why-unified` states that the route-8-only lower bound
  `D_A(𝒳_A) ≥ (1/4-τ_win)|R| - o(|R|)` does not follow: the deficit can reside
  in the target-defect class, which the unified ledger of `[123]` handles.
- **Lean.** `route8LargeBudgetDeficitRow`
  (`hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8LargeBudgetDeficit.lean`)
  decides the exact inequality `Route8LargeBudgetDeficit` against its negation
  `Route8LargeBudgetDeficitFailsStatement` on the same collection `𝒳_A`.
  The positive arm continues to `[114]`--`[124]` exactly as in the diagram; the
  negative arm enters the unified target-defect/route-8 ledger
  (`selectedTypeBRoute8Continuation`, `Assembly/RouteEight/TypeBContinuation.lean`)
  and reaches `[123]`, `[181]`, `[183]`--`[186]`.
  Caller: `selectedRouteEightResidual` (`Assembly/RouteEight/Residual.lean`).
- **Why the Lean prevails.** It repairs the gap `rem:why-unified` itself
  identifies: no arm is assumed, the positive arm is the paper's own `[113]`
  fact, and the negative arm is sent to the unified ledger the paper
  introduces for exactly this mass.  Kernel-checked.

## [118] → [124] on the `[113]`-positive arm

- **Paper** (tex:1134--1140, edges `(residual)--(pressure)`, `(pressure)--(nogo)`).
  The two-support entry `[118]` enters the descent decision `[123]`; its yes arm
  ("terminates in true route 8") is closed at `[124]`.
- **Lean.** On the `[113]`-positive arm every entry of `Ξ(𝒳_A)` is a true
  route-8 entry (`Route8TrueResidual`: target-complete-minimal and no exit-(4)
  witness), so the descent terminates at the empty peeling in true route 8.
  `route8TrueTwoCarrierEntryRow` publishes the terminal entry, and `[124]`
  closes it: `route8TwoCarrierExitRow.runAndCloseIncompatible` with
  `instIncompatibleRoute8TrueTwoCarrierEntryTwoCarrierExit`
  (contract lemmas `route8SurvivorTwoCarrierExit`,
  `route8TrueTwoCarrierEntry_false`,
  `Graph/Contracts/RouteEight/Terminal.lean`).
- **Why the Lean prevails.** The skipped descent step is the identity on this
  arm (no target-defect entry exists to peel), the node closed is the paper's
  `[124]`, and the closure is the paper's own `thm:typeA-two-carrier-nogo`
  argument (`lem:typeA-carrier-deletion-exit`).  Kernel-checked.

## [123]: the terminal stage is fixed by description

- **Paper** (`thm:large-budget-route8-only`, tex:17085--17140). "Run the
  following deterministic procedure"; the decision `[123]` is asked at its
  terminal stage.
- **Lean.** `route8DescentChain` (`Graph/Statements/RouteEight.lean`) is the
  `Classical.epsilon` choice of a stage satisfying `StageOutcome`; the
  existence of such a stage is the paper's procedure
  (`exists_route8StageOutcome`, `Graph/Contracts/RouteEight/Descent.lean`).
  The decision `route8StageOutcomeDichotomy` asks the reduced-rate test
  `Route8StageRateStatement` versus its exact negation
  `Route8StageRateFailedFact` at that one stage.
- **Why at least as strong.** The pinned stage satisfies every property the
  paper's terminal stage has (recorded peel chain, exact stage accounting, and
  either failed rate or passing rate with a true two-support entry); both arms
  are about the same pinned stage, so the decision is an exact dichotomy.

## [181]/[183]: quantification over maximal ledgers

- **Paper** (`thm:typeA-unpaid-exit4-reduction`, tex:17142--17220). Fix the
  lexicographically first maximal ledger `P` of `def:typeA-pressure-ledger`;
  (168.1) holds for `Ξ_un(P)`; outcome (i) "some `ξ ∈ Ξ_un(P)` has no exit-(4)
  witness" versus outcome (ii) (168.2).
- **Lean.** `Route8MaximalDemandPartition` names the maximal pinned ledgers.
  (168.1) is `Route8UnpaidTwoCarrierStatement` for every maximal ledger
  (`route8UnpaidTwoCarrier`); the node-`[181]` keys are
  `Route8UnpaidWitnessFreeStatement` (some maximal ledger has an unpaid
  witness-free entry) and its exact negation
  `Route8UnpaidExitFourResidualStatement` (every unpaid entry of every maximal
  ledger has its witness) (`Graph/Contracts/RouteEight/DemandLedger.lean`,
  `SpineRows/Route8UnpaidExitFourDichotomy.lean`).
- **Why at least as strong.** The paper's fixed ledger is a maximal ledger, so
  (168.1) and (168.2) for all maximal ledgers imply them for it; the yes arm is
  closed at `[124]` exactly as outcome (i).  The two keys are literal
  negations of each other, so the split is exact without choosing a ledger.

## [184]: the silent Type A lane closes at the visibility reduction

- **Paper** (tex:1143--1145; `lem:typeA-unified-visible-ownership`,
  `lem:typeA-unified-silent-terminal-exclusion` tex:17480). Both Type A lanes
  run `[183]`--`[186]`; the silent terminal is excluded as a conjunct of the
  open node `[186]` ((168.22)).
- **Lean.** The silent lane (the silent arm of F1's
  `typeASilentExitSevenDichotomy`, carrying `K .typeASilentExitSevenFree`)
  enters `selectedRouteEightResidualSilent`
  (`Assembly/RouteEight/Residual.lean`), which shares every stage with the
  visible entry (`selectedRouteEightProfile`,
  `selectedRouteEightCollectionCloses`, `selectedRouteEightBridgePrefix`,
  `selectedRouteEightDescent`, `selectedRouteEightUnpaidReduction`) and
  differs only after `[183]`: `route8UnifiedVisibleResidualRow` is run with
  `runAndCloseIncompatible` against `K .typeASilentExitSevenFree`
  (instance `typeASilentExitSevenFreeVisibleClosed`, `TypeAExitRun.lean`).
  The former `Option` argument of `selectedRouteEightResidual` is removed.
- **Why the Lean prevails.** The lane's selected silent excess load is itself a
  unified entry; `[184]` (the paper's own lemma) makes every unified entry
  visible, so the lane is closed by the fact the paper proves at `[184]`,
  before the joint balance.  The paper's `[186]` exclusion (168.22) is the same
  contradiction stated one node later.  Kernel-checked; the visible lane still
  reaches the open node `[186]`.
