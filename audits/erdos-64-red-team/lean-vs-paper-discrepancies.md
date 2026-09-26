# Lean versus paper: registered discrepancies

The manuscript `to_formalize/erdos_64_proof.tex` is the authority for the
proof strategy. The Lean deviates from it only when all four conditions hold:

- the Lean argument is kernel-checked;
- it does not weaken any fact the paper states;
- it closes the node the paper closes; and
- it is better than the paper's argument, because it is simpler, needs fewer
  hypotheses, or does not need a link the paper leaves implicit.

When all four hold, the Lean prevails, and the deviation is recorded here.
Every entry names the node, the paper's argument, the Lean argument and its
declarations, and the reason the Lean is at least as strong.

Entries are ordered by the first node they name.  Each entry records the
contract-migration family that registered it (F1 Type A, F2 Type B, F3 Route 8,
F4 Surplus / Homogeneous / Pair, F5 Spine / Cold / NearCubic).

## [8]: `NoProperBaseline` also records connectedness

*Family F5 (Spine / Cold / NearCubic).*

- **Lean.** `K .noProperBaseline` = `lem:no-proper-core` ∧ `Connected`
  (`connected_of_noProperBaseline`).  The added conjunct is a proved
  consequence; nothing is weakened.

## [13]: `lem:replacement` without hypothesis (iii)

*Family F5 (Spine / Cold / NearCubic).*

- **Lean.** `K .replacementExclusion` excludes every one-way replacement
  (`ReplacementSupport`); hypothesis (iii) (no internal power-of-two cycle in
  `X′`) is not required, because a cycle inside `X′` is already caught by the
  one-way inclusion (i) at `G`'s own outside context.  Excluding more
  replacements is a stronger exclusion.

## [14]: now paper-exact

*Family F5 (Spine / Cold / NearCubic).*

`UncompressibleStatement` is `∀ support, ¬ ReplacementSupport …`, the first
assertion of `cor:uncompressible` ("exactly `lem:replacement`") under
`def:target-complete-compression` (one-way inclusion).  Consumers that hold a
two-way `CompressibleSupport` weaken it with
`replacementSupportOfCompressibleSupport`.

## [34]/[47]: exact full rank

*Family F5 (Spine / Cold / NearCubic).*

- **Paper.** `lem:full-rank`: `r_Ω(R) ≥ W₂(R) − o(W₂)`.
- **Lean.** `curvatureRankDichotomy`'s no arm `K .curvatureFullRank` publishes
  `r_Ω(R) = W₂(R)` at the fixed maximum packing (now pinned:
  `packing = canonicalWindowPacking`).  It serves `[34]` and `[47]`.
- **Why the Lean prevails.** It is the exact finite complement of the rank-drop
  arm and implies the paper's inequality; kernel-checked.

## [50]: now paper-exact at the fixed packing

*Family F5 (Spine / Cold / NearCubic).*

`K .remainderEntropyHigh` / `K .remainderEntropyLow` are the rate test and its
negation on the remainder of the fixed maximum packing
(`packing = canonicalWindowPacking`), decided by `remainderEntropyDichotomy`.

## [53]: the entropy-cap test sits on the high-entropy arm, with `K = 0`

*Family F5 (Spine / Cold / NearCubic).*

- **Paper.** Diagram Part IV (tex:878-894) draws `[50]` yes → `[51]` → `[52]`
  → `[54]` unconditionally, and `[53]` "remaining non-obstruction budget
  `< K|R|`?" on `[50]`'s *no* arm.  The text says the opposite:
  `prop:entropy-high-theta` (tex:9919) is stated "in the high-entropy branch of
  `prop:two-budget`", and `prop:two-budget` (tex:9685) passes the surviving
  residual of *every* case, including (a), to the large-budget analysis.  The
  budget accounting of `eq:entropy-cap` (tex:9870-9901) uses the remainder's
  `(|R|/10)·log₂ n` bits, which only the high arm supplies.
- **Lean.** `entropyCapDichotomy`
  (`Graph/Strategy/SpineRows/EntropyCapDichotomy.lean`) decides, on the high
  arm after `[52]` (`entropyPackageRow`), `K .entropyCapActive`
  (`budget < demand`) against its exact complement `K .entropyCapBound`
  (`demand ≤ budget`).  The active arm is `[54]`, closed by
  `entropyCapBoundRow.runAndCloseIncompatible`; the bound arm is Residual C
  `[55]` (`highEntropyLargeBudgetRow`).  The low arm reaches `[55]` directly
  (`lowEntropyLargeBudgetRow`).  Callers: `nearCubicLargeBudget*`
  (`proofs/.../Assembly/NearCubic/Spine.lean`).
- **Difference.** The forced-obstruction term `K(1-13θ)` of `eq:entropy-cap` is
  set to `0`: the test is the joint package against the labelled skeleton
  budget.
- **Why the Lean prevails.** It follows the mathematical statements
  (`prop:two-budget`, `prop:entropy-high-theta`) where the diagram disagrees
  with them.  Setting `K = 0` needs no value of `c_Ω` or the rank fraction,
  exactly as `rem:closure-robust` (tex:9936) says the closure outside the
  explicit residuals does; every case the paper closes at `[54]` with `K > 0`
  and the Lean does not is routed to `[55]`, which the Lean handles on the same
  terms as every other `[55]` residual.  The `[24]` high-entropy bound
  `θ ≤ 0.01198542083 = 1.4/116.808581006` is itself the `K = 0` threshold.

## [56]: the density input differs by arm (`lem:dense-deficiency-routing`)

*Family F5 (Spine / Cold / NearCubic).*

- **Paper** (tex:7648-7672): "Nodes [56]--[64] consume the density cap only
  through `def⁺(R) − σ(R) < |R|/4`"; `[161]` supplies it from the deficiency
  test in place of `[24]`.
- **Lean.** Three `[56]` rows publish `K .netDeficiencyCap` from the arm's
  input: `netDeficiencyCapRow` (`[24]`'s `K .densityCap`),
  `denseNetDeficiencyCapRow` (`[160]`'s `K .denseDeficiencyBelow`, the `[161]`
  arm), `routeEightNetDeficiencyCapRow` (`[146]`'s `K .coldRoute8Below`, the
  `[147]` arm, `τ(θ) < 3/13 < 1/4`).  The spine `[47]`--`[56]` is one
  composition per input (`nearCubicLargeBudget*`).

## [57] and [173]: the exact collision test replaces the asymptotic cap

*Family F5 (Spine / Cold / NearCubic).*

- **Paper.** Diagram Part V (tex:915-940): `[56]` → `[57]` "large-budget net
  cap" → `[173]` "exact collision test holds?".  `lem:exact-collision-test`
  (tex:7883) decides `[56]`'s collision exactly on the object;
  `rem:no-sufficient-order` removes the order condition at `[57]`.
- **Lean.** `exactCollisionDichotomy` decides `K .netChargeCap` (the exact
  `N₀(R) < 0` at every maximum packing) against `K .exactCollisionFails`;
  `[57]` has no separate fact.  `bridgelessRow` publishes `lem:bridgeless`
  before the decision because both arms consume it: the absorbed residual's
  corridors, and the Type A / Type B continuations (`[63]`, `[64]`), whose
  signatures require `K .bridgeless`.
- **Why the Lean prevails.** It is the paper's own replacement of `[57]`
  (`lem:exact-collision-test`, `rem:no-sufficient-order`), stated without an
  `n ≥ N₀` hypothesis; `lem:bridgeless` holds on every counterexample.

## [62]: the surplus test is asked of every negative piece

*Family F1 (Type A).*

- **Paper** (diagram tex:922–923; `prop:negative-net-charge`).  Node `[61]`
  chooses a connected `X` with `N₀(X) < 0`; node `[62]` asks whether `σ(X) > 0`.
- **Lean.**  `typeSplitDichotomy`: the yes key `K .typeBHighSurplus` (unchanged:
  some negative canonical piece of a maximal packing has `σ > 0`) and the no key
  `K .typeALowSurplus`, its exact negation (every negative canonical piece of
  every maximal packing has `σ = 0`).  On the Type A arm node `[86]`
  (`typeASupportRow`, `Contracts.TypeA.typeASupport`) instantiates the no key at
  the node-`[61]` piece.
- **Difference / why the Lean prevails.**  Node `[61]`'s choice is free in the
  paper; the Lean split is the paper's test under the choice "a piece with
  positive surplus if one exists".  Both arms continue exactly as the paper's
  arms on the chosen piece, and the split is an exact complement.

## [65]–[85]: Type B facts are stated over the support family, not per entry lane

*Family F2 (Type B).*

- **Paper** (diagram tex:950–1035; `def:typeB-assigned-ledger`,
  `def:decorated-fan-envelope`, `lem:absorbed-germ-fan-data`,
  `lem:same-token-bottleneck-routing`). Node [65] receives one assigned Type B
  support `X = (Y_X, H_X)` from [64], [66]/[108], [177] or [144]; nodes
  [67]–[85] reason about that support.
- **Lean.** `TypeBSupport` (`hypostructure/Hypostructure/Graph/Statements/TypeB.lean`)
  is the family of all assigned supports of the object in the three entry forms
  (`TypeBCanonicalForm`, `TypeBAbsorbedForm`, `TypeBSameTokenForm`). Every
  Type B key is stated over this family: row facts are universal over it, and
  each decision ([68] `typeBFanDegreeDichotomy`, [71]/[80]
  `fanCertificateDichotomy`, [72]/[81] `directCycleDichotomy` and
  `b2AssignmentDichotomy`) is a family predicate and its exact negation, proved
  exact by `typeBFanDegreeFourCentres_iff_not_heavy`,
  `typeBFanCertificateResidual_iff_not_marked`,
  `typeBFanDirectCycleFree_iff_not_directCycle` and
  `typeBB2Obstruction_iff_not_choice` (`Graph/Contracts/TypeB/`). The previous
  three-lane Or keys (canonical | absorbed | same-token) are gone; so are the
  lane `rcases` inside decisions.
- **Why at least as strong.** Every universal fact holds in particular at the
  entering support, so no paper fact about X is weakened. The decisions are
  exhaustive and exclusive on one pinned object (the family is a definable
  predicate of the object, not a chosen witness). Each argument is one
  contract lemma instead of three lane copies. The terminal at [72]
  (a direct configuration is an accepted cycle) closes on either arm of the
  family exactly as the paper closes it for X.

## [69]: routed local dichotomy on the heavy arm

*Family F2 (Type B).*

- **Paper** (tex:971; `cor:heavy-center-local-dichotomy` tex:2322,
  `cor:compatible-pair-typeB-routing` tex:13751,
  `prop:triangular-port-typeB-routing` tex:13779). "fan-compatible open pair or
  k−2 triangular ports gives fan-closed ports".
- **Previous Lean.** `triangularPortTypeBRoutingRow` ran only on the degree-four
  arm, where its hypothesis `5 ≤ d_G(h)` never holds; the heavy arm had no
  triangular routing ([69] recorded as WEAKER).
- **Lean now.** On the heavy arm the fan-closed port rows and both routing rows
  run, and `typeBFanLocalDichotomyRow` publishes
  `HeavyCentreRoutedAlternative` at every heavy assigned centre: either a
  fan-compatible open pair together with `CompatiblePairRoutes` in every
  profile at the centre, or a family of exactly `d_G(h) − 2 ≥ 3` triangular
  ports together with `TriangularPortsRoute` (`D_B ≥ (5k−19)/4`). Contract
  `Contracts.TypeB.heavyCentreRoutedAlternative`. The degree-four arm keeps the
  compatible-pair and fan-closed routing of `cor:degree-four-local-activation`.
  Paper-exact; no deviation remains.

## [70]: fan-safe graph and certificate cap are one fact

*Family F2 (Type B).*

- **Paper** (tex:972, `def:typeB-fan-safe` tex:10845, `lem:fan-certificate`).
  Node [70] is "fan-safe graph, P13 certificate graph, and certificate-marked
  cap d_G(h) ≤ 8".
- **Lean.** `TypeBFanCertificateCapStatement` publishes, at every assigned
  centre, `FanSafeAt` (clause (i) of `def:typeB-fan-safe`: no accepted fan
  return, from the selection) together with the cap; producer
  `fanCertificateCapRow`, contract `Contracts.TypeB.typeBFanCertificateCap`.
  The key `typeBFanSafe` is no longer produced: its previous value was the
  definitional unfolding of the fan-safe relation (a tautology read from no
  fact); its content now lives, as a genuine consequence of the selection, in
  `fanCertificateCap` on every Type B branch (previously it was published only
  on the [177] branch). `TypeBFanSafeStatement` is deleted: no key publishes it.
- **Why at least as strong.** Clause (i) is now a proved fact at every centre
  instead of an iff with arbitrary predicates; clauses (ii)–(v) are defining
  conditions of the fan-safe graph, not claims.

## [74]/[82] → [76]/[85]: no split at the bridge reduction

*Family F2 (Type B).*

- **Paper** (tex:976–979, 1020–1023; `prop:typeB-bridge-reduction`). The B2 yes
  edge goes [74] → [76] → [77]; [74] is not a diamond.
- **Previous Lean.** `typeBExclusionDichotomy` split on the sign of the
  remaining core charge and closed the nonnegative arm inline
  (`NearCubicCertificate`), an arm that was uninhabitable (its `Holds`
  contained both the support's negative charge and `N₀ ≥ 0`).
- **Lean now.** Two rows in paper order: `typeBExcludedRow` ([74],
  `prop:typeB-bridge-reduction`: a B2 ledger with nonnegative remaining core
  gives `N₀(X) ≥ 0`) and `typeBExclusionResidualRow` ([76]: a canonical support
  is negative, so its B2 ledger leaves a negative post-ledger core), then the
  mass row and the route-8 continuation [77]. This is the paper's topology; no
  deviation remains.
- **G-repair.** All three keys are about the one canonical B2 ledger
  `canonicalTypeBDisjointChoice data G Y_X H_X` of the Type B support, read
  from `K .typeBDisjointLedger` (d2ded0e's `[76]` also read that key's
  ledger).  The d2ded0e decision's yes arm is not restored: it was
  unreachable and was closed by a hand-built `False`.

## [65]--[85]: the Type B support is the one support fixed by the entry

*Family F2 (Type B), G-repair.*

- **Paper** (tex 961, `def:typeB-assigned-ledger` tex 12909). Node [65]
  receives one assigned support `X = (Y_X, H_X)`, and every node
  [67]--[85] speaks about that `X`.
- **Previous Lean.** Every key quantified over a family `TypeBSupport` of
  arbitrary maximal packings and envelopes; `({a}, {h})` for any high `h`
  was a member, so the family was "all high vertices of G".  No decision
  read its predecessor.
- **Lean now** (`Statements/TypeBLanes.lean`). Each entry form is a lane
  pinned to R0's canonical object of G: ordinary `(X₀, H(X₀))`
  (`canonicalTypeBOrdinarySupport`, on `K .netChargeCap` and `σ(X₀) > 0`),
  decorated `(X₀, {z})` (`canonicalTypeBDecoratedSupport` with its canonical
  envelope, on `K .netChargeCap` and `σ(X₀) = 0`), absorbed `X_ε`
  (`canonicalTypeBAbsorbedSupport ε`, on `K .exactCollisionFails` with the
  [175] data), and the [144] same-token handoff (on `K .surplusAbove`; no
  continuation runs there).  The lanes are mutually exclusive
  (`Contracts.TypeB.ordinary_decorated_exclusive`,
  `netChargeCap_not_exactCollisionFails`; the same-token lane by
  `surplusAbove`/`surplusAtOrBelow`), so each decision's two arms
  `TypeBLaneSome P` / `TypeBLaneAll ¬P` are exact complements at the one
  support (`TypeBLaneSome.not_all`).  Decisions read their d2ded0e
  predecessor: [68] `typeBFanEntry`, [71] `fanCertificateCap`, [72]
  `fanCertificateMarked`, B2 `typeBDirectCycleFree`; [70] reads
  `typeBFanEntry`, [69] `typeBFanHeavyCentre`, the global-local bridge
  `typeBOverlapObstruction`, its mass `typeBGlobalLocalBridge`.  The window
  union is `W₀ = windowSupport P₀` and the fan envelope is
  `canonicalEnvelope G h` throughout; the bridge statements are at `P₀` and
  at G's canonical piece collections.
- **Triangular keys** (`def:triangular-fan-core`, tex 2378; tex 2413, 2452,
  2489, 2521). They are stated at a *heavy* center (`d_G(h) ≥ 5`,
  `def:heavy-center-triangular-port` tex 2223), and so run on the heavy arm
  [69], feeding `prop:triangular-port-typeB-routing` (tex 13780); the
  degree-four arm runs only the routings used by
  `cor:degree-four-local-activation` (tex 2336).  The paper's
  cross-reference table (tex 1871--1881) lists these lemmas at [78]--[81];
  that contradicts their own statements, which are followed here.

## [89], [93], [95], [97], [99], [101], [103], [105], [107]: each exit test is asked of every candidate at once

*Family F1 (Type A).*

- **Paper** (diagram tex:1057–1077 and 1081–1103; `def:typeA-saturated-exits`
  tex:10811; `lem:typeA-visible-entry` tex:11208;
  `lem:typeA-unpeeled-visible-routing` tex:11484;
  `lem:typeA-unpeeled-silent-routing` tex:11540;
  `lem:typeA-exit4-residual-routing` tex:11606).  Each diamond asks its
  question of the Type A support `X`, the saturated receiver `w`, its port and
  its current peeling set `P₄(w)` fixed by the preceding nodes.
- **Lean.**  Each diamond is a `Decision` whose yes key is the paper's
  alternative at *some* candidate of the canonical packing (a negative
  zero-surplus canonical piece, a saturated receiver of it, the canonical
  overloaded-port package or a saturated peeling set) and whose no key is the
  exact logical negation of the yes key, stated in positive form over *every*
  candidate:
  - `[89]` `typeASaturationDichotomy`: `K .typeASaturatedReceiver` /
    `K .typeAUnsaturatedReceivers`;
  - `[93]` `typeAVisibleEntryDichotomy`: `K .typeAVisibleEntry` /
    `K .typeANoVisibleEntry`;
  - `[95]`, `[97]`, `[99]` `typeAExit{One,Two,Three}Dichotomy`;
  - `[101]` `typeAExitFourDichotomy`: `K .typeASaturatedHandoffExitFour` /
    `K .typeAExitFourAbsent`;
  - `[103]`, `[105]` `typeAExit{Five,Six}Dichotomy`;
  - `[107]` `typeAExitSevenDichotomy`: `K .typeAExitSevenHandoff` /
    `K .typeAExitSevenAbsent`.
  Every decision is `by_cases` on the yes-arm proposition, and the complement
  is the contract lemma `Graph.Contracts.TypeA.*_of_not_*`
  (`hypostructure/Hypostructure/Graph/Contracts/TypeA/{Support,Exits}.lean`).
  The continuation of a no arm reads the state it continues at from an earlier
  fact on the same ledger and instantiates the universal negation there
  (`typeAVisibleFirstExcess`, `typeASaturatedHandoffExitFourFree_of_absent`,
  `typeAExitSevenFree`).
- **Difference.**  The paper's no arm is the negation at the fixed candidate;
  the Lean's no arm is the negation at every candidate, which specializes to
  the paper's no arm at the fixed one.  The paper's yes arm at the fixed
  candidate is an instance of the Lean's yes arm.
- **Why the Lean prevails.**  The two keys are the exact complement of one
  proposition about the selected object, so no arm is assumed and no witness
  is chosen separately in the two arms.  Every yes arm is closed (or handed
  off) by the same lemma the paper uses at the fixed candidate
  (`lem:typeA-exits-discharged`, closure contracts in
  `Contracts/TypeA/Exits.lean`), and every no arm is at least the paper's.

## [102] → [89]: the recompute-`L₄` loop is realized by its terminating outcome

*Family F1 (Type A).*

- **Paper** (diagram tex:1070 and 1095, "recompute `L₄`";
  `lem:typeA-exit4-discharge` tex:11628; `lem:typeA-saturated-handoff`
  tex:11753; `rem:typeA-exit4-peeling-use` tex:11785).  After a peel the
  receiver is tested again at `[89]` and the loop repeats until the receiver is
  unsaturated or a non-peeling exit occurs; the loop is finite because every
  peel lowers `L₄(w)`.
- **Lean.**  An append-only ledger cannot commit the same keys twice, so the
  loop is committed as one exact retest after the first peel:
  `typeAExitFourRetestDichotomy`, yes key `K .typeASaturatedHandoffExitFourFree`
  (some saturated peeling state is exit-`(4)`-free: exits `(5)`--`(8)` are
  asked there, `selectedTypeAExitFiveToEight`), no key
  `K .typeAExitFourExhausted` (its exact negation: every saturated peeling state
  still realizes exit `(4)`).  On the no arm `typeAExitFourDischargedRow`
  (`Contracts.TypeA.typeAExitFourReceiverDischarged`) runs the finite descent
  of `lem:typeA-saturated-handoff` from the peeled state and publishes the
  unsaturated receiver with nonnegative remaining charge
  (`lem:typeA-exit4-peeling-charge`), whose target-defect loads enter Part IX
  at `[123]` (`selectedTypeAExitFourDischargedRetest`).
- **Why the Lean prevails.**  The retest is an exact dichotomy, the descent is
  kernel-checked, and the two outcomes are exactly the outcomes the paper's loop
  can end in (`lem:typeA-saturated-handoff`).  The loop's intermediate
  re-tests of exits `(1)`--`(3)` are not repeated: exits `(5)`--`(8)` do not use
  their negations, so nothing the paper proves is lost.

## [106]: the scope of exit `(6)` is an exact decision

*Family F1 (Type A).*

- **Paper** (diagram tex:1074; `lem:typeA-exits-discharged` tex:11658,
  "Exit (6) is excluded by `lem:proper-smearing` in the proper-support case and
  by `lem:no-silent-global-smearing` in the whole-graph case").
- **Lean.**  `typeAExitSixScopeDichotomy`: yes key `K .typeAExitSixProperScope`
  (some exit-`(6)` delocalization adjoins a proper support), no key
  `K .typeAExitSixGlobalScope` (its exact negation).  Each arm commits the
  smearing lemma's conclusion (`typeAExitSixProperRow`,
  `typeAExitSixGlobalRow`) through `AtomicCT.runAndCloseIncompatible`, against
  `K .replacementExclusion`, respectively `K .selection`.
- **Difference.**  The old Lean split on the output of `Delocalization.localize`
  (an `Or` of the two conclusions); the paper's case split is on the support.
  The Lean now splits on the support, as the paper does.

## [109]: the route-`8` residual is split by its node-`[94]` provenance

*Family F1 (Type A).*

- **Paper** (diagram tex:1077, 1143; `lem:typeA-unified-visible-ownership`,
  node `[184]`).  The route-`8` residual `[109]` continues through Part IX; node
  `[184]` proves that every entry of the unified family is visible.
- **Lean.**  `typeASilentExitSevenDichotomy` after the node-`[109]` row: yes key
  `K .typeASilentExitSevenFree` (a route-`8` residual state whose Type A support
  has the node-`[94]` silent-excess origin), no key `K .typeAExitEightNotSilent`
  (its exact negation).  The yes arm is closed at `[184]` by the instance
  `typeASilentExitSevenFreeVisibleClosed`
  (`Contracts.TypeA.selectedSilentExitSevenFree_unifiedVisibleResidual_contradiction`):
  the origin's excess load is a silent member of the unified family, which
  `[184]` makes visible.  The no arm continues through Part IX exactly as the
  paper's residual.
- **Why the Lean prevails.**  The split is an exact complement, it weakens no
  fact, and it closes the silent-origin residual that the paper's `[184]` makes
  vacuous but does not close separately.  Before this change the same closure
  was reached by running a second, silent copy of the exit segment; the two
  lanes now share one exit segment, as the diagram draws the edge `[94]` →
  `[101]`.

## [113]: the large-budget deficit is tested, not asserted

*Family F3 (Route 8).*

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

*Family F3 (Route 8).*

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

*Family F3 (Route 8).*

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

## [131] and [137]: the count-fails arm is the negation of the count

*Family F4 (Surplus / Homogeneous / Pair).*

- **Paper** (diagram tex:1225-1231). "count fails" (resp. "count fails on the
  free side") continues at [178].
- **Lean.** `freePairEntropyDichotomy` / `blockedPairEntropyDichotomy` decide
  the count predicate itself; the no arms `K .freePairCountFails`,
  `K .blockedPairCountFails` are its literal negation.  The first failed pair
  extension that [178] consumes is derived afterwards by
  `freePairCodeUnrealizedRow` / `blockedPairCodeUnrealizedRow` (contract lemmas
  `freePairCodeUnrealized_of_countFails`,
  `blockedPairCodeUnrealized_of_countFails`), for the node-[129] baseline
  family and the node-[136] presentation read from the ledger.
- **Why the Lean is at least as strong.** If the count held for the ledger's
  baseline family it would witness the yes arm, so the count fails for that
  family; the derived facts are exactly the paper's [178] input.

## [137] on the independent branch: one exact coupled-excess test, both arms closed by [138]

*Family F4 (Surplus / Homogeneous / Pair).*

This entry supersedes the `freePairCoupledExcessDichotomy` entry of
`lean-vs-paper-discrepancies.md` ("[137] on the independent branch").

- **Paper** (diagram tex:1204, 1229-1246; `prop:single-graph-sparse-pressure-routing`).
  The [131] "count holds: free pairs" edge enters the [137] diamond
  "coupled excess D_all>0?"; D_all = 0 goes to [138], D_all > 0 to [139].
- **Lean.** The free side runs the same exact decision as the blocked side,
  `coupledExcessDichotomy`
  (`hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/FibrePressure.lean`):
  `K .sparsePressureOverload` versus its literal negation
  `K .sparsePressureNearCubic`.  On the independent branch both arms run
  `freePairSurplusEstimateRow`
  (`HomogeneousBottleneckRows/FreePairCoupledExcess.lean`, contract lemma
  `Graph.Contracts.SurplusPair.spineSurplusEstimate_of_pairSandwich`) and close
  through `runAndCloseIncompatible … (K .surplusAbove) (K .spineSurplusEstimate)`.
  Caller: `Assembly.Internal.strictSurplusIndependent`
  (`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict/Independent.lean`).
- **Difference.** The D_all > 0 arm on the free side is closed by [138]'s
  estimate instead of continuing to [139].  The earlier Lean
  `freePairCoupledExcessDichotomy` published the estimate itself as its no-arm
  key, so its keys were not complements; it is deleted.
- **Why the Lean prevails.** The [131] count gives σ(G) ≤ C_sp⌈√n⌉ on the whole
  count-holds branch, whatever D_all is, which contradicts [19]; the paper's
  "no blocked pairs, so D_all = 0" needs a link between the overload ledger's
  entropy budget and E_spine that the paper does not state.  The contradiction
  uses only [131], [126] and [19], is kernel-checked, and closes the arm.

## [139], [141], [143]: the class tests are on the existence of an overload witness in the class

*Family F4 (Surplus / Homogeneous / Pair).*

- **Paper** (diagram tex:1204-1208, 1240-1244). [139] asks whether "the
  overloading token" of [137] lies in 𝔗_W, [141] whether it lies in 𝔗_R, and
  the no-no arm is the primitive audit [143].
- **Lean.** `windowOverloadClassDichotomy` and `remainderOverloadClassDichotomy`
  (`HomogeneousBottleneckRows/WindowOverloadClass.lean`) decide, by exact case
  analysis, whether some overload witness of the object has its token in 𝔗_W
  (resp. 𝔗_R); the no arms `K .windowClassAbsent`, `K .remainderClassAbsent`
  are the literal negations.  `primitiveClassOverloadRow` (contract lemma
  `Graph.Contracts.SurplusPair.primitiveClassOverload_of_classesAbsent`) then
  shows that the [137] overload witness is primitive.  Each audit
  ([140] `windowBottleneckAuditRow`, [142] `remainderBottleneckAuditRow`, [143]
  `primitiveBottleneckAuditRow`, all through the one contract lemma
  `homogeneousBottleneckPattern_of_overloadAtClass`) reads the witness of its
  own class.
- **Difference.** The earlier Lean tested the class of one witness chosen
  inside the decision, and its two keys were two existentials over separately
  chosen witnesses (not complements).  The Lean now tests the class predicate
  itself.
- **Why the Lean prevails.** The three audits apply to every overload witness
  with no further hypothesis, so choosing a 𝔗_W (then 𝔗_R) witness whenever one
  exists routes every object to an audit of a class its overload actually
  has; the keys are exact complements on the object, and no arm is lost.

## [181]/[183]: quantification over maximal ledgers

*Family F3 (Route 8).*

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

## [182]: each pair-code test has its own exact negation

*Family F4 (Surplus / Homogeneous / Pair).*

- **Paper** (diagram tex:1211-1214, 1232-1236; caption tex:1255). The
  failures of the [178], [179] and [180] implications meet only at the open
  node [182].
- **Lean.** Each test is an exact decision with its own negation key
  (`K .pairFactorizationFails`, `K .pairRealizabilityFails`,
  `K .pairIncrementFails`); a row on each negative arm
  (`pairFactorizationResidualRow`, `pairRealizabilityResidualRow`,
  `pairIncrementResidualRow`) publishes the one [182] outcome
  `K .pairConditionalFactorizationResidual` with the literal object on which
  the implication fails.  The [179] and [180] outcome splits are likewise
  exact (`K .pairSystemNoEarlyOutcome`, `K .pairIncrementNoEarlyOutcome`), and
  the serial system / arithmetic input is derived on the negative arm
  (`pairSerialDemandSystemRow`, `pairSerialArithmeticRow`).
- **Difference.** None in topology: the three failures still meet at [182].
  The paper leaves the three implications unproved and declares [182] open;
  the root boundary `SelectedLedgerBoundaryResult` keeps that outcome, and
  this migration does not attempt the open implications.

## [184]: the silent Type A lane closes at the visibility reduction

*Family F3 (Route 8).*

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

## Remaining divergences (not admitted under the exception), family F5

- **[49]** `Graph.RemainderClass` drops the paper's subcubicity on the
  boundaried-piece part, adds `|E| = |E(R)|` (needed by the `RemainderGlue`
  injection at `[54]`/`[164]`), and caps `def⁺` at `def⁺(R)` rather than at the
  branch's current net-deficiency cap.  Not changed in this pass.
- **[165]/[166]** The paper's `Φ`-decrease (`lem:refined-minimality-swap`,
  tex:7732) needs the refined order to compare the multisets of canonical
  decomposition pieces; the Lean's third coordinate
  (`canonicalDecompositionCode`) is a well-order on labelled skeletons, for
  which a canonical exchange `Q → E` does not provably decrease.  The `[163]`
  row therefore defines the representative as canonical only when the swap is
  refined-smaller.  Not changed in this pass.
- **[156]** The family-F5 entry "G2 closes through the sparse exit (b) (gap
  repair)" was reverted at integration: the closure went through sparse exit
  clause (b), which appears to accept any two boundary pieces and would close
  the branch vacuously.  G2 is recorded again and the cold outcome returns to
  `[187]` (`K .coldBranchClosed`), as at `d2ded0e`.

## Paper errors

Each entry is a claim of the paper that is not established, stated faithfully
at its node.  In the live Lean tree it is either a `sorry` tagged
`-- PAPER-ERROR [node] tex:<line>` on the proof of exactly that claim, or,
where the user decided so, a residual carried by the node's open leaf.

### [144] `lem:same-token-bottleneck-routing`, parallel and cubic-first-separator cases (tex 5585-5620)

- **Paper claim.** The two same-label demands' response coordinates "lie in the
  same boundary-degree fibre" (tex 5589).  Their identification is either
  target-defective (exit (b)) or "target-complete on a proper support", which
  "`lem:replacement`, `cor:uncompressible` give [as] the target-complete
  compression exit" (tex 5594; tex 5614 is the same claim at a cubic first
  separator).
- **Faithful Lean statement.** Read the two coordinates on G's own piece at the
  canonical support `Z` of their union (`SupportAtom.retainedPiece`).  The case
  with equal fibres and a separating context is exit (b) at G's declared family
  (`declaredSparseSurplusExit_of_pairDefect`).  Two cases remain:
  - the readings lie in different fibres; the routing label records the `T(p)`
    profile, not the reading at `Z`;
  - the readings are context-equivalent.
- **Why it fails.** `def:admissible-rank-quotient` (tex 6026-6029): "a
  target-complete proper-support correlation that has no smaller graph
  representative is not an admissible rank reduction."  The paper never
  constructs the smaller representative that exit (c) needs.
- **Counterexample.** `Quarantine/PaperRepairs/Node144Gap.lean` gives the
  survivor dichotomy L1′ (a target-complete pair adds no exit, L3) and two
  locally G-valid configurations, F1 (a shoulder star) and F2 (a binary cubic
  funnel), that reach [144] with no exit.
- **Representation (user decision).** No `sorry`.  The two remaining cases are
  `SameTokenPatternPairUnresolvedStatement` (key
  `K .sameTokenPatternUnresolved`), published on the no-handoff arm of the exact
  decision `sameTokenHandoffDichotomy` (`K .typeBHandoff` /
  `K .typeBHandoffFails`).  They are carried by the open leaf [144a]:
  `Node144aOutcome` is the handoff, or the unresolved pattern pair, together
  with every [144] retained fact.

### [153] (F2) exclusion, `lem:cold-corridor-first-failure` (ii) (tex 7265-7270)

- **Paper claim.** An (F2) first failure is "a target-defective quotient ...
  exactly the sparse exits ... excluded in `def:surviving-cold-branch`".
- **Faithful Lean statement.** `Contracts.Spine.coldFailureDefect_excluded`:
  on the survivor (`K .sparseSurplusSurvivor`), no (F2) event occurs.  The row
  reads the survivor key, as at d2ded0e.
- **Why it fails.** The (F2) pair compares two corridor prefixes through their
  cut-state interface (tex 7187-7197).  It is not an identification of two
  declared coordinates of G's sparse family: demands, pairs and spine
  coordinates (tex 2769-2772).  The two readings of an (F2) pair are the retained
  piece `retainedPiece(prefix_right, prefix_left)` and the piece
  `piece(prefix_right)`, and they have different boundary-degree profiles on
  `∂prefix_right`.  So the pair is not a clause-(b) exit, and the survivor fact
  does not refute it.
- **Tag.** `sorry`, `PAPER-ERROR [153] tex:7268`, in
  `Graph/Contracts/Spine/ColdFirstFailure.lean`.

### [153]/[175] full charge of a subcubic cold half-edge, `lem:absorbed-germ-fan-data` (i) (tex 7920-7922) with `lem:cold-germ-extraction` (tex 7318-7322)

- **Paper claim.** A half-edge whose first-failure support is subcubic "is
  charged in full" by the extraction count, i.e. it is an (F5) candidate.  The
  (F4) handoff incidences are "already routed" and removed at `o(n)` cost.
- **Faithful Lean statement.** `Contracts.Spine.coldSubcubicFirstFailureGerm`:
  on the routed classification (every half-edge is (F5) or (F4)), a subcubic
  first-failure prefix is (F5).
- **Why it fails.** The registry the paper declares at (F4) (tex 7234) consists
  of declared Type B envelope cores and route-8 response supports.  A corridor
  whose foot lies in such a support is (F4) at segment 0, even when the support
  is subcubic (`Quarantine/PaperRepairs/ColdF4Charge.lean`,
  `coldF4_of_foot_declared`).  The paper neither bounds nor excludes these
  half-edges.
- **Tag.** `sorry`, `PAPER-ERROR [153] tex:7920`, in
  `Graph/Contracts/Spine/ColdSubcubicCharge.lean`.
- **Inconsistency.** Tex 7926-7934 (`lem:absorbed-germ-fan-data` (ii)) reads a
  handoff as reaching a vertex of degree ≥ 4 (the heavy-centre reading).
  Tex 7234 declares whole supports.  Lean implements the (F4) definition as
  stated at its node (tex 7234).  The heavy-centre reading is quarantined in
  `Quarantine/PaperRepairs/ColdF4Charge.lean`.
