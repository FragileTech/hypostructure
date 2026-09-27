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

## [62]: now paper-exact at the node-[61] support

*Family F1 (Type A).*

- **Paper** (diagram tex:922–923; `prop:negative-net-charge`).  Node `[61]`
  chooses a connected `X` with `N₀(X) < 0`; node `[62]` asks whether `σ(X) > 0`.
- **Lean.**  `typeSplitDichotomy` reads `K .negativeSupport`, fixes
  `X₀ = canonicalNegativePiece` (the canonical choice of node `[61]`'s
  existential) and splits on `σ(X₀) = 0`: `K .typeALowSurplus` /
  `K .typeBHighSurplus`, exact complements at `X₀`.  No divergence remains.

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

## [89], [93], [95], [97], [99], [101], [103], [105], [107]: now paper-exact at the fixed objects

*Family F1 (Type A); final fix pass TA.*

- **Paper** (diagram tex:1057–1077 and 1081–1103; `def:typeA-saturated-exits`
  tex:10811).  Each diamond asks its question of the fixed `X`, `w`, port and
  `P₄(w)`.
- **Lean.**  Every Type A key is pinned (`Statements/TypeA.lean`,
  `AtTypeASupport` / `AtVisiblePort` / `AtExitReceiver` / `AtTerminalState` /
  `AtPeeledVisiblePort`) to the canonical objects of `G`
  (`Statements/CanonicalTypeA.lean`): `X₀`, the node-`[89]` receiver, the
  node-`[93]` visible receiver and its overloaded port, the exit-chain receiver,
  the terminal receiver of the recompute-`L₄` retest
  (`canonicalTerminalReceiverAt`) and its terminal set.  Every decision reads
  its predecessor key (`[89]` ← `[88]`, `[97]` ← `[95]`-no, `[99]` ← `[97]`-no)
  and splits at those objects; both keys are the node's predicate and its
  negation.  `[88]` is pinned at `X₀` (`ZeroSurplusRoutingAt`, from node
  `[13]` and `[63]`).  Exit `(3)` is the paper's: two receiver-entry returns
  through the pinned port fail `C_s` at a common packed window of `P₀`
  (`ExitThreeThrough`), closed at `[100]` by the accepted cycle
  (`K .typeAExitThreeCycle`).  Exit `(7)` is asked at the terminal state's
  receiver and eligible loads (`ExitSevenAt`), and node `[108]` is its own row
  (`K .typeAExitSevenEnvelope`: the canonical separation of `X₀` is the one of
  that state, and its decorated handoff fan envelope exists), read by the Type B
  entry.  No divergence remains.

## [102] → [89]: the recompute-`L₄` loop is realized by its terminating outcome

*Family F1 (Type A); final fix pass TA.*

- **Paper** (diagram tex:1070 and 1095, "recompute `L₄`";
  `lem:typeA-exit4-discharge` tex:11628; `lem:typeA-exit4-residual-routing`
  tex:11606; `lem:typeA-saturated-handoff` tex:11753).  After a peel node
  `[89]` is asked again with `L₄`, and the saturated branch re-enters `[93]`
  and exits `(1)`--`(7)`; the loop is finite because every peel lowers `L₄`.
- **Lean.**  An append-only ledger cannot commit the same keys twice, so the
  repeated peels are the canonical witnessed peeling sequence `canonicalPeel`
  of each receiver, stopped at its terminal set `P₄(w)`.  After node `[102]`,
  `typeAExitFourRetestDichotomy` reads `K .typeAExitFourPeeled` and asks node
  `[89]` over the receivers of `X₀` at their terminal sets: yes
  `K .typeAPeeledSaturatedReceiver` at the terminal receiver; no
  `K .typeAExitFourReceiverDischarged` (node `[90]` with `L₄`), followed by
  node `[91]`'s bound on the unpeeled loads
  (`K .typeAPeeledUnsaturatedDischarge`).  On the yes arm node `[93]` is asked
  again at `P₄(w)` (`typeAPeeledVisibleEntryDichotomy`): exits `(1)`--`(3)` at
  the overloaded port of `P₄(w)` with closures `[96]`, `[98]`, `[100]`
  (`typeAPeeledExit*Dichotomy`), or node `[94]`'s residual excess `E₄(w)`
  (`K .typeAPeeledSilentExcess`); node `[101]` then holds at the terminal set,
  and exits `(5)`--`(8)` are asked there.
- **Per-peel retest (final fix pass R8).**  The paper asks `[89]` after
  every peel (`rem:typeA-exit4-peeling-use`, tex 11785-11792; tex 1095).  The
  canonical step `canonicalPeelStep` advances only when the receiver is
  saturated at the current set *and* exit `(4)` has a witness there, so
  `canonicalPeel_retest_of_ne_terminal` (`Statements/CanonicalTypeA.lean`)
  proves, at G's own peel states (every receiver of G's `X₀`, every stage of
  G's canonical sequence) other than the terminal
  set, `[89]` answers saturated, `[101]` answers exit `(4)` with that stage's
  canonical witness, and `[102]` peels exactly that load.  The terminal set is
  therefore the first stage at which the per-peel retest is not followed by a
  peel -- the first unsaturated stage (`[90]`, the no arm) or a saturated
  exit-`(4)`-free stage (`[93]`--`[109]` again, the yes arm); by
  monotonicity of `L₄` in the peeling set, "some receiver saturated at its
  terminal set" is exactly "some receiver saturated at every stage".  The
  per-peel answers are published on the ledger as the last clause of
  `K .typeAExitFourFiniteDescent` (`TypeAExitFourFiniteDescentFact`).  Exits
  `(1)`--`(3)` at an intermediate stage are accepted-cycle contradictions at
  any peeling set (`[96]`, `[98]`, `[100]`), so not re-asking them there removes
  no surviving state.  The no arm's node `[92]` is recorded under Paper
  errors.

## [106]: the scope of exit `(6)` is an exact decision

*Family F1 (Type A).*

- **Paper** (diagram tex:1074; `lem:typeA-exits-discharged` tex:11658).
- **Lean.**  `typeAExitSixScopeDichotomy` reads `K .typeAExitSix` and splits on
  the enlarging support `Z` of the one canonical exit-`(6)` delocalization of
  the terminal state (`canonicalExitSixDelocalizationAt`): proper
  (`K .typeAExitSixProperScope`, `lem:proper-smearing`, closed against
  `K .replacementExclusion`) or `Z = V(G)` (`K .typeAExitSixGlobalScope`,
  `lem:no-silent-global-smearing`, closed against `K .selection`).
- **Difference.**  d2ded0e split on the output of `Delocalization.localize`
  (an `Or` of the two conclusions) at the same delocalization; the paper's case
  split is on the support, and the Lean splits on it.

## [109]: no provenance split (removed)

*Family F1 (Type A); final fix pass TA.*

The former split of node `[109]` by the node-`[94]` silent provenance
(`typeASilentExitSevenFree` / `typeAExitEightNotSilent`) is removed: node
`[109]` continues to node `[110]` on every lane, as in the diagram
(tex:1077, 1122).  The closure it fed at node `[184]` is quarantined
(`Quarantine/PaperRepairs/SilentLaneClosure.lean`).

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

## [139], [141], [143]: now paper-exact at the overloading token of G

*Family F4 (Surplus / Homogeneous / Pair).*

The class tests ask about *the* overloading token of `[137]`
(`canonicalOverloadClass`, the class of the canonical token of G's canonical
certified ledger).  `windowOverloadClassDichotomy` reads `[137]`'s overload arm
and splits `class(t) = 𝔗_W` against `class(t) ≠ 𝔗_W`;
`remainderOverloadClassDichotomy` reads `[139]`'s no arm and splits
`class(t) = 𝔗_R` against its negation; the no-no arm is `class(t) = 𝔗_prim`
(`primitiveClassOverloadRow`).  The audits `[140]`/`[142]`/`[143]` publish the
canonical homogeneous pattern at that token
(`homogeneousBottleneckPattern_of_class`).

## [181]/[183]: the committed maximal ledger `P₀`

*Family F3 (Route 8).*

- **Paper** (`thm:typeA-unpaid-exit4-reduction`, tex:17142--17220). Fix the
  lexicographically first maximal ledger `P` of `def:typeA-pressure-ledger`;
  (168.1) holds for `Ξ_un(P)`; outcome (i) "some `ξ ∈ Ξ_un(P)` has no exit-(4)
  witness" versus outcome (ii) (168.2).
- **Lean.** The ledger is `P₀ = canonicalRoute8Partition`
(`Statements/CanonicalRouteEight.lean`), the `Classical.choice` of the
  node-`[349]` record `K .route8DemandLedger`: a maximal pinned ledger.
  (168.1) (`Route8UnpaidTwoCarrierStatement`), node `[181]`'s yes arm
  (`Route8UnpaidWitnessFreeStatement`) and its exact negation (168.2)
  (`Route8UnpaidExitFourResidualStatement`) are all stated at `P₀`
  (`Statements/RouteEightPinned.lean`); the decision reads `[349]`.
- **Remaining difference.** `P₀` is a maximal ledger chosen by
  `Classical.choice`, not the paper's lexicographically first one.  The paper
  uses only properties every maximal ledger has.

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

## [184]: no separate silent lane (removed)

*Family F3 (Route 8); final fix pass TA.*

With the `[109]` provenance split removed, both Type A lanes run
`[110]`--`[186]` through the one composition `selectedRouteEightResidual`; the
silent-lane copy `selectedRouteEightResidualSilent` and its `[184]` closure are
gone.

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
  on the survivor (`K .sparseSurplusSurvivor`), the first failure of a selected
  half-edge `ε` of G, read on G's retained occurrence (corridor, presentation
  and index of the classified data), is not (F2) (restated 2026-09-26, see the
  addendum).  The row reads the survivor key, as at d2ded0e.
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
- **Addendum (2026-09-26): the evidence, and the hook restated.**
  `Quarantine/PaperRepairs/ColdF2Refutation.lean` (Lean-checked, no `sorry`,
  standard axioms):
  - `prefix_zero_profile_ne`, `not_residualTargetDefect_prefixPair_zero`: for
    every corridor of G in an outside component and every `right > 0`, the
    readings `retainedPiece(J_right, J_0)` and `retainedPiece(J_right,
    J_right)` have different `d_∂` (the entry foot is on `∂J_right` and loses
    its corridor edge to `head 1`), so the prefix coordinates `{J_0, J_right}`
    carry no clause-(b) defect for any target predicate
    (`prefixPair_residualTargetDefect_profile`: clause (b) on the prefix pair
    is read at `Z = select?(J_l ∪ J_r) = J_r` and forces equal `d_∂`).
  - `coldFirstFailureDefectAt_one_iff`, `coldF2_not_clauseB`: on an object of
    minimum degree `≥ 2` with `4 ∈ LengthOK`, the Lean (F2) at segment 1 of
    every corridor of length `≥ 1` is exactly "states 0 and 1 agree" (the
    length-3 path context from the foot to `head 1` closes a 4-cycle with
    `J_1` and none with the edgeless `J_0`), while `{J_0, J_1}` is never a
    clause-(b) exit.  So (F2) ⇏ sparse exit.
  - `edge_twoPath_sameFibre_targetDefect`: reading prefixes instead through
    their two-label cut-state interface `T(J) = {foot, head}` (tex 7187-7197)
    puts `J_1` (an edge) and `J_2` (a two-edge path) in the same `d_∂ = (1,1)`
    fibre and separates them by a context, so such a clause (b) would fire on
    every corridor of length `≥ 2` and make the surviving branch vacuous.
    Neither reading makes the paper's step valid.
  - `coldFailureDefect_excluded_is_false`: the previously committed statement
    of `Contracts.Spine.coldFailureDefect_excluded` quantified over every
    corridor, presentation, index and segment, and is **false** (constant
    index: states agree, (F2) fires at segment 1).  A `sorry` of a false
    statement proves anything about G, which is forbidden.  It is therefore
    restated, without changing the paper claim, at exactly the objects where
    its only consumer `coldFailureRouting_of_failures` applies it: G's retained
    occurrence (`coldOccurrenceCorridorAt` / `coldOccurrencePresentationAt` /
    `coldOccurrenceIndexAt` of the classified data), at a segment that is the
    first failure (no earlier (F1)--(F5) event): "the first failure of `ε` is
    not (F2)".  The refutation does not apply there: the retained index is
    injective (`coldOccurrenceStateFacts … .2.2.1`), so a constant index is
    excluded as soon as segment 1 exists (checked in Lean), and the states are
    G's chosen ones.  The restated claim is still not proved -- it fails at a
    G whose retained presentation has equal states at segments 0 and 1 with
    no event at segment 0 -- but whether G's retained presentation is such is
    not determined, so the statement is not refutable.  The tag stays
    `sorry -- PAPER-ERROR [153] tex:7268`.

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
- **Tag (historical).** `sorry`, `PAPER-ERROR [153] tex:7920`, in
  `Graph/Contracts/Spine/ColdSubcubicCharge.lean`.  **Resolved 2026-09-26** by
  the user-approved (F4) repair below: the sorry is replaced by a proof, with
  the statement unchanged.
- **Inconsistency.** Tex 7926-7934 (`lem:absorbed-germ-fan-data` (ii)) reads a
  handoff as reaching a vertex of degree ≥ 4 (the heavy-centre reading).
  Tex 7234 declares whole supports.  Lean implements the (F4) definition as
  stated at its node (tex 7234).  The heavy-centre reading is quarantined in
  `Quarantine/PaperRepairs/ColdF4Charge.lean`.

### [92] after peeling: the unsaturated charge does not close once a load is peeled (tex 1095, 11753, 11785)

*Final fix pass TA.*

- **Paper's claim.**  The diagram returns node `[102]` to `[89]` "with the
  residual load `L₄`" (tex 1095 and caption), and the no arm of `[89]` closes at
  `[92]` ("unsaturated Type A charge closes").
- **Faithful formal statement.**  On the retest's no arm every receiver of
  `X₀` has `1 + L₄(w) ≤ s·q(w)` at its terminal set
  (`K .typeAExitFourReceiverDischarged`).  `lem:typeA-exit4-peeling-charge`
  then gives exactly `|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|`
  (`K .typeAPeeledUnsaturatedDischarge`,
  `Contracts.TypeA.card_le_scaled_deficiency_add_peeled`).
- **Why it fails.**  `[92]` closes against `[86]`, `s·def⁺(X₀) < |V(X₀)|`.  On
  this arm node `[102]` has peeled at least one load of the exit-chain
  receiver (`K .typeAExitFourPeeled`), so `Σ_w |P₄(w)| ≥ 1` and the bound above
  does not contradict `[86]`.  The statement `|V(X₀)| ≤ s·def⁺(X₀)` cannot be a
  `PAPER-ERROR` sorry: its negation is `[86]`, which is on this very ledger.
  The paper itself routes this case elsewhere: `rem:typeA-exit4-peeling-use`
  (tex 11785-11792) says the charge calculation applies only to the unpeeled
  loads and a support with an exit-`(4)` witness "is routed by alternative (iii)
  of `lem:density-mersenne`" (tex 11860-11863).
- **Lean.**  The arm follows that routing: after `[91]` it enters the unified
  target-defect/route-`8` ledger of node `[123]`
  (`selectedTypeAExitFourDischargedRetest`,
  `Assembly/TypeA/ExitFourDischargedRetest.lean`).  No `sorry`.

### [348] `lem:typeA-unified-carriers`: alternative (b) of `def:typeA-trace-basin` at the unified entries is "a standing-invariant contradiction" (tex 15360-15364, 15336-15339)

*Final fix pass R8 (supersedes the TA entry "[123] / key 348").*

- **Paper's claim.**  `lem:typeA-unified-carriers` (tex 15360-15364): at an
  entry of `\tilde\Xi`, "Alternatives (b)--(d) are exits (5),(6),(7): the first
  two are standing-invariant contradictions (`cor:uncompressible`,
  `lem:proper-smearing`, `lem:no-silent-global-smearing`)"; the census of
  `lem:typeA-unified-deficit` (tex 15336-15339): "exits (5),(6) are
  contradictions".
- **Faithful formal statement.**
  `Contracts.RouteEight.route8QuotientFree_of_uncompressible`
  (`Graph/Contracts/RouteEight/EntryCensus.lean`), a library contract applied
  only at G (`instIncompatibleRoute8QuotientResidualSelection`, fed by G's
  selection fact, G's baseline, the registered cubic/dyadic presentation and
  G's uncompressibility): no entry of G's unified collection (and no entry of
  G's extracted route-8 cores) carries a nontrivial target-complete response
  quotient -- `Route8QuotientFreeStatement` at G, the node-`[347]` predicate.  Its proof is
  `sorry -- PAPER-ERROR [348] tex:15362`.
- **The failing step, about G.**  The paper's argument at `[123]` is: an entry
  `ξ = (X, w, u, B_u)` of G's unified collection whose trace basin `B_u`
  realizes alternative (b) contradicts `cor:uncompressible` for G.  That
  contradiction needs the fact *"G's response quotient at `ξ` is realized by a
  smaller connected boundaried piece of G"* -- i.e. a support `S` of G with
  `CompressibleSupport G S` -- which is what `K .uncompressible` refutes.  The
  paper supplies it only "when this quotient is realized by a smaller connected
  representative" (`def:typeA-trace-basin` (b), tex 10773-10775);
  `lem:typeA-exits-discharged` (tex 11690-11694) says a compression occurring
  "only at the trace-basin response level" is "not an admissible route-8
  residual" and derives no contradiction.  No fact on G's ledger at `[348]`
  (`[339]` unified deficit, the selection fact, `K .replacementExclusion`,
  `K .uncompressible`, the Type B sublinear ledger) produces such a
  representative from the quotient at `ξ`.
- **Why the missing fact is substantive at G.**  At every entry of G's unified
  collection with `α(ξ) ≤ 1`, forgetting the trace incidence *is* a nontrivial
  target-complete response quotient of G's basin
  (`route8Entry_smallCoreQuotient`, applied at G's entries in
  `route8EntryFacts`); so the claim contains "every unified entry of G has
  `α(ξ) ≥ 2`", which the paper obtains (`lem:typeA-unified-carriers`) only
  through this same claim.
- **Neither side derivable from G's ledger at `[348]`.**  The decision
  `route8QuotientDichotomy` reads `[339]` and asks (b) at G's own entries
  (`route8UnifiedEntries` over P₀'s remainder).  No ledger fact at that node
  asserts a response quotient at any of G's basins, and none bounds `α` at
  G's entries (that bound is derived downstream, at the census, *from* the
  quotient-free arm); the only closure the ledger offers against (b) is
  `K .uncompressible`, which needs the missing representative above.
- **Lean.**  `route8QuotientDichotomy` stays (it reads `[339]`); its no arm
  `K .route8QuotientResidual` is closed by `closeIncompatible` against
  `K .selection` (`instIncompatibleRoute8QuotientResidualSelection`,
  `Strategy/SpineRows/Route8QuotientDichotomy.lean`; uncompressibility is
  derived from the selection fact through `replacementExclusion_of_selection`).
  `[348]` is no longer an outcome of Part IX: `SelectedRouteEightBoundary` has
  two disjuncts (Type B sublinear residual, `[186]` joint balance).  The
  `.route8QuotientResidual` disjunct of `OtherReturnedOutcome`
  (`Assembly/Final.lean`, part of the protected six-outcome result) is now never
  produced; it was left in place because that type is not to be edited here.
- **The TA vacuity claim is withdrawn.**  The TA entry stated that
  `Route8.TraceBasin.exists_traceResponseQuotient_of_selected`
  (`Graph/TraceIncidenceQuotient.lean`) makes `¬ Route8Entry` hold whenever
  `load ≠ receiver`.  That file was imported by no module and does not compile
  against the live `TraceResponseQuotient` (whose third clause is the
  all-realizations clause since `21dd850`); the scratch check succeeded only
  because Lean loaded a stale `TraceIncidenceQuotient.olean` of 2026-09-04,
  whose proof had been checked against the pre-`21dd850` clause
  (`TargetComplete` of `retainedReading retained` against `retainedReading` of
  the full family, which erasing the trace incidence satisfies trivially).
  The file is deleted.  At G the route-8 entry is `Route8Entry` at G's pinned
  objects (`X₀`/`P₀`, the receiver and load of G's census, the basin
  `select?` of G); of its clauses, trace-completeness holds by selection,
  (c) is refuted from G's `K .replacementExclusion` and selection
  (`not_traceDelocalization`), (d) from G's no-handoff filter, (b) at the
  unified entries by `[347]`/`[348]` above, and (a) is the exit-(4) witness
  that G's own decisions ask ([101], [181]); none of G's ledger facts decides
  (a) at G's entries, so neither `Route8Entry` nor its negation follows from
  them.  The erased-trace-incidence quotient is target-complete at G's basin
  only if every realization, including states differing on `T_u` off the
  retained supports, answers G's declared target algebra alike in every
  context; nothing on G's ledger states that.
- **Realization class restated.**  `QuotientRealization`
  (`Graph/Route8Residual.lean`) is now the paper's: a boundaried state in the
  basin's boundary-degree fibre "whose image under the quotient map is the
  given quotient", i.e. which carries every retained entry exactly as
  `\rho_u(B_u)` does (a label-fixing placement, injective on each retained
  declared support and preserving and reflecting its incidences).  The earlier
  class (label-fixing surjective images of the basin piece) read the sentence
  in the opposite direction.  Nontriviality is the paper's too: a forgotten
  coordinate whose declared support meets `B_u - ∂B_u` or contains an edge of
  `B_u` (the earlier third clause asked both endpoints off `∂B_u`).

## User-approved repairs

### [153]/[175] (F4) registry: the heavy handoff centres (user-approved, 2026-09-26)

- **Paper.** (F4) (`def:cold-corridor-first-failure`, tex 7234): "the corridor
  first enters a declared Type B handoff envelope or the route-8 response
  support already recorded in the branch state".  Its uses read "enters" at a
  heavy vertex: `lem:cold-germ-extraction` (tex 7297, proof tex 7326-7329: "If
  a candidate support contains a vertex of degree at least 4, then the
  corresponding corridor first enters the high-degree handoff ledger and was
  already removed"); `lem:absorbed-germ-fan-data` (ii) (tex 7926-7930: the
  corridor enters `z` with `d(z) ≥ 4`, "`z` is a heavy centre", `ε` is
  decorated handoff fan data at `z`; the declared interface of a decorated
  envelope is its centre, `def:decorated-fan-envelope`, `H ⊆ V_{≥4}(G)`,
  `lem:typeA-high-degree-handoff`).  The route-8 response support contributes
  nothing on this branch: `def:surviving-cold-branch` (v) (tex 6982) leaves no
  terminal true route-8 entry.  The whole-support reading of tex 7234 fires
  (F4) at segment 0 on a subcubic support, and the paper neither bounds nor
  excludes those half-edges (entry "full charge of a subcubic cold half-edge"
  above; `Quarantine/PaperRepairs/ColdF4Charge.lean`).
- **Lean (live).**
  - `Statements/Spine.lean`, `ColdDeclaredHandoffSupport data G support :=
    ∃ centre, support = {centre} ∧ δ < d_G(centre)` -- G's heavy handoff
    centres.
  - Library (`Graph/ColdGermFamily.lean`, namespace `ColdCorridor.Corridor`):
    `head_mem_prefixSupport_iff`, `head_right_mem_intervalSupport`,
    `head_terminal_mem_prefixSupport_statesRead`, `RegistryHigh`,
    `handoff_before_germ_not_subcubic` (a first entry into a heavy registry
    that precedes a germ segment covered by the trace prefix puts a vertex of
    degree `> δ` in that prefix).
  - Contracts at G (`Contracts/Spine/ColdSubcubicCharge.lean`):
    `coldDeclaredHandoffSupport_registryHigh`, `coldGermAt_exists_head_mem`,
    `coldHandoffOccurrence_not_subcubic` (at the retained classification of
    `K .coldFailureRouting`), and the proof of
    `coldSubcubicFirstFailureGerm` (statement unchanged), which was the
    `PAPER-ERROR [153] tex:7920` sorry.
  - `Contracts/Spine/ColdHandoff.lean`: `coldHandoffOccurrence_not_candidate`,
    `coldF4_card_le_corridorLoss`: on the node-`[153]` witness of
    `K .coldGermCandidates`, `#{ε : first failure (F4)} ≤ #{ε eligible : ε ∉
    candidates} ≤ corridorLoss ≤ (δ+1)·B_cold·σ(G)` -- the (F4) half-edges are
    inside the existing first-high loss, with no new term and no `o(n)`.
- **Why this is the paper's reading.** Every consumer of (F4) in the paper
  (tex 7326-7329, 7926-7930) uses exactly "the corridor reaches a vertex of
  degree ≥ 4"; with this registry the paper's charge argument goes through as
  written.
