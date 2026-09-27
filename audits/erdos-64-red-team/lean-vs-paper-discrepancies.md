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

## [11], [12]: restored at the entry, at G's own boundaried pieces

*Family F5 (Spine / Cold / NearCubic), final pass (group SD).*

- **Lean.** `K .degreeProfileFibres` (idx 2300) and
  `K .targetCompleteContextUniversality` (idx 2301) are published in
  `selectedEntryPrefix` between `[10]` and `[13]`
  (`degreeProfileFibresRow`, `targetCompleteContextUniversalityRow`, which
  reads `[11]`).  Both are stated about every admissible rank quotient of the
  declared coordinates of a region of G (`Graph.CurvatureQuotient`) and the
  `∂Z`-boundaried realizations of its support `Z ⊆ G`; `[12]` also states the
  "consequently" clause at G's own outside context `G − X`.  Branch D's `[37]`
  closes against `[12]` (see Paper errors, "[11], [12], [36]/[37]").
- The former keys 322/323 (deleted by F5 at 4e1a360) were plain projections of
  `Response.TargetComplete` over arbitrary pieces; they are not restored.

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

## [24]: the high-entropy clause is not published

*Family F5; recorded in the final pass (group SD).*

- **Paper.** `[24]` "bounded cold-mass return from [153]: `θ ≤ θ_win + o(1)`;
  high entropy: `θ ≤ 0.01198542083…`".
- **Lean.** `K .densityCap` publishes only the window-only cap
  `2·rate·scales·ν ≤ (scales+1)(δn+T) + slack·rate·scales·T`
  (`θ ≤ θ_win + o(1)`).  The high-entropy sharpening is `def:Theta`'s, which the
  `[53]` test now carries at `K > 0`; no consumer reads a sharpened `[24]`.

## [36]–[46]: Branch D closures and scope

*Family F5; final pass (group SD).*

- `[39]` and `[42]` close against node `[13]` `K .replacementExclusion`
  (`lem:replacement`), not by re-deriving it from `K .selection`: the strictly
  smaller proper representative of `def:proper-quotient-representative` has the
  one-way profile inclusion (a), which is `lem:replacement`'s hypothesis (i);
  tex 9226 cites `cor:uncompressible`, which is `lem:replacement` for proper
  supports.
- `[40]`/`[41]`: the diagram says `Z ⊋ C`; the Lean's `[40]` records
  `Z ⊄ C` (and `C ⊊ C ∪ Z`), and `[41]` classifies the certificate's own support
  `Z`, as `lem:full-rank`'s proof does (tex 9380-9395, `Z` the minimal
  certificate support).
- `[45]` is pinned: the whole-graph support, the rank reduction on `𝒲₂(R₀)` and
  the closed representative are all of the one certificate `branchCertificate?`.
- `[19]` is pinned at node `[31]`'s surviving family `𝓘₀ =
  canonicalSurvivingFamily?` (`test ∉ 𝓘₀`, determiners `⊆ 𝓘₀`); the decision
  reads `[31]`.

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

## [53]: the entropy-cap test sits on the high-entropy arm (`K > 0`, paper-exact test)

*Family F5 (Spine / Cold / NearCubic); `K = 0` removed in the final pass (group SD).*

- **Paper.** Diagram Part IV (tex:878-894) draws `[50]` yes → `[51]` → `[52]`
  → `[54]` unconditionally, and `[53]` "remaining non-obstruction budget
  `< K|R|`?" on `[50]`'s *no* arm.  The text says the opposite:
  `prop:entropy-high-theta` (tex:9919) is stated "in the high-entropy branch of
  `prop:two-budget`", and the budget accounting of `eq:entropy-cap`
  (tex:9870-9901) uses the remainder's `(|R|/10)·log₂ n` bits, which only the
  high arm supplies.
- **Lean.** `entropyCapDichotomy` decides, on the high arm after `[52]`, and
  reading its predecessors `[48]` (`K .forcedCurvatureCost`) and `[52]`
  (`K .entropyPackageDemand`), the paper's test at `P₀`:
  `K .entropyCapActive` = `skeletonBudget < jointPackageDemand ·
  2^{forcedObstructionBits}` against its exact complement `K .entropyCapBound`,
  where `forcedObstructionBits` is `K|R| − o(|R|)` in the exact form node `[48]`
  publishes.  `[54]` (`entropyCapBoundRow.runAndCloseIncompatible`) reads
  `[22]`, `[48]`, `[51]`, `[52]`; on the all-cold arm of `[22]` its bound is the
  `PAPER-ERROR [54] tex:9921` hook (see Paper errors).
- **Difference.** Only the position on the high arm (diagram vs text).

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
- **[55] is a merge node.** `K .largeBudgetResidual` is the disjunction of the
  `[53]`-no fact and the low-entropy fact (each producer fills one disjunct).
  The paper's content of `[55]` ("`θ ≤ θ_win + o(1)`") is carried by the arm's
  density input above, not by `[55]`; every `[56]` row reads `[55]` as its
  predecessor (manifest `Requires`, `inputs.get`) but derives the cap from the
  density input.

## [57] and [173]: the exact collision test replaces the asymptotic cap

*Family F5 (Spine / Cold / NearCubic).*

- **Paper.** Diagram Part V (tex:915-940): `[56]` → `[57]` "large-budget net
  cap" → `[173]` "exact collision test holds?".  `lem:exact-collision-test`
  (tex:7883) decides `[56]`'s collision exactly on the object;
  `rem:no-sufficient-order` removes the order condition at `[57]`.
- **Lean.** `exactCollisionDichotomy` reads its predecessor `[56]`
  (`K .netDeficiencyCap`) and decides `K .netChargeCap` (the exact
  `N₀(R₀) < 0` at the fixed maximum packing `P₀`) against
  `K .exactCollisionFails`;
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
  ports together with `TriangularPortsRoute`
  (`D_B ≥ ((s+1)k − (s(δ+2) − 1))/s`, the paper's `(5k−19)/4` at `δ = 3`,
  `s = 4`). Contract `Contracts.TypeB.heavyCentreRoutedAlternative`. The
  degree-four arm keeps the compatible-pair and fan-closed routing of
  `cor:degree-four-local-activation`. Paper-exact; no deviation remains.
- **Final pass (TB).** The routing statements no longer quantify over
  arbitrary load profiles or write numerals: they are at the registered
  discharge profile `typeBDischargeProfile data` (`α = 1/s`, `s =
  data.dischargeScale`), the normal form is at `data.threshold`, the heavy
  guard is `δ + 1 < d_G(h)`, and the contracts read `δ = 3`, `s = 4` from
  `K .cubicBaseline`.  `lem:triangular-cross-shoulder` states its high
  shoulder as `δ < d_G(s)`.

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
  edge goes [74] → [76] → [77]; [74] is not a diamond.  The fan-mass arms go
  [75] → [76] and [84] → [85].
- **Previous Lean.** `typeBExclusionDichotomy` split on the sign of the
  remaining core charge and closed the nonnegative arm inline
  (`NearCubicCertificate`), an arm that was uninhabitable.  Later, the fan-mass
  arms went straight from [75]/[84] to route 8, and a content-free mass key
  (`typeBExclusionResidualMass`, idx 188) followed [76].
- **Lean now.** [74] `typeBExcludedRow` (`prop:typeB-bridge-reduction`: a B2
  ledger with nonnegative remaining core gives `N₀(X) ≥ 0`), then [76]/[85]
  `K .typeBExclusionResidual`, then route 8 [77].  [76]/[85] is one statement
  (`TypeBExclusionResidualStatement`) reached from all three arms: if B2 holds
  at the support, a negative canonical core keeps a negative post-ledger core
  on its canonical B2 ledger (its deficit is carried only through route 8);
  if B2 fails or a centre is a fan-certificate residual centre, every assigned
  centre is charged to its surplus (`def:typeB-residual-mass`), whose total is
  the sublinear bridge mass of `prop:typeB-bridge-sublinear`.  Producers:
  `typeBExclusionResidualRow` (reads `K .typeBDisjointLedger`,
  `K .typeBExcluded`), `typeBCertificateMassExclusionRow` (reads
  `K .fanCertificateResidualMass`, [75]/[84] → [76]/[85]) and
  `typeBObstructionMassExclusionRow` (reads `K .typeBOverlapObstructionMass`).
  Key 188 is deleted.  This is the paper's topology.
- **G-repair.** All keys are about the one canonical B2 ledger
  `canonicalTypeBDisjointChoice data G Y_X H_X` of the Type B support.

## [65]--[85]: the Type B support is the one support fixed by the entry

*Family F2 (Type B), G-repair and final pass.*

- **Paper** (tex 961, `def:typeB-assigned-ledger` tex 12909). Node [65]
  receives one assigned support `X = (Y_X, H_X)`, and every node
  [67]--[85] speaks about that `X`.
- **Lean now** (`Statements/TypeBLanes.lean`). Each entry form is a lane
  pinned to a canonical object of G: ordinary `(X₀, H(X₀))`
  (`canonicalTypeBOrdinarySupport`, on `K .netChargeCap` and `σ(X₀) > 0`),
  decorated `(X₀, {z})` (`canonicalTypeBDecoratedSupport` with its canonical
  envelope, on `K .netChargeCap` and `σ(X₀) = 0`), absorbed
  (`canonicalTypeBAbsorbedSupport`, on `K .exactCollisionFails` with the [175]
  fan data), and the [144] same-token handoff at `canonicalSameTokenSupport`
  (on `K .surplusAbove`; no continuation runs there).
  - The absorbed support is the support of **one** canonical half-edge,
    `canonicalTypeBAbsorbedHalfEdge` (the canonical choice of a selected
    half-edge outside node [153]'s subcubic candidates): its core is that
    half-edge's retained first-failure prefix, i.e. the counted core of the
    [177] envelope, and its centre is the least high vertex of that prefix
    (`AbsorbedHandoffAt`, read at the half-edge itself, so the centre lies in
    the core).  The lane is nonempty exactly on the [175] yes arm: the [177]
    entry reads `K .typeBAbsorbedHalfEdge` ("some selected corridor meets a
    high-degree vertex", decided by `typeBAbsorbedHalfEdgeDichotomy` from
    `K .absorbedGermFanData`).  On its no arm every selected corridor is
    subcubic: the configurations are the genuine (F5) configurations of
    [176], closed by [154]--[157] and [165]--[168] (on the
    `K .coldPositiveGerm` arm these rows have run; on the
    `K .coldNoPositiveGerm` arm the family is empty and [156]--[157] are run
    on it), and the local cold-terminal exclusion `K .coldBranchClosed` is
    returned at [187], as for every other cold configuration
    (`SelectedAbsorbedGermBoundary`).
  - Every Type B key is `TypeBLaneAt P = ∃ Y H, TypeBLaneMember Y H ∧ P Y H`.
    The lanes are mutually exclusive and each has one support
    (`Contracts.TypeB.TypeBLaneMember.unique`, from
    `ordinary_decorated_exclusive` and `netChargeCap_not_exactCollisionFails`),
    so a decision splits `P` / `¬P` at that one support
    (`TypeBLaneAt.split`, `TypeBLaneAt.not_and_not`).  The same-token disjunct
    of [65] is separated from the continuation lanes by the
    `K .surplusAtOrBelow` read of [68]/[70] (`typeBLanes_of_entry`); no lemma
    states that exclusivity.
  - Decisions read their predecessor: [68] `typeBFanEntry` (and
    `surplusAtOrBelow`), [71]/[80] `fanCertificateCap`, the direct-cycle test
    `fanCertificateMarked`, [72] B2 and [81] `typeBDirectCycleFree`,
    `prop:typeB-bridge-sublinear`'s test (`typeBSublinearDichotomy`)
    `typeBBridgeSublinear`.
  - [81] on the degree-four arm is the paper's test (tex 1019): `c ≤ 1` at
    every assigned centre, or `c ≥ 2` with the B2 disjoint choice
    (`K .typeBDegreeFourLedger`), against `c ≥ 2` and B2 fails, with its
    minimal overlap obstruction (`K .typeBDegreeFourOverlap`, [83]);
    `c` is the closed count at the canonical fan envelope.  The heavy arm
    keeps [72]'s B2 test.
  - [82] publishes `lem:typeB-exclusion` Step 1 (`K .typeBDegreeFourClosed`):
    at `c ≤ 1` every assigned centre's marked fan is certificate-closed
    (`s·D_B ≤ 0`), or the support is B2-paid.
  - The fan envelope at a centre `h` of the support `(Y, H)` is the assigned
    envelope `typeBFanEnvelope Y H h = {h} ∪ Y ∪ H`: a fan neighbour is
    cubic-closed exactly when its two non-`h` incidences are assigned to the
    support (`def:marked-typeB-fan`, `E_h` of `def:typeB-residual-mass`).  The
    B1 entry, the degree-four profile, the `[81]` count `c`, the residual mass
    and the assigned profiles of `def:fan-closed-port` and its routings are all
    at that envelope.
  - The global-local reflection, B2(a)--(d) hygiene and the [76] B2-paid
    residual are stated at the lane's own core `Y_X` (a connected support
    inside `R(P₀)`, `TypeBLaneMember.core_subset_remainder`), not only when
    `Y_X` is a canonical piece; the library (`TypeBPostLedgerCore`,
    `TypeBGlobalLocalReflection`, `TypeBMaximalCompletion`) is stated for any
    core inside the remainder.
  - The window union is `W₀ = windowSupport P₀`, and the bridge statements
    are at `P₀` and at G's canonical piece collections.  The presentation
    facts (accepted quadrilateral, dyadic target, fan-cap, deficit and
    bridge-mass slacks) are published once with `K .cubicBaseline`
    (`TypeBPresentationStatement`) and read with `inputs.get`.
- **Triangular keys** (`def:triangular-fan-core`, tex 2378; tex 2413, 2452,
  2489, 2521). They are stated at a *heavy* center (`d_G(h) > δ + 1`,
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

## [130]: now paper-exact, the full blocker set `Blk(π)` over clauses (a)--(f)

*Group SP (Surplus / Pair / [144]).*

- **Paper** (diagram tex 1195 "canonical pair split: blocker-free?";
  `prop:sparse-pair-independence-dichotomy`, tex 4721-4726;
  `def:canonical-blocker-ledger`, tex 2926-2934).  A pair is blocked when
  `Blk(π) ≠ ∅` over all six clause types.
- **Lean.** `pairResponseIndependenceDichotomy` (`Strategy/SurplusRows.lean`)
  splits `Graph.HasSparsePairBlocker activation Π(𝒜₀)`
  (`Graph/SparseEntropySandwich.lean`): some scheduled pair has a nonempty
  `(recordSparsePairDEBlockers activation Π).blockers π`, the same recorded
  activation that [134] (`canonicalPairLedger`) and [136] (`CapacityLedgerSpec`)
  use.  `IndependentPairFamilyStatement` is its literal negation at G's
  canonical activation; the [131] code pair set (`canonicalCodePairSet`), the
  [131] count-fails input (`FreePairCodeUnrealizedStatement`), the [132]
  blocker arm (`CanonicalBlockerRouteStatement`) and the [134] ledger
  (`CanonicalPairLedgerStatement`) all read the same six-clause predicate, and
  the first failed pair set of [178] is `Π ⊆ Π_free`
  (`PairOverlapFirstFailure.pairSet_blockerFree`).
- **Difference.** None.  Earlier the test read clauses (d)/(e) only.

## `def:surplus-blockers` (d), (e): the determination certificate of `r_π`

*Group SP (Surplus / Pair / [144]).*

- **Paper** (tex 2897-2903; `lem:sparse-pair-dependence-exit`, tex 4675-4718).
  (d) is "a boundary-degree-profile coordinate which prevents a quotient or
  replacement from staying in a single fibre"; (e) is "a target-response
  coordinate witnessing a target-defective quotient, target-complete
  compression, or support-dependence event".  In the lemma both arise from an
  inclusion-minimal determination of `r_π` from a subfamily `B`.
- **Lean.** `SparsePairDetermination` is that determination (a functional,
  rank-reducing attempted declared quotient of G's pair-response family at the
  activation, with an inclusion-minimal certificate of `r_π`).
  `SparsePairDEProfileObstructionAt` (d) adds that two of G's own coordinates
  `{r_π} ∪ B`, read on G's piece at their canonical support, lie in different
  boundary-degree fibres.  `SparsePairDEResponseObstructionAt` (e) adds one of
  the three events: `ResidualTargetDefect` among `{r_π} ∪ B`,
  `ReplacementSupport` of the determination support, or a whole-graph support
  with a strictly smaller closed representative.
- **Difference.** Earlier, (d) compared the two demands' declared supports of
  every pair with no attempted identification (true for almost every pair), and
  (e) omitted the support-dependence event.  (e) is empty on the survivor
  branch; see Paper errors.

## [131]: `lem:mixed-sparse-spine-dependence` is the paper's statement, with no consumer

*Group SP (Surplus / Pair / [144]).*

- **Paper** (tex 4872-4887).  If `ℐ_spine ∪ ℛ_{𝒜₀}` is not independently
  target-testable, G has a sparse surplus exit or some pair has a blocker of
  type (d) or (e).
- **Lean.** `MixedSparseSpineDependenceStatement` (key 203) is exactly that at
  G's canonical spine family and canonical activation:
  `¬ (∀ functional admissible quotient, label-injective) →
  DeclaredSparseSurplusExit ∨ HasSparsePairDEBlocker activation Π`.  The
  contract `mixedSparseSpineDependence_of_baseline` proves it through the exit
  disjunct: the quotient is admissible (fibrewise and context-universal), so
  `DeclaredQuotient.localize` gives exit (c) or exit (d).
- **Difference.** The fact is published on [131]'s ledger
  (`mixedSparseSpineDependenceRow`) and no row requires it: the [131] entropy
  count is a registered branch test ("[131] and [137]: the count-fails arm is
  the negation of the count"), so the independence it would justify is not
  consumed.  Earlier the conclusion did not mention the pair and re-chose the
  quotient.

## [132]: the exit arm reads [130] and is closed by the [125] survivor

*Group SP (Surplus / Pair / [144]).*

- **Paper** (diagram tex 1197-1199, 1224; `lem:sparse-pair-dependence-exit`).
  "blocked-pair routing: exit or canonical blocker?"; the exit closes at [133].
- **Lean.** `blockedPairRoutingDichotomy` reads `K .dependentPairFamily` and
  splits `DeclaredSparseSurplusExit` against its negation; the exit arm closes
  at [133] against `K .sparseSurplusSurvivor` (`closeIncompatible`).
- **Difference.** The exit predicate is a property of G's declared family, so
  there is no witness to pin.  On this branch the exit arm is dead because
  [125] already excludes every exit; this is the paper's own [133].

## [179]/[180]: the Type B alternative is the obstruction's own first-separator handoff

*Group SP (Surplus / Pair / [144]).*

- **Paper** (`lem:pair-system-realizability` (iv), tex 5110-5130, proof tex
  5147-5153; `lem:pair-system-increment-arithmetic`, tex 5207-5220).  "The first
  nonserial intersection is a same-token routed bottleneck whose first
  separator is a high-degree vertex: the decorated Type B fan data".
- **Lean.** `PairSystemEarlyOutcome.typeB` and `PairIncrementEarlyOutcome.typeB`
  carry `PairObstructionHandoff returns`
  (`Statements/CanonicalPairHandoff.lean`): the canonical routes inside the
  retained obstruction's overlap support to its two demands `d_p`, `d_q`, their
  canonical first separator, and `envelopeOfFirstSeparator` on the core
  `{d_p, d_q}` at `P₀` under the node-[144] handoff conditions, escaping
  physically.  The Type B entry `TypeBFanEntryStatement`
  (`Statements/TypeBLanes.lean`) has a matching strict-surplus lane at
  `canonicalPairObstructionSupport` of `canonicalPairDemandReturns`
  (`typeBFanEntry_of_pairObstructionHandoff`).
- **Difference.** Earlier the alternative was node [144]'s same-token handoff
  of G, unrelated to the obstruction.

## Presentation identities of the surplus branch on the ledger

*Group SP (Surplus / Pair / [144]).*

- **Lean.** `K .surplusPresentation` (idx 2200,
  `SurplusPresentationStatement`) is published once at the start of [125]'s
  activation (`surplusPresentationRow`); the surplus, pair and [144] rows read
  the deficit safety, join slack, dyadic target, routing-label count and spine
  scale from it, and `3 ≤ δ` / `¬ LengthOK 2` from `K .cubicBaseline`, with
  `inputs.get`.  No surplus/pair/[144] row reads a `Data` field.

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
  `[187]` (`K .coldBranchClosed`), as at `d2ded0e`.  Since 2026-09-27 the
  absorbed branch `[176]` runs the same `[154]` G2 test
  (`coldGermDistinctionDichotomy`) before `[163]`: its G2 arm is the same
  `[187]` cold outcome (`SelectedAbsorbedGermBoundary` gained that disjunct),
  and `[406]` runs only on the silent arm, as in the dense pass.

- **[165]/[166] size split `[244]`/[245]** (`canonicalSwapSizeDichotomy`,
  `coldCanonicalSwapSmaller` / `coldCanonicalSwapSameSize`).  The paper gives it
  no placement: `lem:refined-minimality-swap` (tex 7732-7757) splits only
  `E ≠ Q` against `E = Q`, and `E` has `|E| = |Q|` by
  `def:neutral-equal-length-germ` (the Lean records
  `representative.size = germ.piece.internalVertexCount` at `[406]`).  A
  strictly smaller canonical representative is a target-complete compression,
  already excluded by (F3)/G3.  The decision is left unwired (as at d2ded0e);
  it is dead code, reported, not deleted.

- **Deleted non-paper keys (final pass, group SD).** `gadgetClosure` [500],
  `contractionCritical` [439], `remainderRelabelingEntropy` [501] and
  `relabelingDensityCap` [502] had no tex statement and no reader; their keys,
  rows, contracts (`Contracts/Spine/SpineMinimalClosure.lean`,
  `relabelingDensityCap_of_orbitCount`,
  `remainderRelabelingEntropy_of_normalized`) and assembly entries are removed.
- **Presentation laws on the ledger (final pass, group SD).** The HSS closure
  law (`thm:p13free`, at G and G's induced subgraphs), the dyadic target, the
  scale family, the net-cap slack and the barrier label semantics are published
  once at the entry as `K .spinePresentationLaws` (idx 2302); node `[16]` is the
  row `hssTargetCycleRow` (`K .hssTargetCycle`, idx 2303) closed against
  `K .selection`.  `3 ≤ δ` / `δ = 3` are read from `K .cubicBaseline`.

## Paper errors

Each entry is a claim of the paper that is not established, stated faithfully
at its node.  In the live Lean tree it is either a `sorry` tagged
`-- PAPER-ERROR [node] tex:<line>` on the proof of exactly that claim, or,
where the user decided so, a residual carried by the node's open leaf.

### [11], [12], [36]/[37]: definitional lemmas and an empty terminal (tex 6088, 6106, 9220, 9388)

- **Paper claim.** `lem:degree-profile-fibres` and `lem:context-universality`
  are proved by "condition (a)" and "this is precisely the meaning of
  target-completeness".  Case (i) of `lem:curvature-dependence-routing`
  (node `[37]`, "a target-defective quotient") is a terminal of the decision
  `[36]`.
- **Faithful Lean statement.** `[11]`/`[12]` at G's boundaried pieces (see the
  `[11], [12]` entry above).  `[23]` `ContextDefectStatement`: some pair the
  certificate's admissible quotient identifies is separated by an outside
  context.
- **Why it is empty / trivial.** The certificate's quotient is admissible, and
  `def:admissible-rank-quotient` (tex 6026) makes every admissible quotient
  target-complete, so `[11]`/`[12]` hold by the definition and `[23]` never
  holds; `lem:full-rank` (tex 9388) says so itself: "The first is excluded by
  the definition of target-completeness".  Lean evidence:
  `Contracts.Spine.contextDefect_false_of_contextUniversality`
  (`[12]` ⇒ `¬[23]`); the decision `[36]` is therefore trivial on every G.
- **Representation.** No `sorry`.  `[37]` closes by
  `closeIncompatible (K .targetCompleteContextUniversality) (K .contextDefect)`.

### [54] on the all-cold arm of [22], `prop:entropy-high-theta` (tex 9919-9921)

- **Paper claim** (`prop:entropy-high-theta`, proof, tex 9921): "Suppose
  `θ > Θ(n) + o(1)`.  By the definition of `Θ(n)` this is precisely
  inequality (`eq:entropy-cap`), that is, the remaining non-obstruction budget
  is strictly smaller than the forced full-rank obstruction cost of
  `cor:forced-curvature-cost`.  Then the window package of
  `lem:p13-window-package`, the remainder bits, and the forced-obstruction bits
  together strictly exceed the near-cubic skeleton budget.  **These bits form
  one independently target-testable coordinate family**, so the number of
  realized target-complete states would exceed the number of labelled
  skeletons, contradicting `lem:independent-target-entropy`,
  `lem:skeleton-dominates`."
- **The paper's argument on the all-cold arm.** The paper does not split `[54]`
  by the hot/cold ledger of `[22]` (`def:cold-window-ledger`, tex 6937, is about
  windows only).  Its one argument is the displayed chain.  On the arm of `[22]`
  where no window family of `P₀` is retained, the family is the remainder states
  of `R₀` and the forced obstruction bits.  The chain has three steps: (1) the
  bit count exceeds the budget -- this is the active arm of `[53]`; (2) the bits
  form one independently target-testable family arising canonically from the
  labelled class -- the premise of `lem:independent-target-entropy` (tex 6241);
  (3) `lem:independent-target-entropy` + `lem:skeleton-dominates`.  Steps (1)
  and (3) are in the Lean (`K .entropyCapActive`; `K .skeletonDominates` with the
  realization form `WindowFamilyRealized`).
- **Where it fails: step (2) is asserted, never proved.** The remainder states
  are realized alone (`RemainderGlue`, which is how the `K = 0` version closed
  this arm), and the rank coordinates are independently target-testable alone
  (`def:curvature-target-rank`, `rem:rank-coordinate-entropy-interface`).  No
  lemma of the paper shows the *product* family is realized by one labelled
  skeleton class.  It is not a false step as stated for the forced part, but
  on this arm the Lean shows the same assertion is false for the full
  curvature code: `Contracts.Spine.allCold_code_overflow` (live, proved) derives
  from the arm's own fact `¬ WindowFamilyRealized ∅` and `K .skeletonDominates`
  that `skeletonBudget < remainderStates(R₀) · 2^{c_Ω·r_Ω(R₀)}`, i.e. the
  remainder states together with the full curvature code are *not* realized.
  The paper's step (2) for the forced part `K|R| − o(|R|) ≤ c_Ω·r_Ω(R₀)`
  (node `[48]`) therefore rests on a fact the paper never proves, and the arm
  exists exactly when its stronger form fails.
- **Tried in Lean first.** On the retained-hot arm step (2) is the ledger fact
  `WindowFamilyRealized 𝒫_hot`, and `[54]` is proved
  (`entropyCapBound_of_hotColdPartition`: window rate ≤ package bits, forced bits
  ≤ `c_Ω·r_Ω` by `[48]`, retained code ≤ realized ≤ budget).  On the all-cold arm
  no ledger fact there (`[22]`, `[48]`, `[51]`, `[52]`, `K .skeletonDominates`,
  `K .uncompressible`, the cold-corridor keys of the arm) bounds a joint
  realization of remainder states with rank coordinates, so there is nothing to
  derive it from.
- **Negation not derivable.** The ledger constrains the four quantities of the
  claim (`RS` = remainder states, `B` = skeleton budget, `cr = c_Ω·r_Ω(R₀)`,
  `F` = forced bits) only by `RS ≤ B` (glue), `1 ≤ B`, `B < RS·2^{cr}`
  (`allCold_code_overflow`), `F ≤ cr` (`[48]`) and `n^{|R|} ≤ RS^d` (`[51]`/
  `[52]`).  `Quarantine/PaperRepairs/EntropyCapAllCold.lean` checks (`decide`)
  that both `RS·2^F ≤ B` and its negation are consistent with all of them
  (e.g. `RS=2, B=5, cr=3` with `F=1`, resp. `F=3`).  The statement also carries
  the selection hypothesis (a minimal counterexample), so no concrete model of
  the full hypothesis set is available to refute it.
- **Faithful Lean statement.** `Contracts.Spine.entropyCapBound_allCold`: at the
  selected G, on that arm, with `[48]`, `[51]`, `[52]`:
  `remainderStates(R₀) · 2^{K|R|−o(|R|)} ≤ skeletonBudget`.
- **K = 0 at d2ded0e.** The gap is exposed exactly by restoring the paper's
  `K > 0` test.  d2ded0e's `[53]` compared the joint window/remainder package
  with the budget (`K = 0`): a different, stronger premise, so the cases
  `demand ≤ budget < demand·2^{K|R|−o(|R|)}` that the paper closes at `[54]`
  were routed to `[55]` instead.  That was a deviation from the paper's `[53]`
  (registered at the time with `rem:closure-robust` as rationale), and it
  avoided step (2): on the all-cold arm the `K = 0` bound needs only
  `RemainderGlue`.  The faithful `K > 0` version is kept.
- **Tag.** `sorry`, `PAPER-ERROR [54] tex:9921`, in
  `Graph/Contracts/Spine/RemainderEntropy.lean`.

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

### [130]--[134] blocker (e) of `def:surplus-blockers` is empty on the surplus survivor (tex 2900; tex 4686-4718, 4899-4925)

*Group SP (Surplus / Pair / [144]).*

- **Paper claim.** `def:surplus-blockers` (e) is "a target-response coordinate
  witnessing a target-defective quotient, target-complete compression, or
  support-dependence event, in the sense of `lem:context-universality`,
  `cor:uncompressible`, `lem:proper-smearing`,
  `lem:no-silent-global-smearing`".  [130] tests `Blk(π) = ∅` over all six
  clauses, and (e) is one of the ways a pair can be blocked at [130]/[134].
- **Faithful Lean statement.** `Graph.SparsePairDEResponseObstructionAt
  activation Π π` (`Graph/SparseEntropySandwich.lean`): an inclusion-minimal
  determination certificate of `r_π` from its determiners
  (`SparsePairDetermination`, the certificate of
  `lem:sparse-pair-dependence-exit`, tex 4675-4684) together with one of the
  clause's three events: a target-defective identification among G's own
  coordinates `{r_π} ∪ determiners` (`ResidualTargetDefect`), a target-complete
  replacement of the determination support (`ReplacementSupport`, compression
  and proper support dependence), or a whole-graph support with a strictly
  smaller closed representative.  It is read at G's canonical activation at
  every node that uses the blocker set.
- **Why it is empty.** Each of the three events is a named sparse surplus exit
  of G's declared family: exit (b), (c), (d) respectively
  (`declaredSparseSurplusExit_of_responseObstruction`,
  `Statements/SurplusPair.lean`).  The paper says so itself: "This is a sparse
  surplus exit of type (b), and the distinguishing target-response coordinate
  is also a blocker of type (e)" (tex 4690-4691; for (c) tex 4700-4701, and
  in `lem:mixed-sparse-spine-dependence` tex 4906-4914).  Every node that reads the blocker set ([130]--[136], [144]) runs
  on the survivor `K .sparseSurplusSurvivor` of [125], which is the negation of
  every such exit.  So on this branch no pair has a blocker of type (e); [130]'s
  blocked arm is driven by clauses (a)--(d) and (f).
- **Evidence.** `declaredSparseSurplusExit_of_responseObstruction` (kernel-
  checked, no `sorry`); with the survivor fact it refutes every (e)
  obstruction.  The same map is used at [144]
  (`Contracts/SurplusPair/Routing.lean`, `responseObstructionRoutes`).
- **Representation.** No `sorry` (nothing unprovable is claimed).  The clause
  is kept as the paper states it; it is simply never inhabited on the branch.
  No other predicate replaces it.

### [144] the capped arm is unreachable after the audits (tex 1238-1252, 5653-5690, 5805-5812)

*Group SP (Surplus / Pair / [144]).*

- **Paper claim.** The diagram routes [137] `D_all > 0` → [139]/[141] → the
  geometric audits [140]/[142]/[143] "homogeneous matching/star" → [144]
  "same-token bottleneck: Type B handoff or capped route?", whose capped arm
  goes to [138].  `prop:nonnear-cubic-sharp-overload-routing` reads it as "if
  no homogeneous same-token pattern reaches size `L_geom`, the fixed caps hold
  ...; if such a pattern exists, `lem:same-token-bottleneck-routing` gives
  either a sparse surplus exit or decorated Type B handoff data".
- **Faithful Lean statement.** `homogeneousBottleneckDichotomy`
  (`Strategy/HomogeneousBottleneckRows/FibrePressure.lean`) decides the fixed
  caps `HomogeneousCapsHoldAt` at G's canonical certified ledger, after the
  audit, in the paper's order; the capped arm runs `homogeneousCapsCloseRow`
  to [138] (`Assembly/Surplus/Local.lean`, `selectedBottleneckDischarge`).
  d2ded0e has the same order.
- **Why it fails.** The audit's own output, `K .homogeneousBottleneckPattern`,
  is a role-homogeneous same-token pattern of size at least `L_geom` in the
  role fibre of G's overloading token at that same ledger; the caps say no
  token carries one.  So on the paper's own path the caps test has only its
  failing arm (and `D_all > 0` at [137] already forces the audits to find the
  pattern).  The paper's capped route to [138] is the [137] no-arm, not a
  [144] arm.
- **Evidence.** `Contracts.SurplusPair.not_homogeneousCapsHold_of_pattern`
  (`Graph/Contracts/SurplusPair/OverloadClass.lean`, kernel-checked):
  `HomogeneousBottleneckPatternSchema → HomogeneousCapsHoldStatement → False`.
- **Representation.** No `sorry`.  The decision and its capped arm are kept
  exactly as the paper draws them; the arm is dead.  [144a] is unchanged.

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
- **Addendum (2026-09-27): G's cut-state presentation pinned.**
  `ColdCorridorStateStatement` ([30]) now pins the retained presentation and
  index of every eligible `ε` to G's own cut-state presentation of its corridor,
  `coldCutStatePresentation data G corridor` with the identity index (a
  `Sigma` equation in the per-`ε` clause).  That presentation reads, from G, the
  boundary-degree profile (G-degrees of the foot and the prefix head), the two
  boundary stubs, the cold-window offsets at the two window interfaces
  (`coldWindowOffset`, the position on the induced `P₁₃` of `P₀`), and the
  declared coordinates on `T(J) = coldActiveInterface` (the two packed windows
  of the stubs and the foot/head), read as their exact embedded datum
  (`coldDeclaredSupport` / `coldDeclaredValue`).  The hook
  `coldFailureDefect_excluded` keeps its tag and its statement form; it is now
  a claim about G's actual corridor states.
  - Not provable: at a first repeat of G's states, the (F2) clause is the
    Part-0 size separation of `retainedPiece(J_r, J_l)` and `piece(J_r)`, so the
    claim holds for G only if G's states do not repeat before a terminal or
    (F4) event, which nothing on the ledger decides.
  - Not refuted: the Part-2 refutation needs state 0 = state 1.  At the pinned
    presentation `T(J_1) = T(J_0) ∪ {head 1}` with `head 1` outside `T(J_0)`, so
    the retained declared value of the full-support coordinate differs; scratch
    check `coldCutState_zero_ne_one` (group CO, `F3_stateCheck.lean`, standard
    axioms).  No other refutation is known.
  - Node `[422]` (`coldFailureDefectRoute`) is restated at the same retained
    occurrence with the paper's (ii) conclusion: an (F2) first failure of G is
    a named sparse surplus exit of G (`DeclaredSparseSurplusExit`), as at
    d2ded0e.  It is discharged on the survivor through this hook
    (`coldFailureDefectRoutes_of_survivor`), and the routing row `[68]` now reads
    it (`K .coldFailureDefectRoute`) together with `K .sparseSurplusSurvivor`
    to exclude (F2).  The former `[422]` (`defect → ¬ TargetComplete` over
    every corridor and presentation) was true by definition and read by no row.

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

### [162] terminality of the cold return corridors, `lem:dense-cold-pass` (tex 7692-7694)

- **Context: the corridor windows (user ruling 2026-09-27).**
  `def:cold-corridor-first-failure` (tex 7165-7167) deletes only `X_cold`, the
  ambient-cubic cold windows, and takes the components of `G − X_cold`.  Until
  2026-09-27 the Lean (`coldCorridorWindows`, unchanged since d2ded0e) deleted
  the whole packing `⋃P₀`, so every corridor lay in `R = G − ⋃P₀`.  The user
  allowed keeping that only if it is not weaker than the paper.  It is weaker:
  nothing in the paper keeps a corridor out of the hot windows or the
  non-ambient-cubic cold windows (`def:surviving-cold-branch` and the hot/cold
  split, tex ~6960-6990, only bound the non-ambient-cubic ones by `o(n)`).  A
  selected stub whose foot lies in a hot window has a genuine corridor through
  that window in the paper, while the R-version turned it into a two-vertex
  cross-window incidence.  So the R-version dropped paper configurations.
  `coldCorridorWindows` is now `windowsOf (cold.filter AmbientCubicWindow)` =
  `X_cold`.  `[30]` lost its two R-clauses (`componentAt ε ⊆ R`, corridor path
  `⊆ R`), which the paper does not state, and its cross-window clause now lands
  in an ambient-cubic cold window.
- **Paper claim.** "Since the boundaried pieces of `R` are induced-`P₁₃`-free
  and subcubic, they have bounded diameter, so every return corridor is
  terminal in the sense of the (F5) terminal subcase" (tex 7692-7694).
- **Faithful Lean statement.** `Contracts.Spine.denseColdCorridorsTerminal_of_state`
  (conclusion `DenseColdCorridorsTerminalStatement`, unchanged): from the
  retained corridor state `[30]`, `[27]`'s normalization and the hot/cold
  split, every retained corridor of G has `statesRead ≤ Q_cold`.
- **Why it fails.** The diameter bound is about the pieces of `R`.  A corridor
  of `G − X_cold` may run through hot windows (induced `P₁₃`s, not in `R`) and
  non-ambient-cubic cold windows, so neither `R`'s `P₁₃`-freeness nor any other
  ledger fact bounds its length.  Its lex-first path is shortest inside its
  component, but that component contains the windows it crosses.
- **Not refutable.** A counterexample needs an outside component with more
  than `Q_cold = |CutState|` vertices: every corridor of a component with at
  most `Q_cold` vertices is terminal (scratch check
  `terminal_of_small_component`, group CO `F3_terminalCheck.lean`, standard
  axioms).  `Q_cold` is the cardinality of the full cut-state alphabet, so no
  concrete refutation is available, and the hypotheses do not bound `n`.
- **Tag.** `sorry`, `PAPER-ERROR [162] tex:7694`, in
  `Graph/Contracts/Spine/ColdMass.lean`.

### [177] the counted core of the absorbed fan data, `lem:absorbed-germ-fan-data` (ii) (tex 7926-7934)

- **Paper claim.** A selected half-edge whose first-failure support `J`
  contains a vertex `z` of degree `≥ 4` "is therefore decorated handoff fan
  data at `z`" (tex 7932).  A decorated envelope needs a counted core
  `Y ⊆ R` that is `P₁₃`-free (`def:decorated-fan-envelope`, tex 10898-10903),
  and the paper's core is the first-failure support `J`.
- **Faithful Lean statement.**
  `Contracts.Spine.coldAbsorbedPrefix_subset_remainder`: for `ε` outside node
  `[153]`'s candidate set, the prefix of G's retained corridor through its trace
  end lies in `R(P₀)`.  `Contracts.TypeB.absorbedGermDecoratedAssignedSupport`
  reads it.  Before the corridor-windows ruling it followed from `[30]`'s
  R-clause.
- **Why it fails.** With the paper's `X_cold` corridors, `J` may meet a hot or
  non-ambient-cubic cold window before `z`, and the paper never shows `J ⊆ R`.
- **Not refutable.** A refutation needs a concrete object carrying the whole
  routed first-failure classification `[68]`.  None is known.
- **Tag.** `sorry`, `PAPER-ERROR [177] tex:7932`, in
  `Graph/Contracts/Spine/ColdSubcubicCharge.lean`.

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

### [82] `c ≤ 1` without B2: "`N₀(X) ≥ 0`" (tex 1020, `lem:typeB-exclusion` tex 14349, `rem:typeB-status`)

- **Paper claim.** Node [82]: "yes: certificate-closed or B2-paid;
  `N₀(X) ≥ 0` outside route 8", on the [81] yes arm "`c ≤ 1`, or `c ≥ 2` with
  B2".
- **Faithful Lean statement.** `K .typeBDegreeFourClosed`
  (`TypeBDegreeFourClosedStatement`): at `c ≤ 1` every marked fan is
  certificate-closed, so its closed fan neighbourhood has charge `−D_B ≥ 0`
  (`lem:typeB-exclusion` Step 1); otherwise B2 holds.  `N₀(X) ≥ 0` is then
  published on the B2-paid support only (`K .typeBExcluded`, conditional on the
  canonical B2 ledger).
- **Why the paper does not give `N₀(X) ≥ 0` at `c ≤ 1` without B2.**
  `lem:typeB-exclusion` assumes that `X` admits B2; Step 1 is "a local
  calculation at a single fan center.  It does not identify disjoint paying
  ledger items for different centers.  The required disjointness is exactly the
  refined support ledger B2" (tex 14435-14437), and `rem:typeB-status` repeats
  that outside the residuals "the exclusion requires the refined support ledger
  B2".  So on the `c ≤ 1`, B2-fails case the paper states `N₀(X) ≥ 0` at [82]
  with no argument.  On the ordinary and decorated lanes `X₀` is negative
  (`TypeBCanonicalLane`), so the claim cannot be published as a proved fact
  there.  No `sorry` is used: the node's proved content (Step 1 and the B2-paid
  bridge reduction) is on the ledger, and the continuation [85] is the same
  `K .typeBExclusionResidual` fact as on the other arms.

## Paper findings (no sorry)

Each entry is a place where the paper is internally inconsistent or routes a
case differently from its diagram.  The Lean follows the paper's main theorem
and argument path; no `sorry` is involved.

### [348] paper inconsistency: `lem:typeA-unified-carriers` (tex 15362) vs `thm:main` (tex 369-372)

*Fix pass fix2-TR (supersedes the R8 entry "PAPER-ERROR [348] tex:15362").*

- **The two statements.**  `thm:main` (tex 369-372, 388-390), the diagram
  (tex 1215, `[187] OPEN aggregate`), its caption (tex 1255: "`[187]` collects
  ... `route8QuotientResidual` ... and `[187]` does not assert closure of any
  survivor") and the outcome table (tex 1432) list *failure of route-8
  quotient freeness* as a returned outcome of `[187]`.  The proof of
  `lem:typeA-unified-carriers` (tex 15360-15364) instead dismisses alternative
  (b) of `def:typeA-trace-basin` at an entry of `\tilde\Xi` as exit (5), "a
  standing-invariant contradiction (`cor:uncompressible`)".
- **Why they disagree.**  Exit (5) and alternative (b) yield a compression of
  G only "when this quotient is realized by a smaller connected
  representative" (tex 10773-10775, 10824-10826); `lem:typeA-exits-discharged`
  (tex 11690-11694) derives no contradiction from a response-level (b).  The
  step at tex 15362 therefore needs "G's quotient at `ξ` is realized by a
  smaller connected boundaried piece of G", which neither the paper nor G's
  ledger at `[348]` supplies.  `thm:main` does not use that step: it returns
  the outcome instead.
- **Lean (follows `thm:main`).**  `route8QuotientDichotomy` reads `[339]` and
  splits on `Route8QuotientFreeStatement` at G's unified entries (tex
  15360-15364 content only: every entry of `route8UnifiedEntries`, its
  `select?` basin, no `TraceResponseQuotient`).  Its no arm
  `K .route8QuotientResidual` is routed through `SelectedRouteEightBoundary`
  (`Assembly/RouteEight/Boundary.lean`, three disjuncts) to the existing
  `OtherReturnedOutcome.route8QuotientResidual` disjunct of
  `SelectedLedgerBoundaryResult` (`Assembly/Final.lean`, unchanged).  The
  former closure `instIncompatibleRoute8QuotientResidualSelection` and the
  sorry'd `Contracts.RouteEight.route8QuotientFree_of_uncompressible` are
  deleted.  No `sorry`.  The census of `lem:typeA-unified-carriers` still gets
  `α(ξ) ≥ 2` on the free arm (`route8EntryFacts`), from G's own
  quotient-freeness.
- **Scope of `[347]`.**  The former second conjunct of
  `Route8QuotientFreeStatement` (every negative no-handoff core of a deleted
  region, any `σ`, every receiver, `excessBasinReduced` loads) went beyond
  tex 15360-15364 and had no reader; it is removed.  The extracted cores carry
  their own quotient-free clause in `route8ExtractedCores`.
- **Realization class (unchanged from R8).**  `QuotientRealization`
  (`Graph/Route8Residual.lean`) is a boundaried state in the basin's
  boundary-degree fibre "whose image under the quotient map is the given
  quotient"; nontriviality is a forgotten coordinate whose declared support
  meets `B_u - ∂B_u` or contains an edge of `B_u`.

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
