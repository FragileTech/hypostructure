# Lean versus paper: current state

This register describes the Erdős–Gyárfás proof as it stands: the residual
families returned by the Lean root, the open proposition of each, and the places
where the Lean differs from the manuscript `to_formalize/erdos_64_proof.tex`.
Paper references are by label.  Lean paths are relative to
`hypostructure/Hypostructure/Graph/` (library, statements, contracts, rows) or
`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/` (assembly).

## Scope of this register

The manuscript is the authority for the proof strategy.  The Lean departs from
it only when the Lean argument is kernel-checked, weakens no fact the paper
states, closes the node the paper closes, and is simpler, needs fewer
hypotheses, or does not need a link the paper leaves implicit.  Each such
departure is recorded below with the node, the paper's argument, the Lean
argument and its declarations.  A step that closes a branch the paper keeps
open, from facts of G alone, is tagged **Lean improvement**.

## Root residual list

`SelectedLedgerBoundaryResult` (`Assembly/Final.lean`) is the result type of
`officialCounterexample_reaches_selectedLedgerBoundary`: a disjunction of six
groups, 43 top-level subtypes.  Each generic residual is an abbrev in
`Assembly/Residuals.lean` (the explicit conjunction of the facts common to its
paths); each subtype in `Assembly/Residuals/<name>.lean` adds the facts of its
own path.  Fact counts are the numbers of `Holds … spineData .<key>` conjuncts in
the abbrev bodies; "+k" is a subtype's extra conjuncts.

| Group | Generic facts | Subtypes (extra facts) | Carries `n < N₀` |
|---|---:|---|---|
| `[144a]` `Node144aOutcome` | 136 | `windowHandoff` (+3), `windowFails` (+18), `remainderHandoff` (+4), `remainderFails` (+19), `primitiveHandoff` (+5), `primitiveFails` (+20) | none |
| `[172a]` `BlockedBarrierOverlapOutcome` | 125 | `DeficiencyAtOrAbove` (+1), `DeficiencyBelowRateFails` (+2) | none |
| `[182]` `PairConditionalFactorizationOutcome` | 120 | `freeFactorizationFails` (+3), `freeRealizabilityFails` (+8), `freeIncrementFails` (+12), `blockedFactorizationFails` (+12), `blockedRealizabilityFails` (+17), `blockedIncrementFails` (+21) | none |
| `[186]` `Route8JointBalanceOutcome_product` | 155 | one product: generic ∧ `Route8LaneEntry` ∧ `NetChargeContinuation` | 400 of its 750 paths (below); every path carries `¬ SufficientlyLargeForNetCap` (9706) |
| `[187]` `OtherReturnedOutcome` | see below | 23 subtypes | 13 subtypes and 400 of 750 paths of each product |
| `[54]` `Node54ResidualOutcome` | 92 | `realizedColdBelow` (+3), `realizedBounded` (+6), `unrealizedTauHighBounded` (+7), `unrealizedRateFailsBounded` (+8), `unrealizedBothRates` (+3) | `realizedBounded`, `unrealizedTauHighBounded`, `unrealizedRateFailsBounded` |

`[187]` (`OtherReturnedOutcome`, `Assembly/Final.lean`):

| Part | Generic facts | Subtypes (extra facts) | Carries `n < N₀` |
|---|---:|---|---|
| Pair Type B (`[179]`/`[180]` entry) `PairTypeBOutcome` | 133 | `independentSystem` (+2), `dependentSystem` (+11) | none |
| Type B sublinear failure `TypeBSublinearOutcome_product` | 128 | generic ∧ `Route8LaneEntry` ∧ `NetChargeContinuation` | 400 of 750 paths |
| Route-8 quotient failure `[348]` `Route8QuotientOutcome_product` | 142 | generic ∧ `Route8LaneEntry` ∧ `NetChargeContinuation` | 400 of 750 paths; every path carries `¬ SufficientlyLargeForNetCap` (9706) |
| Private-carrier rate failure `Route8RateFailsOutcome` | 113 | 11: `realized_{highEntropy, lowNonrepetitive, lowWedgeFree, lowWedge}` (+6, +5, +7, +8), `denseAtOrAbove_{highEntropy, lowNonrepetitive, lowWedgeFree, lowWedge}` (+7, +6, +8, +9), `denseBelow_{lowNonrepetitive, lowWedgeFree, lowWedge}` (+6, +8, +9) | all 11 |
| Local cold-terminal exclusion `ColdBranchClosedOutcome` | 105 | 8: `linearRealizedSilent` (+18), `linearDenseAtOrAbove_repeated` (+8), `linearDenseRateFailed_repeated` (+9), `linearDenseAtOrAbove` (+10), `linearDenseRateFailed` (+11), `linearRealizedDistinguished` (+8), `linearDenseAtOrAbove_repeatedDistinguished` (+8), `linearDenseRateFailed_repeatedDistinguished` (+9) | `linearRealizedSilent`, `linearRealizedDistinguished` |

The three products have `15 × 50 = 750` paths: `Route8LaneEntry` has 15 arms
(three prefix blocks × four entropy arms, and `Route8LanePrefixBlock_unrealizedDenseBelow`
× three low-entropy arms), `NetChargeContinuation` has 50
(`Assembly/Residuals/Route8Blocks.lean`).

Nodes that return no residual:
- `[153]`: its equal-state pair is the repeat subcase of (F5) of
  `lem:cold-corridor-first-failure` and continues into the germ routing
  `[154]`--`[157]`; it reaches `[187]` as the `_repeated` cold-terminal subtypes.
- `[162]`: the dense cold pass runs without a terminality condition on a
  heavy-entry corridor; its arms continue to `[187]` and `[54]`.

## Bounded-size residuals

On `[146]` no, the density order is decided exactly on G's order
(`realizedOrderDichotomy`, `boundedOrderDichotomy`,
`Strategy/SpineRows/DensityOrder.lean`; keys 6600-6605).  The arm `N₀ ≤ n` is
closed (see "Closed from G's facts", density order); every residual on the other
arm carries the combined bound and `K .realizedOrderSmall` or
`K .boundedOrderSmall`, i.e. `n < N₀`:

- realized arm (`[158]` yes, `[146]` no): the four `Route8RateFailsOutcome_realized_*`,
  `Node54ResidualOutcome_realizedBounded`, `ColdBranchClosedOutcome_linearRealizedSilent`,
  `ColdBranchClosedOutcome_linearRealizedDistinguished`, and the 200 product paths
  through `Route8LanePrefixBlock_realizedColdAtOrAbove`;
- `[24]` arm (`[158]` no, `[146]` no, bounded arm of `[153]`): the seven
  `Route8RateFailsOutcome_dense*`, `Node54ResidualOutcome_unrealizedTauHighBounded`,
  `_unrealizedRateFailsBounded`, and the 200 product paths through
  `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`.

`N₀ = densityOrderCutoff A D r S C_sp δ` (`Graph/DensityOrder.lean`) with
`A = 234`, `D = 109`, `r = 118`, `δ = 3`:
`N₀ = max(2^(⌊3A/(2(2r−A))⌋+1), (⌊3·(2A + A·S + 2rD)·C_sp/((2r−A)·δ)⌋ + 2)²)`.
Realized arm (`S = 0`): `N₀ = max(2^176, (13096·C_sp + 2)²) ≈ 7.8·10⁵⁵`
(`C_sp = spineScale ≈ 6.7·10²³`).  `[24]` arm: `S = boundedDensityOrderSlack`.
`Assembly/Residuals/Node54Order.lean` reads the two keys as `n < N₀` at
`spineData` (`realizedOrderSmall_lt_cutoff`, `boundedOrderSmall_lt_cutoff`) and
gives the lower end `13 ≤ n` (`windowOrder_le_vertexCount`); nothing else on
these ledgers bounds `n` from below.

The net-deficiency cap `SufficientlyLargeForNetCap` (key 222) is split on only on
the route-8 residuals `[186]` and `[348]` (9705/9706, `route8NetCapDichotomy`,
`Assembly/RouteEight/Local.lean`), where its large arm is closed by the density
theorem (see "Density theorem").  Elsewhere the paper imposes no order condition at
`[57]` and `[113]` (`rem:no-sufficient-order`, `lem:exact-collision-test`), and on
the producers of `K .netDeficiencyCap` outside the `[24]` arm the absorbed arm of
`[173]` is contradicted exactly.

<a id="open-constructions"></a>

## Open propositions

Each residual carries its whole ledger.  Below is the defining failure and the
part of it no fact of the ledger decides.

<a id="residual-144a"></a>

### `[144a]` (`Node144aOutcome`)

- **Defining failure.**  `[144]`'s same-token bottleneck (`lem:same-token-bottleneck-routing`):
  the Type B handoff `K .typeBHandoff` (three handoff subtypes) or its failure
  `K .typeBHandoffFails` with the unresolved same-label pattern pair
  (three `*Fails` subtypes).  At G the unresolved statement is "`r_p ≠ r_q` and
  `Z = select?(X_p ∪ X_q)` exists" (`K .sameTokenUnresolvedDecided`, 8100).
- **Facts on the fails subtypes.**  The partition 6806, transplants 8000/8001,
  readings 8101, rerouted swap 8102/8103, whole-graph configuration 8104, port-path
  cover 8105, path interactions 8106, ladder count 8107, walk attachment 9990,
  separator exclusion 9991, and 9855: the sub-arm
  W ∧ Tri(1) ∧ Tri(2) ∧ EndEdgesFree is empty at G (`lem:144a-tri-arm-empty`).
  The generic residual carries 9850-9854 (walk windows, exchange, W0 escape,
  crossing count, hub count).
- **Open.**  On the three `*Fails` subtypes: at every walk witness of each pair
  seed, ¬(W ∧ Tri(1) ∧ Tri(2) ∧ EndEdgesFree), i.e. an open (non-triangular)
  port, a walk using the other pair's end edge, or the boundary-free/transplant
  antecedent W failing (then the U1/U2 boundary configurations of 8100-8103).
  On the three handoff subtypes: G's same-token Type B handoff data; no fact of
  the ledger contradicts it.

<a id="residual-172a"></a>

### `[172a]` (`BlockedBarrierOverlapOutcome`)

- **Defining failure.**  `BlockedBarrierFailureStatement`: a first coordinate `c`
  of rank `k` with all earlier aggregate tests holding and
  `F_c·A_k < W_c·A_{k+1}` (`A_k = blockedReachedCount k`, numbers of G's class;
  `BlockedAggregateBoundAt`, `Statements/Spine.lean`).
- **Facts.**  8600 `blockedOwnRecord`, 8601 `blockedFailureSlack`
  (`A_{k+1} ≤ A_k`, `1 ≤ |𝓑| ≤ A_{k+1}`, `F_c < W_c`), 8602
  `blockedPrefixCompression`, 8603 `blockedFailingSetCarries`
  (`|𝓑|·2^{bits·p}·∏_Φ F ≤ |𝒢|·∏_Φ W` for the set `Φ` of failing coordinates), 8604
  `blockedOverlapSupport` (G's completion supports are connected non-cycle closed
  walks of length `2^j`).  Library: `Graph/LayeredFactorization.lean`
  (`aggregate_of_local_share`, `local_share_not_forced`,
  `repetition_of_failed_share`).
- **Open.**  An upper bound on `∏_Φ W/F` (or `Φ = ∅`), or a derivation of an
  overlap-component obstruction from a failed aggregate: this is
  `lem:barrier-failure-overlap`.  Not built: a canonical completion support with
  a locality theorem, and the compression of `Reg(c)` by a configuration swap.

<a id="residual-182"></a>

### `[182]` (`PairConditionalFactorizationOutcome`)

- **Facts.**  8200 `pairCorrelation` (signature counts `P_k` along the failed
  order, first non-branching index `k*`, weighted deficiency bounds, a forbidden
  extension at `k*`), 8201 `pairCoverage`, 8202 `pairFullModulus`, 8203
  `pairUncrossing` (`Graph/PairCorrelation.lean`, `Graph/SerialFrobenius.lean`,
  `Graph/PathUncrossing.lean`).
- **Open.**  One of: (`[178]`) G's canonical minimal obstruction `F₀`
  (least cardinality, colex-least, inside the failed prefix) is pairwise
  separated or splits into two non-overlapping realized blocks, with
  `P_{k+1} < 2P_k` at some `k` in every order; (`[179]`)
  `¬ PairObstructionHandoff returns` and no serial demand system on G's canonical
  `returns`; (`[180]`) `¬ PairObstructionHandoff serial.returns` at G's
  canonical serial system.  Not built: the serial system from the uncrossed pair
  (ordered cells with disjoint interiors, and the cell bound `D_sp` from the cold
  cut-state exchange of `[166]`).

<a id="residual-186"></a>

### `[186]` (`Route8JointBalanceOutcome_product`) and `[348]` (`Route8QuotientOutcome_product`)

- **Defining failures.**  `[186]`: `K .route8JointBalance`
  (`3|R| ≤ 13|∂R| + 3h + O`, `O` the open demand units).  `[348]`:
  `¬ Route8QuotientFreeStatement` at G's unified entries, with 8150
  `K .route8QuotientEntriesAtG` (`0 < |Ξ̃|`, `|∂R| < δ|Ξ̃|`, a two-support entry,
  per entry the selected basin, size-preserving representative, folds carrying
  cycles and paths, carriers in `∂R`, no exit-(5) datum).
- **Facts on both.**  8700 `route8FoldPeels` (a fold pair of the selected basin
  makes the load an exit-(4) peel; `thm:typeA-two-carrier-nogo` at G), 9800-9807
  (`lem:r8-packing-exchange` and the arm-closure residual, `lem:r8-arm-closure-residual`),
  9900-9902 (piece-window attachment, piece chain cycles, piecewise rate
  `Σ_X (3|X| − 13E(X)) > 3·slack` with a heavy piece), 9975-9980 (dominance
  irreducibility, `Graph/DominatedReplacement.lean`), 9810-9812 (window exchanges at G:
  legal double landings of X15 on one window, the two-arm trigger on one window, the rung
  bound for an X15 copy with exits on two windows; see "Window exchanges at G").  On
  `[186]` the rate over the
  pieces is pinned: `3h < Σ_X (3|X| − 13E(X)) ≤ 3h + O`, so `O > 0`.
- **Density facts on both.**  9700-9704 (the density theorem at G: hub-free pieces
  have `ex(X) ≤ 0` or are X15 copies; X15 copies have `ν(X) ≥ 2`; Π on thick
  hub-free pieces; `ex(X) ≤ 28σ_X` on hub pieces; the arm closure for large `n`),
  and 9706 `route8NetCapSmall`.
- **Closed arm.**  `F ≤ 14 ∧ SufficientlyLargeForNetCap` (9705) is refuted by 9704
  (`closeIncompatible`, **Lean improvement**; the paper states the density bound as
  `rem:r8-density-conjecture`).
- **Open.**  Both residuals live in the window `¬ (F ≤ 14 ∧
  SufficientlyLargeForNetCap … n)`; at `spineData` (`F = 8`) this is
  `¬ SufficientlyLargeForNetCap 3 4 13 windowRate spineScale densitySlack n`,
  i.e. `n` below `netCapCutoff`.  There 9804 and 9807 are vacuous and the
  residuals are open with the facts above.  `F` enters the split key because no
  ledger fact publishes `F = 8`.

<a id="residual-187-pair-type-b"></a>

### `[187]` pair Type B (`PairTypeBOutcome`)

- **Defining failure.**  Alternative (iv) of `[179]`, `PairObstructionHandoff`
  at G's canonical pair returns: the canonical first separator `h ∈ U` of degree
  `> δ` with two next vertices in `U`, non-absorbing at `P₀`, escaping envelope.
- **Facts.**  8350-8352 (handoff support `({d_p.2, d_q.2}, {h})`, charge,
  net-charge dichotomy: negative charge or `d(h) < 3δ`), 8353-8357 (charge at
  `h`, boundary type of `U`, every member of `𝒰` critical, descent, forces at
  `h`), 8358 demand ends, 8359 hub balance, 8360 `pairHandoffFibreAtG`.
- **Open.**  The handoff with the whole ledger; in particular whether the fibre
  of G's own level signature at `π_h` has one realized extension (a repetition at
  G) or two (8360).  In the negative-charge branch nothing bounds `d(h)`.

<a id="residual-187-type-b-sublinear"></a>

### `[187]` Type B sublinear failure (`TypeBSublinearOutcome_product`)

- **Defining failure.**  `¬ TypeBSublinearHypotheses` (`prop:typeB-bridge-sublinear`)
  in G's canonical form (8300), decomposed exactly by 8302 into arms (A), (B), (C).
  Arm facts 8301, 8303-8305 (empty failure arms at G, **Lean improvement**),
  8306-8316 (cover payment, receiver ports = window stubs, saturated basins,
  flow values, piece sizes, piece mass dichotomy, landing structure).
- **Open.**  (A) a flat vertex of a positive-surplus piece whose canonical trace
  lands on a centre, or a non-centre receiver with `s·q ≤ L`; (B) the same for
  handoff pieces against the absorbed core; (C) an absorbed vertex with a window
  port, at most `2·def⁺(R(P₀))` of them.  The receiver-load bound is
  the Type A unsaturation lemma, which the paper proves only for zero-surplus
  supports.

<a id="residual-187-private-carrier-rate"></a>

### `[187]` private-carrier rate failure (`Route8RateFailsOutcome`)

- **Defining failure.**  `Route8RateFailsStatement`: the manuscript rate
  `(δs+1)|∂R| + δ·F·s·T(n) < δ|R|` (`Route8Census.Rate`, `τ < 3/13`) fails at
  `P₀`; every subtype carries `n < N₀`.
- **Facts.**  8250-8258 (join with cross-window term `X`, pieces, flow,
  carrier injection, exact-slack rate, stub-deficit identity, deficit versus
  stubs, entry lower bound), 8259 `route8CoreEmpty` (every census core is empty
  or its entry is determined), 8260 `route8StrongRate` (the strong rate with
  `[113]` gives a nonempty route-8 collection, or the thin remainder
  `|R| ≤ s|∂R| + F·s·T(n)`), 8261-8263 on the thin remainder (isolation
  `X + T < σ_W + F·T`, window stubs, `n < N₀'`), 8264-8269 (cycles of the
  window-piece graph `B` through the remainder for `s ≤ 2`, cycle rank at least
  `6.5p + (σ_W − X)/2` on the thin arm, achievable lengths).
- **Open.**  The failed rate with these facts: every cycle of `B` of any length
  `2s` must avoid `{2^k}`; the family for `s ≥ 3` is not built, and no fact ties
  the length sets of two pieces or forces a collision.

<a id="residual-187-cold-terminal"></a>

### `[187]` local cold-terminal exclusion (`ColdBranchClosedOutcome`)

- **`linearRealizedSilent`.**  `[154]` silent arm on the realized package:
  G's marked neutral equal-length germ `(Q, E)`, `E = Q`, subcubic, not handed off
  (8400), with the excision facts 8401-8405 (`Graph/SpliceLift.lean`,
  `Graph/DoubleSuppress.lean`, `Graph/SpliceRoute.lean`, `Graph/PairRoute.lean`).
  Open: for every consecutive interior pair of the germ's stretch, a Mersenne
  path around it (`2^k − 1`) or a double cycle of length `2^k + 2`, unless the pair
  lies in a triangle or `C₄`; no two consecutive internally disjoint Mersenne
  paths of equal exponent; every chord of the stretch has non-accepted span `+1`.
  This system is satisfiable for every stretch length; the stretch is bounded
  only by `M_cold`.
- **`linearDenseAtOrAbove`, `linearDenseRateFailed`, `linearRealizedDistinguished`,
  `*_repeatedDistinguished`.**  `[154]`'s G2 yes-arm: some active germ's
  constructed second representative `E` (`GConstructedPiece`,
  `BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`; every fold
  pair of the support distinguishes (`distinguishingAt_fold`), and an excision
  `E` gives a cycle of G of length `L + q` with `L` accepted, `L + q` not
  (`excision_dichotomy`).  Open: no fact excludes such a germ.
- **`*_repeated`.**  G's first repeated cut state on a retained dense corridor
  (`K .coldRepeatedStateResidual`) on the silent arm of `[154]`, which the table
  `[157]` must exclude; the terminality argument of the dense residual
  (bounded diameter of the pieces of `R`) does not reach corridors of `G − X_cold`.

<a id="residual-54"></a>

### `[54]` (`Node54ResidualOutcome`)

- **Defining failure.**  `[53]` active and the joint realization inequality
  `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` fails at `P₀` (`K .entropyCapActive`,
  `K .allColdEntropyResidual`, the latter in aggregate form
  `B < 2^{b_P·p} ∨ B < retainedCode P₀`).  Facts 8550 `stubDeficitIdentity`,
  8551 `remainderCycleSpectrum`.
- **Open.**  The bounded subtypes: the ledger with `13 ≤ n < N₀`.
  `realizedColdBelow` and `unrealizedBothRates`: no size bound; the stub-deficit
  identity and the rate inequalities are jointly consistent in the linear
  relaxation.

## Lean deviations from the paper

### [8]: `NoProperBaseline` also records connectedness

`K .noProperBaseline` is `lem:no-proper-core` ∧ `Connected`
(`connected_of_noProperBaseline`), a proved consequence.

### [13]: `lem:replacement` at G's own context

`ReplacementSupport` (`Graph/InterfaceReplacement.lean`) takes a proper
connected support `Z` of G and an arbitrary `∂Z`-boundaried piece `X'` with
(ii) the profile of `G[Z]`, (iv) the baseline of `G' = glue X' (G − Z)`, (v)
`G'` strictly smaller, and in place of (i) and (iii) their consequence in the
paper's proof, "`G'` has no power-of-two cycle", read in `G − Z`.  The hypothesis
set is weaker than the paper's, so the exclusion `K .replacementExclusion` is
stronger.

### [34]/[47]: exact full rank

`curvatureRankDichotomy`'s no arm `K .curvatureFullRank` publishes
`r_Ω(R) = W₂(R)` at `P₀ = canonicalWindowPacking`; it implies `lem:full-rank`'s
`r_Ω(R) ≥ W₂(R) − o(W₂)`.

### [53]: the entropy-cap test sits on the high-entropy arm

The diagram (Part IV) puts `[53]` on `[50]`'s no arm; `prop:entropy-high-theta`
is stated in the high-entropy branch of `prop:two-budget`, and
`eq:entropy-cap` uses the `(|R|/10)·log₂ n` bits only that arm supplies.  The
Lean follows the text: `entropyCapDichotomy` decides, on the high arm after
`[52]`, `K .entropyCapActive` (`skeletonBudget < jointPackageDemand ·
2^{forcedObstructionBits}`, the demand counting all windows of `P₀`) against
`K .entropyCapBound`; `[54]` is `entropyJointRealizationDichotomy` on the active
arm.

### [55]/[56]: the density input differs by arm

`lem:dense-deficiency-routing` says nodes `[56]`--`[64]` consume only
`def⁺(R) − σ(R) < |R|/4`.  Three `[56]` rows publish `K .netDeficiencyCap` from
the arm's input: `netDeficiencyCapRow` (`[24]`), `denseNetDeficiencyCapRow`
(`[160]`'s `K .denseDeficiencyBelow`), `routeEightNetDeficiencyCapRow`
(`[146]`'s `K .coldRoute8Below`).  `[55]` (`K .largeBudgetResidual`) is a merge
node, the disjunction of the `[53]`-no and low-entropy facts; the paper's content
of `[55]` is carried by the arm's density input.

### [57] and [173]: the exact collision test

`exactCollisionDichotomy` reads `[56]` and decides `K .netChargeCap`
(`N₀(R₀) < 0` at `P₀`) against `K .exactCollisionFails`, as
`lem:exact-collision-test` and `rem:no-sufficient-order` do, with no `n ≥ N₀`
hypothesis; `[57]` has no separate fact.  `bridgelessRow` publishes
`lem:bridgeless` before the decision, since both arms read it.  The no-arm is
closed at the node (see "Closed from G's facts", `[173]`/`[174]`).

### [65]--[85]: the Type B support pinned by the entry

Each Type B entry is a lane pinned to a canonical object of G
(`Statements/TypeBLanes.lean`, `Statements/CanonicalTypeB.lean`), and every node
`[67]`--`[85]` speaks about that one support `X = (Y_X, H_X)`.
- **Triangular keys.**  `def:triangular-fan-core` and its lemmas are stated at a
  heavy centre (`d_G(h) > δ + 1`) and feed `prop:triangular-port-typeB-routing`,
  so they run on the heavy arm `[69]`.  The paper's cross-reference table lists
  them at `[78]`--`[81]`, which contradicts their own statements; the Lean
  follows the statements.
- **[70].**  `TypeBFanCertificateCapStatement` publishes, at every assigned
  centre, clause (i) of `def:typeB-fan-safe` together with the certificate cap, as
  one fact read from the incoming arm (`fanCertificateCapRow` on the heavy arm,
  `degreeFourFanCertificateCapRow` on the degree-four arm).
- **[85] → [77].**  Part VII expands the degree-four no-branch of `[68]`, which in
  Part VI runs `[68] → [70] → … → [76] → [77]`; so `[85]` is `[76]` for that branch
  and its route-8 cores continue at `[77]` (`K .typeBRoute8Entry`).  The degree-four
  support can be negative at G, and the paper's statement "cannot carry linear
  deficit outside route 8" sends the deficit to route 8.

### [102] → [89]: the recompute-`L₄` loop

An append-only ledger cannot commit the same keys twice, so the repeated peels
are the canonical peeling sequence `canonicalPeel` of each receiver, stopped at
its terminal set `P₄(w)`.  After `[102]`, `typeAExitFourRetestDichotomy` asks
`[89]` at the terminal sets; the yes arm asks `[93]` and exits `(1)`--`(3)` again
at `P₄(w)`, the no arm is `[90]` with `L₄` followed by `[91]`.  The no arm's
`[92]` is under "Paper findings".

### [131] and [137]: the count-fails arm, and the free side of [137]

- `freePairEntropyDichotomy` / `blockedPairEntropyDichotomy` decide the count
  itself; the no arms are its literal negation, and the first failed pair
  extension `[178]` reads is derived afterwards
  (`freePairCodeUnrealizedRow`, `blockedPairCodeUnrealizedRow`).
- On the independent branch the free side runs `freePairCoupledExcessDichotomy`
  (`Strategy/HomogeneousBottleneckRows/FibrePressure.lean`) and both arms close by
  `[138]`'s estimate (`freePairSurplusEstimateRow`) against `[19]`: the `[131]`
  count gives `σ(G) ≤ C_sp⌈√n⌉` on the whole count-holds branch.  The paper sends
  `D_all > 0` to `[139]`; its "no blocked pairs, so `D_all = 0`" needs a link
  between the overload ledger and `E_spine` that it does not state.
- `lem:mixed-sparse-spine-dependence` (`MixedSparseSpineDependenceStatement`,
  key 203) is published at G's canonical quotient and activation and has no
  consumer, because the `[131]` count is a branch test.

### [130]: the full blocker set, with exact tests of clauses (d) and (e)

`pairResponseIndependenceDichotomy` splits `Graph.HasSparsePairBlocker` over all
six clauses of `def:surplus-blockers` at G's canonical activation.  On the
blocked arm an exact decision tests clause (d)
(`pairProfileObstructionDichotomy`, keys 2903/2904) and closes its positive arm,
and clause (e) is decided at G: the fact-only row `pairNoResponseObstructionRow`
(reads `K .selection`, `K .dependentPairFamily`) publishes
`K .pairNoResponseObstruction` (2901) (see "Closed from G's facts").  The determination behind (d)/(e) is
`SparsePairDetermination` with the valuation `SparsePairExactValuation`, so its
quotient is target-complete as the paper's determination quotient is.

### [178]--[180] and [182]

- **[178] in aggregate.**  `Graph.SparsePairSkeletonModel.CountRealizing`
  (`Graph/PairCorrelation.lean`): some exposure order doubles the number of
  realized signatures at every step, the count the entropy argument consumes; the
  conditional factorization is asked at G's canonical minimal obstruction
  `F₀` only (`PairOverlapSystem.ConditionalFactorization`), with the exact
  negation `not_conditionalFactorization_iff`.
- **[179].**  The outcome types name only objects of G: `PairSystemEarlyOutcome`
  has the target cycle (i) and the handoff (iv), `PairIncrementEarlyOutcome` the
  handoff.  The paper's (ii) (a target-defective identification of readings in
  `G − Z`) and (iii) (a replacement inside the overlap support) conclude about
  objects built from G and are refuted by `[4]`'s selection
  (`Graph.not_residualTargetDefect_of_avoids`, the replacement exclusion), so
  they are not alternatives.  The target cycle is empty at G, so coverage is
  exactly `PairObstructionHandoff ∨ ∃ serial system on these returns`
  (`pairSystemRealizabilityOutcome_iff`).  The Type B alternative (iv) is the
  obstruction's own first-separator handoff (`PairObstructionHandoff`,
  `Statements/CanonicalPairHandoff.lean`; entry `typeBFanEntry_of_pairObstructionHandoff`).
- **[180].**  The arithmetic arm is empty at G (`not_pairSerialArithmetic_of_avoids`),
  and the periodic alternatives after `[179]`'s no-early arm are empty
  (`not_pairIncrementEarly_of_noEarly`, **Lean improvement**), so the pair Type B
  entry has only the system arm.
- **[182].**  Each test is an exact decision with its own negation key
  (`K .pairFactorizationFails`, `K .pairRealizabilityFails`,
  `K .pairIncrementFails`), pinned to the same canonical object as its test.  The
  paper claims "exactly one" alternative of `[179]` occurs; the Lean does not prove
  exclusivity and follows the paper's precedence ((i)--(iv) before the serial (v)).

### [49]: `RemainderClass`

`Graph.RemainderClass` drops the paper's subcubicity on the boundaried-piece
part, adds `|E| = |E(R)|` (needed by the `RemainderGlue` injection at `[54]`), and
caps `def⁺` at `def⁺(R)` rather than at the branch's net-deficiency cap.

### [163]/[165]/[166]: the refined swap

`lem:refined-minimality-swap` needs the refined order to compare multisets of
canonical decomposition pieces; the Lean's third coordinate
(`canonicalDecompositionCode`) is a well-order on labelled skeletons, for which a
canonical exchange does not provably decrease, so the `[163]` row defines the
representative as canonical only when the swap is refined-smaller.  The size
split `canonicalSwapSizeDichotomy` has no placement in the paper (`E` has
`|E| = |Q|` by `def:neutral-equal-length-germ`) and is not wired.

### [163] at the silent family's (F5) configuration

`lem:neutral-germ-symmetry` assumes the dense residual's terminal (F5)
configuration (`lem:dense-cold-pass`, `def:neutral-equal-length-germ`).  The Lean
runs the symmetry split `absorbedNeutralSymmetryDichotomy` at the silent family's
neutral configuration without terminality (`K .coldAbsorbedNeutralConfiguration`,
`NeutralConfigurationStatement`), which `lem:absorbed-germ-fan-data` (i) asserts;
on the realized silent arm the genuine second-strand arm then closes
(`twoStrandSurvivorRow`, `symmetricPairEndpointExclusionRow`, **Lean improvement**).

### (F4) registry: the heavy handoff centres (user-approved)

`def:cold-corridor-first-failure` (F4) reads "the corridor first enters a
declared Type B handoff envelope or the route-8 response support"; every consumer
(`lem:cold-germ-extraction`, `lem:absorbed-germ-fan-data` (ii)) reads "enters" as
reaching a vertex of degree at least 4.  The whole-support reading fires (F4) at
segment 0 on a subcubic support, which the paper neither bounds nor excludes.  The
Lean registry is G's heavy centres: `ColdDeclaredHandoffSupport data G support :=
∃ centre, support = {centre} ∧ δ < d_G(centre)` (`Statements/Spine.lean`), with
`coldSubcubicFirstFailureGerm` proved (`Contracts/Spine/ColdSubcubicCharge.lean`)
and the exact count `coldF4_card_le_corridorLoss`: the (F4) half-edges lie inside
the first-high loss `≤ (δ+1)·B_cold·σ(G)`.

### [53] active on the dense pass: the exact [54] decision (user-approved)

Part XII routes `[53]` active on the dense pass to `[164]`.  The Lean closes those
arms (`nearCubicLargeBudgetRateFailed`, `nearCubicLargeBudgetColdRate`,
`nearCubicLargeBudgetDensityCap`) with the exact `[54]` decision: its joint arm
closes, its other arm returns `[54]`.  `[164]`'s proof uses the `K = 0`,
hot-only reading, which the exact `[50]`/`[53]` tests do not have.

### Lean-only facts on the entry prefix and the strict arm

Facts of G not stated in the paper are published once and carried by every
residual below them (**Lean improvement**, no decision and no split): switch paths
6800-6806, density order 6600-6605, cycle counting 6900-6907
(`Graph/CycleCounting/*`), local rigidity 7100-7103 (`Graph/LocalRigidity.lean`),
hubs, windows and remainder 7200-7237 (`Graph/JointSystem.lean`,
`Graph/WindowCombination.lean`, `Graph/HubLinkObject.lean`,
`Graph/JointObject.lean` and the statement modules `JointHubs`, `HubLinks`,
`PairArms`).  The one closure they give is the first band at `C_sp` (below).

<a id="paper-errors"></a>

## Paper errors

No claim of the paper is shown false at G.  The places where the paper is
inconsistent or unargued are the "Paper findings" below.

## Paper findings

Places where the paper is internally inconsistent, routes a case differently
from its diagram, or states a step that is empty, trivial or unargued at G
without being false there.  No `sorry` is involved.

### [11], [12], [36]/[37]: definitional lemmas and an empty terminal

`lem:degree-profile-fibres` and `lem:context-universality` hold by the
definition of an admissible (target-complete) quotient, and case (i) of
`lem:curvature-dependence-routing` (`[37]`) never holds; `lem:full-rank` says so
itself.  `[36]` is decided yes by admissibility (`contextUniversal_of_selection`);
`[37]` closes by `closeIncompatible (K .targetCompleteContextUniversality)
(K .contextDefect)` (`Contracts.Spine.contextDefect_false_of_contextUniversality`).

### [82]: `c ≤ 1` without B2

Node `[82]` claims "`N₀(X) ≥ 0` outside route 8" on `c ≤ 1`.  With B2 failing,
this needs Step 2 of `lem:typeB-exclusion` (disjoint paying items for different
centres), which Step 1 does not supply (`rem:typeB-status`).  The Lean treats the
case as a Type B bridge residual charged by `lem:typeB-bridge-deficit-bound`
(`TypeBBridgeDeficitBoundAt`) at `[85]` (`typeBDegreeFourExclusionResidualRow`).

### [92] after peeling

The diagram returns `[102]` to `[89]` and closes the no arm at `[92]`.  After a
peel, `lem:typeA-exit4-peeling-charge` gives only
`|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|` with `Σ_w |P₄(w)| ≥ 1`, which does not
contradict `[86]`.  `rem:typeA-exit4-peeling-use` routes this case to
alternative (iii) of `lem:density-mersenne`; the Lean follows it and enters the
unified target-defect/route-8 ledger of `[123]`
(`selectedTypeAExitFourDischargedRetest`, `Assembly/TypeA/ExitFourDischargedRetest.lean`).

### [113]: tested, not asserted

The diagram draws `[113]` as a box; `rem:why-unified` states that the route-8-only
lower bound does not follow.  `route8LargeBudgetDeficitRow` decides the exact
inequality on `𝒳_A`; the positive arm continues to `[114]`--`[124]` and closes,
the negative arm enters the unified ledger of `thm:large-budget-route8-only`.

### [348]: `lem:typeA-unified-carriers` against `thm:main`

`thm:main`, the diagram and the outcome table return the failure of route-8
quotient freeness from `[187]`; the proof of `lem:typeA-unified-carriers`
dismisses alternative (b) of `def:typeA-trace-basin` at an entry of `Ξ̃` as exit
(5), "a standing-invariant contradiction".  Exit (5) needs the quotient realized
by a smaller connected representative, which the paper does not supply.  The Lean
follows `thm:main`: `route8QuotientDichotomy` returns `Route8QuotientOutcome`.
At G the size-preserving representative of the (b)-quotient class is a valid
replacement of exactly the piece's size, so a smaller one would contradict
minimality (8150).

### [170]/[172a]: the absent-completion failure at the smallest scales

`blockedCoordinate` ranges over `j < separatedScaleCount n = ⌊log₂ n⌋` and every
registered row `(a, b)`, `a + b ≤ 14`.  `lem:p13-window-package` names no minimum
scale, and at a scale `2^j ≤ a + b` no completion support exists, so
`S = A` and the ratio fails whenever `F < W` (every registered row).  The paper
records this at `[172a]` ("the absent-completion state survives and `S = A`").
Restricting to `j ≥ 2` would change `L` (shared with `[158]`/`[159]`/`[171]`) and
leave the failure at `j = 2`; the statements of `[170]`--`[172a]` follow the paper.

## Closed from G's facts

Branches the paper keeps that are refuted at G by facts on G's ledger at the
node, closed there with `closeIncompatible`.

- **The named sparse exits of [125] are empty at G.**  `Graph.SparseSurplusExit`
  has the two conclusions of `def:named-surplus-exits` that are objects of G:
  (a) an accepted cycle of G and (e) a suppression-chord cycle certificate whose
  lifted length is accepted, which expands to an accepted cycle of G.  `[4]`'s
  selection refutes both, so `[125]`'s survivor fact `K .sparseSurplusSurvivor`
  is a theorem about G (`Graph.Contracts.SurplusPair.not_declaredSparseSurplusExit`),
  published by the fact-only row `sparseSurplusSurvivorRow` (reads `K .selection`)
  on the strict arm of `[20]` and on the near-cubic arm before `[21]`; neither arm
  has an exit branch.  Clauses (b)--(d) of the paper's list conclude about
  objects built from G (readings of G's pieces glued into `G − Z`, a replacement
  piece glued in, another finite object); wherever the proof meets one, G's
  selection refutes it: (b) by the avoidance (two readings of G agree in
  `G − Z`, `Graph.not_residualTargetDefect_of_avoids`, `lem:sparse-exit-b-empty`),
  (c) and (d) by the minimality (`not_replacementSupport_of_minimal`).
- **[130] blocker (d).**  The determination quotient is admissible, so it never
  identifies states in different fibres (`not_sparsePairDEProfileObstructionAt`,
  `not_pairProfileObstruction_of_fibres`); closed against
  `K .pairDegreeProfileFibres` (2902).
- **[130]--[134] blocker (e).**  Each event of (e) (a target-defective
  identification, a compression of the determination support, a whole-graph
  closed representative) is refuted by `[4]`'s selection
  (`not_responseObstruction_of_selection`), so clause (e) is empty at G and has
  no branch: `K .pairNoResponseObstruction` is a theorem about G
  (`pairNoResponseObstruction_of_selection`).
- **[131] mixed dependence.**  G's canonical rank-reducing quotient of the mixed
  family does not exist: it would localize to a replacement or a smaller closed
  representative, refuted by `[4]`'s selection
  (`mixedSparseSpineDependence_of_baseline`; `K .mixedSparseSpineDependence`
  states the quotient is `none`).
- **[144] capped arm.**  The audit's pattern `K .homogeneousBottleneckPattern`
  refutes the caps at the same canonical ledger
  (`not_homogeneousCapsHold_of_pattern`, `selectedBottleneckDischarge`,
  `Assembly/Surplus/Local.lean`); the paper's route to `[138]` from this arm is the
  `[137]` no arm.
- **[118]/[124].**  The `[113]`-yes two-support entry is the terminal obstruction
  of `prop:typeA-route8-closure-from-nogo`: `thm:typeA-two-carrier-nogo` gives an
  exit-(4) witness at `ι₂` against (T2) (`route8TrueTwoCarrierEntry_false`,
  `Assembly/RouteEight/Residual.lean`).
- **[173]/[174].**  `K .exactCollisionFails` (`N₀(R₀) ≥ 0`), `K .route8Rate` and
  `[29]`'s `def⁺(R₀) ≤ e(R₀, W)` give `3|R₀| ≤ 12·e < 13·e + 3·slack < 3|R₀|`
  (`Contracts.RouteEight.exactCollisionFails_route8Rate_false`,
  `Assembly/NetCharge/Continuation.lean`).  On the dense double-yes arm this is
  the paper's own dead branch; on the spine and `[147]` arms, **Lean
  improvement** (the paper reads both rates asymptotically).  The absorbed lane
  `[174]`--`[177]` is therefore not a factor of the route-8 products.
- **[146] yes after [160]'s first complement.**  `θ < 1/78` forces `τ(θ) < 1/4`
  (`denseDeficiencyBelow_of_coldRoute8Below`, `nearCubicDensePassAtOrAbove`).
- **[53] bound arm on the [161] dense residual.**  `[52]`, `[159]` and `[160]` give
  `K .entropyCapActive` (`entropyCapActive_of_denseUnrealized`,
  `denseEntropyCapActiveRow`), against `K .entropyCapBound`.
- **Density order, `N₀ ≤ n` (Lean improvement).**  `[146]` no gives
  `δn ≤ A·p₁₃ + D·T(n)`; the realized package or `[24]` gives the window cap; the
  combination is false for `n ≥ N₀` (`Graph.densityOrderBound_false_of_large`),
  closed in `Assembly/NearCubic/Survivor/Realized.lean` and `…/Unrealized.lean`.
- **[144a] one-sided equal-count region (Lean improvement).**  The transfer clause
  and connectedness force a singleton support against two-vertex pattern supports
  (`ReadingProfiles.onesided_singleton`); the partition
  `K .sameTokenPairPartition` keeps the other regions.
- **[144a] sub-arms (Lean improvement).**  The separated configuration in
  W ∧ Tri(k) (9991: `n ≤ 729` against `n ≥ C_sp(C_sp+1) + 9`) and the sub-arm
  W ∧ Tri(1) ∧ Tri(2) ∧ EndEdgesFree (9855: `σ ≤ 2637` against `σ > 102·103`;
  `lem:144a-tri-arm-empty`) are empty at G.
- **[19] strict arm, first band at `C_sp` (Lean improvement).**
  `8n ≤ 32s + 125s²` at `s = n − σ` (`K .highSurplusBound`) with `σ > C_sp⌈√n⌉`
  refutes `n ≤ C² + C + 1 + t*` (`K .highSurplusOrder`,
  `registered_firstBand_excluded`, `Assembly/Surplus/RegisteredConstants.lean`):
  every strict-surplus residual has `n > 4.55·10⁴⁷`.
- **(F2) of the cold corridor (Lean improvement).**  G's two readings of
  `J_right` reconstruct G, so no segment carries (F2)
  (`Corridor.not_firstFailureDefect`).
- **Q1 of exit (4).**  Q1 compares the readings of two declared coordinates of G
  in `G − Z` and is false at G (`Q1TargetDefect.false_of_avoids`,
  `Graph/ExitFourFamily.lean`).  Q2, Q3, Q5 and the trace-basin alternatives (a),
  (b) are read on `GConstructedPiece` realizations and are live tests (a fold pair
  of a basin makes (a) occur, `traceLocalTargetDefect_of_foldPair`).

## Density theorem

**Lean improvement**: the paper states the density bound as a conjecture
(`rem:r8-density-conjecture`).  `Graph/DensityCert/` proves, for any finite simple
graph, `density_le_of_admissible_in (G) (W) (hc : ConnIn G W) (ha : AdmIn G W) :
dIn G W ≤ 0 ∨ EmbOnto CG.x15.graph G W`: a connected induced subgraph that is
subcubic, has no cycle of length 4, 8, 16 or 32 and no induced P13 has
`8e ≤ 11|W|` unless it is X15 (graph6 `N?AA@AODAOP_KGGoGH?`).  Axioms: propext,
Classical.choice, Quot.sound and the `native_decide` helper axioms.

- Blocks and bridges (`Blocks.lean`, `BlocksAux.lean`): blocks of a subcubic graph
  are vertex-disjoint, each bridge adds 8 to `8e − 11n`, and induced paths
  concatenate across bridges.
- Ear closure (`Ear.lean`, `closure_of_cert`): every 2-connected admissible graph
  is a copy of a member of any list `L ∋ K₂` with `ClosureCert L`.
- Certificate (`Checker`, `Search`, `Data`, `CertShard00`-`15`, `Cert.lean`): the
  list is K₂ plus the 5519 two-connected admissible blocks (all with ≤ 21
  vertices); every ear extension is rejected by a verified witness or matched by a
  verified isomorphism; 16 `native_decide` shards.
- Tree DP (`DP.lean`, `rooted_bound`): `degIn W r ≤ 2 → dIn W ≤ fTab (lamIn W r)`,
  `fTab = −11, −9, −9, −8, −5, −5, −3, −2, 0, 0, 3, 3`.
- X15 landings (`X15Landing.lean`, `x15_exit_landings`): glued to an induced P13
  with no forbidden cycle and no two disjoint induced P13s, the three exits of X15
  never all land on the path, and two land at distance ≥ 10.

Facts at G (`Strategy/SpineRows/Route8Density.lean`; contracts in
`Graph/Route8HubFree.lean`, `Graph/Route8X15Landing.lean`,
`Contracts/RouteEight/Density.lean`), on the common prefix of `[186]` and `[348]`
after 9807:

- 9700 `route8HubFreeDensity`: every canonical hub-free piece X of R has
  `ex(X) ≤ 0` or is an X15 copy.
- 9701 `route8X15LongLandings`: a hub-free X15 copy has `ν(X) ≥ 2` for every valid
  placement system (9800 with Q = {P}).
- 9702 `route8HubFreePi`: `13·ex(X) ≤ 30·ν(X)` on thick hub-free pieces.
- 9703 `route8HubPieceExcess`: `0 < σ_X → ex(X) ≤ (F−1)·s·σ_X` (the first part of
  `lem:r8-hub-free-suffices`).
- 9704 `route8ArmClosure`: `F ≤ 14 → SufficientlyLargeForNetCap … n → False`
  (9807 at c = 30 with 9702, 9703 and σ ≤ T).
- 9705/9706: the exact split on `F ≤ 14 ∧ SufficientlyLargeForNetCap … n`.

## Window exchanges at G

Three exchange facts about G at one or two windows of G's own maximum window packing
`P₀ = canonicalWindowPacking` (`R` its remainder).  X15 enters only as the shape of
induced copies `e : x15Graph ↪g G` with every vertex in G's `R`.  The rows read only G's
ledger facts: target avoidance (`selection`), the dyadic target law (`cubicBaseline`)
and the maximality of `P₀` (`canonicalWindowPacking_spec`).  Axioms: propext,
Classical.choice, Quot.sound and the `native_decide` helper axioms.

Facts at G (`Strategy/SpineRows/Route8WindowExchange.lean`; statements in
`Statements/Route8WindowExchange.lean`, contracts in
`Contracts/RouteEight/WindowExchange.lean`), on the common prefix of `[186]` and `[348]`
after 9706:

- 9810 `route8X15DoubleLanding` (reads `cubicBaseline` for the dyadic target law and
  `selection` for G's target avoidance): at window order 13, an induced copy of X15 in R
  whose only edges to a window `P ∈ P₀` are `e a — p i` and `e b — p j`, for distinct
  exits `a, b ∈ {4, 6, 9}`, has `{a, b} = {6, 9}` and `{i, j}` one of `{0,10}`,
  `{0,11}`, `{1,11}`, `{1,12}`, `{2,12}`.  Exit 4 never double-lands; `{0, 12}` gives
  two disjoint induced 13-vertex paths in G on the copy and `P`, against the maximality
  of `P₀`.
- 9811 `route8ArmPairTrigger` (reads no prerequisite; the maximality of `P₀` is
  `canonicalWindowPacking_spec`): two vertex-disjoint arms in R landing at positions
  `i < j` of one window, of lengths at least `(order − 1 − i, j)` and meeting
  `p[0..i]` resp. `p[j..order−1]` only at their landing edges, do not exist.
- 9812 `route8X15HeavyPair` (reads `cubicBaseline` and `selection`): at window order 13,
  for two distinct windows of `P₀` with subcubic vertices and an induced copy of X15 in
  R with distinct exits landing on both, the rungs between the windows number at most 6
  when exit 4 lands and at most 8 otherwise.  A pair with at least 9 rungs carries no
  such copy.  The proof reads a finite certificate (`HeavyPairCert*`, `native_decide`
  shards) at G: every 7, resp. 9, rungs between the two windows give in G a cycle of
  length 4, 8, 16 or 32 or a window vertex of degree at least 4.
