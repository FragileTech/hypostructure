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
  closes against `[12]` (see Paper findings (no sorry), "[11], [12], [36]/[37]").
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

## [24]: now paper-exact, both clauses published

*Family F5; recorded in the final pass (group SD); fixed 2026-09-27 (fix2-SC).*

- **Paper.** `[24]` "bounded cold-mass return from [153]: `θ ≤ θ_win + o(1)`;
  high entropy: `θ ≤ 0.01198542083…`" (`prop:p13-density`, tex 8480-8551).
- **Lean.** `K .densityCap` (`DensityCapStatement`) publishes both clauses at
  G: the window-only cap `2·rate·scales·ν ≤ (scales+1)(δn+T) +
  slack·rate·scales·T` (`θ ≤ θ_win + o(1)`), and the high-entropy clause in the
  paper's own conditional form: if the joint window/remainder comparison
  `(2^{rate·scales·ν})^d · n^{|R₀|} ≤ |range stateOf|^d` holds for a state map on
  G's labelled skeleton class, then `(2^{rate·scales·ν})^d · n^{|R₀|} ≤
  skeletonBudget^d` (`eq:feasibility`, whose solution is
  `θ ≤ 0.01198542083… + o(1)`).  Proof: `lem:skeleton-dominates` at G
  (`densityCap_of_coldMassBounded`).
- **Difference.** None.

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
  publishes.  `[54]` is the exact decision `entropyJointRealizationDichotomy`
  on the active arm: its joint arm closes (`entropyCapBoundRow
  .runAndCloseIncompatible`), its other arm returns the `[54]` residual
  ([#residual-54](#residual-54)).
- **Demand (fixed 2026-09-27, fix2-SC).**  `jointPackageDemand` counts the
  package of **all** `p₁₃` windows of `P₀`, `2^{rate·scales·|P₀|}·remainderStates(R₀)`,
  as `eq:entropy-cap` does (tex 5259-5282: `L_win = c₁₃θn log₂ n`, `θ = p₁₃/n`;
  `116.808581006 = c₁₃ − 1.3`); `[52]` likewise.  Until then the Lean counted
  only `𝒫_hot`, so on arms with `𝒫_hot ⊊ P₀` the Lean active arm was smaller
  than the paper's.  `[54]` reads `[21]`, `K .skeletonDominates`, `[48]`,
  `[51]`, `[52]`; its case split is on `WindowFamilyRealized P₀`.
- **Dichotomies on the path to `[54]` that concern realization.**

  | node | predicate | Lean key / decl | arm to `[54]` | family |
  |---|---|---|---|---|
  | `[22]` | `𝒫_hot` retained, or `𝒫_hot = ∅ ∧ ¬ WindowFamilyRealized ∅` (a partition fact, not a decision) | `K .hotColdPartition`, `IsHotColdWindowPartition` (`Statements/Spine.lean`) | both | window package of `𝒫_hot` × remainder states × **full** curvature code `2^{c_Ω r_Ω}` (`retainedCode`) |
  | `[22]`/`[23]` | `2^{rate·s·|𝒫_hot|} ≤ B` | `K .barrierCap`/`K .barrierOverflow`, `barrierDichotomy` (`Strategy/EntropyClosure.lean`) | cap | window package of `𝒫_hot` |
  | `[158]` | `2^{b_P} ≤ |𝒢_{n,m}|` | `K .windowPackageRealized`/`Unrealized`, `windowPackageRealizationDichotomy` (`Strategy/SpineRows/WindowPackage.lean`) | both | window package of `P₀` alone |
  | `[50]` | `n^{|R|} ≤ |𝒢(R)|^d` | `K .remainderEntropyHigh`/`Low` | high | remainder states alone |
  | `[53]` | `B < demand·2^F` | `K .entropyCapActive`/`K .entropyCapBound`, `entropyCapDichotomy` | active | all-window package × remainder states × forced bits (a count, not a realization) |

  No dichotomy decides the realization of the sub-family (remainder states) ×
  (forced bits), with or without the window package.  On `[54]`'s own branch
  (`[53]` active) `B < demand·2^F ≤ retainedCode P₀`, so
  `¬ WindowFamilyRealized P₀` holds there.
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
- **No-arm.** The `[173]` no-arm (`K .exactCollisionFails`, `[174]`) is closed
  at the node against `K .route8Rate`: see "Closed from G's facts",
  `[173]`/`[174]`.

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
- **Fix pass (TB, fix2).** [70] reads the fact of its incoming arm, as the
  paper's edges [69] → [70] and [79] → [80] run: on the heavy arm
  `fanCertificateCapRow` reads `K .typeBFanLocalDichotomy`, on the degree-four
  arm `degreeFourFanCertificateCapRow` reads `K .typeBFanDegreeFourProfile`,
  and the cap is published at the Type B support of that fact.  The cap is
  stated at G's canonical fan-certificate labelling
  (`canonicalFanCertificateLabelling`, the `Classical.choice` of a labelling of
  `h` in `G`), and [71]/[80] decide whether that labelling is present at every
  assigned centre (`K .fanCertificateMarked`: `∃ marking, canonical… = some
  marking ∧ d_G(h) ≤ cap`; `K .fanCertificateResidual`: `canonical… = none` at
  a high centre).

## [74]/[82] → [76]/[85] → [77]: the bridge reduction, the fan mass and the route-8 entry

*Family F2 (Type B), fix pass (TB, fix2).*

- **Paper** (tex:976–979, 1020–1023; `prop:typeB-bridge-reduction` tex 14289,
  `lem:typeB-bridge-deficit-bound` tex 14803, `def:typeB-residual-mass`
  tex 14682). The B2 yes edge goes [74] → [76] → [77]; [74] is not a diamond.
  The fan-mass arms go [75] → [76] and [84] → [85].  [76] → [77] "route-8
  cores continue in Part IX".
- **Lean now.**
  - [74] (`K .typeBDisjointLedger`, `TypeBB2LedgerAt`) is published from the
    B2 fact `K .typeBB2Choice` unconditionally: the support is B2-paid, its
    canonical disjoint choice refines every candidate charge and its canonical
    B2 ledger `canonicalTypeBDisjointChoice data G Y_X H_X` exists (the core's
    high centres are assigned on every lane,
    `TypeBLaneMember.centres_subset`) with its exact augmented refinement,
    post-ledger hygiene and grouped envelope coverage.  The contract uses the B2
    fact (`typeBB2LedgerAt … member b2`).
  - [74] `prop:typeB-bridge-reduction` (`K .typeBExcluded`) is the reduction as
    an inequality on that ledger: `Σ_{remaining core} ch ≤ s·No(X)` with
    `s·No(X) = s·def⁺(Y_X) − s·σ(H_X) − |Y_X|`
    (`TypeBEnvelopeCharge.remainingCore_le_scaledNetCharge`, from (B-ledger) at
    `(Y_X, H_X)`, `augmentedLedgerWith_add_card`).  A nonnegative remaining core
    (no route-8 residual) gives `N₀(X) ≥ 0`.
  - [75]/[84] (`K .fanCertificateResidualMass`, `K .typeBOverlapObstructionMass`)
    carry the arm's witness (a centre without G's canonical labelling, or G's
    canonical reflected minimal overlap obstruction) and
    `lem:typeB-bridge-deficit-bound` at `(Y_X, H_X)` itself
    (`TypeBBridgeDeficitBoundAt`): when the non-window core carries no route-8
    residual profile (`BridgeResidualComponentAt Y_X`),
    `|Y_X| + s·σ(H_X) ≤ s·def⁺(Y_X) + F·s·σ(H_X)`, i.e.
    `N₀₋(X) ≤ 8·Σ_{h∈H_X}(d_G(h) − 3)` (`bridgeDeficitBound_assigned`).  The
    per-centre degree arithmetic `CentreBridgeMassBound` is no longer the
    [75]/[84] content.
  - [76]/[85] (`K .typeBExclusionResidual`) is the join of its arms: B2-paid
    with the remaining core carrying the whole deficit, or B2 fails and the
    [75]/[84] bound holds.  Producers: `typeBExclusionResidualRow` (reads
    `K .typeBDisjointLedger` and `K .typeBExcluded`),
    `typeBCertificateMassExclusionRow` (reads `K .fanCertificateResidualMass`),
    `typeBObstructionMassExclusionRow` (reads `K .typeBOverlapObstructionMass`),
    `typeBDegreeFourExclusionResidualRow` (reads `K .typeBDegreeFourClosed`).
    It is no longer derivable from the entry alone as a free-standing
    implication: each producer derives it from its arm's fact.
  - [77] (`K .typeBRoute8Entry`, idx 2801, `selectedTypeBRoute8Entry`) reads
    `K .typeBExclusionResidual`: a negative Type B support (`s·No(X) < 0`)
    hands the negative remaining core of its canonical B2 ledger to route 8, or
    is a bridge residual charged to its surplus.  The shared route-8 census
    then runs on the same ledger.
  - [82] (`K .typeBDegreeFourClosed`) is one node: certificate-closed
    (`lem:typeB-exclusion` Step 1, `c ≤ 1` and `s·D_B ≤ 0`), or B2-paid with the
    remaining core carrying the whole deficit.  It no longer publishes
    `K .typeBDisjointLedger` / `K .typeBExcluded` (those are [74]'s keys).
- **[85] → [77] (tex 1025-1034, 979).** Part VII's [85] is a terminal ellipse.
  Part VII is the expansion of Part VI's degree-4 no-branch of [68] (caption of
  `fig:proof-diagram-part-vi`: "The degree-4 no-branch of [68] is expanded in
  Part VII"); in Part VI that branch runs [68] → [70] → … → [76] → [77].  So
  [85] is [76] for the degree-4 branch and its route-8 cores continue at [77]
  as in Part VI.  No closure is available at [85]: the degree-4 support can be
  negative at G (the ordinary/decorated lanes have `N₀(X₀) < 0`), and the
  paper's own statement is "cannot carry linear deficit outside route 8", i.e.
  the deficit goes to route 8.  The Lean runs [85] → [77] with the same
  `K .typeBRoute8Entry` reader; this is the Part VI topology, not an extra
  edge.

## [65]--[85]: the Type B support is the one support fixed by the entry

*Family F2 (Type B), G-repair, final pass and fix pass (TB, fix2).*

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
  - **Absorbed support** (fix pass, #7).  The support of a selected half-edge
    `ε` outside node [153]'s subcubic candidates is
    `canonicalTypeBAbsorbedSupportAt ε = (J_ε, {z_ε})`: `z_ε` is the least high
    vertex of `ε`'s corridor prefix, and `J_ε` is the prefix of the corridor
    **through `z_ε`** (`AbsorbedHandoffAt`, `core = prefixSupport firstIndex`).
    The first failure occurs on entering `z` (`def:cold-corridor-first-failure`
    (F4): "the corridor first enters a declared Type B handoff envelope"), so
    `J` contains no second high vertex after `z`: `AbsorbedHandoffAt` states
    `centres J ⊆ {z}`, proved from the earlier-degree bound of the fan data.
    Hence `H_X = {z} ⊇ centres(Y_X)` on this lane too
    (`TypeBAbsorbedLane.centres_subset`), and the B2 ledger / B2-paid clauses
    are no longer guarded by an unverified `centres Y ⊆ H`.
    *Merge note:* this changes the core of the [177] envelope from the prefix
    through the trace end to the prefix through `z` (a statement-level change
    in `AbsorbedHandoffAt` and a few lines of
    `Contracts.TypeB.absorbedGermDecoratedAssignedSupport`: `core`,
    `centreCore`, the new `onlyCentre`, `coreInside` by `prefixSupport_mono`);
    the [177] PAPER-ERROR sorry `coldAbsorbedPrefix_subset_remainder` is read
    unchanged.
  - **Every case-(ii) half-edge is charged** (fix pass, #6).
    `K .typeBAbsorbedCharge` (idx 2800, [177], `typeBAbsorbedChargeRow`) is
    `∀ ε ∉ candidates, ∃ J z, canonicalTypeBAbsorbedSupportAt ε = some (J, {z})
    ∧ z high ∧ z ∈ J ∧ centres J ⊆ {z} ∧ J ⊆ R(P₀) ∧
    TypeBBridgeDeficitBoundAt J {z}`: each half-edge the bounded arm discards
    has its own pinned Type B support, and that support's negative part is
    charged to `σ(z)` (`lem:typeB-bridge-deficit-bound`), as the lemma says
    ("every half-edge it discards is charged to the Type B ledger", tex 7933).
    The [177] → [65] entry (`absorbedGermFanEnvelopeRow`) reads it: the lane's
    support is its instance at G's canonical absorbed half-edge.  [175]'s
    per-corridor question ("selected corridor meets a high-degree vertex?") is
    published per corridor by `K .absorbedGermSplit` / `K .absorbedGermFanData`
    (every `ε` is a candidate or has its first high centre) and, for the
    case-(ii) corridors, by `K .typeBAbsorbedCharge`.  The executor has one
    path, so the continuation [67]--[85] runs at one support: the decision
    `typeBAbsorbedHalfEdgeDichotomy` splits at the one canonical object
    `canonicalTypeBAbsorbedHalfEdge` (`some` / `none`), which is the paper's
    [175] edge into [177] at that corridor; every other case-(ii) corridor's
    charge is the pinned `∀ ε` fact.
  - Every Type B key is `TypeBLaneAt P = ∃ Y H, TypeBLaneMember Y H ∧ P Y H`.
    The lanes are mutually exclusive and each has one support
    (`Contracts.TypeB.TypeBLaneMember.unique`, from
    `ordinary_decorated_exclusive` and `netChargeCap_not_exactCollisionFails`),
    so a decision splits `P` / `¬P` at that one support
    (`TypeBLaneAt.split`, `TypeBLaneAt.not_and_not`).  The same-token disjunct
    of [65] is separated from the continuation lanes by the
    `K .surplusAtOrBelow` read of [68]/[70] (`typeBLanes_of_entry`); no lemma
    states that exclusivity.
  - Decisions read their predecessors: [68] `typeBFanEntry` (and
    `surplusAtOrBelow`), [71]/[80] `fanCertificateCap`, [72] and [81]
    `typeBHybridEntry` (B1) and `fanCertificateMarked` (the `[71]` marking),
    `prop:typeB-bridge-sublinear`'s test (`typeBSublinearDichotomy`)
    `typeBBridgeSublinear`.
  - **No direct-cycle diamond** (fix pass, #5).  The paper excludes the direct
    fan-window cycles inside [72] ("local fan-window ledger complete",
    `lem:typeB-direct-fan-window-cycles`); Part VII has no diamond between
    [80] and [81].  The former decision `directCycleDichotomy` (keys
    `typeBDirectCycle` / `typeBDirectCycleFree`) and its closure against
    `K .selection` are removed; `K .typeBDirectCycleFree` is now a fact row
    (`typeBDirectCycleFreeRow`, reads `K .fanCertificateMarked` and
    `K .selection`), and `K .typeBHybridEntry` (B1) reads it.  Key
    `typeBDirectCycle` (idx 81) is deleted.
  - **B2 at G's lane support** (fix pass, #1).  `TypeBB2At Y H` is the
    paper's B2 at `(Y_X, H_X)`: every demand `h ∈ H_X` carries G's canonical
    `[71]` labelling under the label-packing cap (no fan-certificate residual
    centre, `def:typeB-bridge-statements` B2), and the demands admit a choice of
    candidate entries with pairwise disjoint ledger supports.  Every candidate
    entry of `def:typeB-candidate-ledger` is evaluated on the assigned fan
    envelope of the support itself, `E_h = {h} ∪ Y_X ∪ H_X`
    (`TypeBRefinedSupport.fanEnvelope`, which is `typeBFanEnvelope`), `h` is a
    high centre of `H_X`, and `A_h` ranges over neighbours of `h` in
    `Y_X \ H_X`.  The degree window is the demand's: `δ < d_G(h)` and the
    `[71]` cap `d_G(h) ≤ fanPackingCap`; no numeral appears.  The former
    candidate profiles (`TypeBProfileSchedule.profileCandidatesWith`: the
    2-ball envelope of every hub with `4 ≤ d ≤ 8` and a constructed labelling)
    are no longer read, and `TypeBProfileSchedule` / `TypeBHybridLedger` left
    the build.  [72]'s yes arm is `B1 ∧ B2` at the support ("local fan-window
    ledger complete; B2 disjointness holds"); its no arm is the marking with
    G's canonical minimal overlap obstruction
    (`canonicalOverlapObstruction`, pinned).
  - [81] on the degree-four arm is the paper's test (tex 1019): `c ≤ 1` at
    every assigned centre, or `c ≥ 2` with B2 (`K .typeBDegreeFourLedger`,
    with the B1 ledger), against `c ≥ 2` and B2 fails, with G's canonical
    minimal overlap obstruction (`K .typeBDegreeFourOverlap`, [83]); `c` is the
    closed count at the assigned fan envelope.  The heavy arm keeps [72]'s B2
    test.
  - The fan envelope at a centre `h` of the support `(Y, H)` is the assigned
    envelope `typeBFanEnvelope Y H h = {h} ∪ Y ∪ H`: a fan neighbour is
    cubic-closed exactly when its two non-`h` incidences are assigned to the
    support (`def:marked-typeB-fan`, `E_h` of `def:typeB-residual-mass`).  The
    B1 entry, B2's candidate entries, the degree-four profile, the `[81]` count
    `c`, the residual mass and the assigned profiles of `def:fan-closed-port` and
    its routings are all at that envelope.
  - The assigned profiles (`IsFixedTypeBProfile`) have their centre in `H_X`
    (fix pass, #12).  `def:fan-closed-port` is no longer a key: it was a
    definitional unfolding (`fanClosedPortAt` has no hypothesis); the routing
    contracts cite `fanClosedPortAt` directly and `compatiblePairFanClosureRow`
    reads the node-[65] entry.  Key `fanClosedPort` (idx 442) is deleted.
  - The global-local reflection, B2(a)--(d) hygiene and the [76] B2-paid
    residual are stated at the lane's own core `Y_X` (a connected support
    inside `R(P₀)`, `TypeBLaneMember.core_subset_remainder`), not only when
    `Y_X` is a canonical piece.
  - The window union is `W₀ = windowSupport P₀`, and the bridge statements
    are at `P₀` and at G's canonical piece collections; the
    `prop:typeB-bridge-reduction` obstruction at a piece is G's canonical one
    (`canonicalOverlapObstruction`).  The route-8 set of
    `lem:typeB-bridge-with-route8-core` in `K .typeBBridgeMass` is G's
    canonical collection `𝒜` (`canonicalBridgeRoute8Pieces`: the pieces on
    which the Type A routing/unsaturation pair fails), not an arbitrary subset
    of the pieces (fix pass, #13).  The presentation facts (accepted
    quadrilateral, dyadic target, fan-cap, deficit and bridge-mass slacks) are
    published once with `K .cubicBaseline` (`TypeBPresentationStatement`) and
    read with `inputs.get`.
- **Triangular keys** (`def:triangular-fan-core`, tex 2378; tex 2413, 2452,
  2489, 2521). They are stated at a *heavy* center (`d_G(h) > δ + 1`,
  `def:heavy-center-triangular-port` tex 2223), and so run on the heavy arm
  [69], feeding `prop:triangular-port-typeB-routing` (tex 13780); the
  degree-four arm runs only the routings used by
  `cor:degree-four-local-activation` (tex 2336).  The paper's
  cross-reference table (tex 1871--1881) lists these lemmas at [78]--[81];
  that contradicts their own statements, which are followed here.  Fix pass:
  `K .triangularFanCore`, `K .triangularFirstLanding` and
  `K .triangularCrossShoulder` are stated at the heavy assigned centres of the
  Type B support (`TypeBLaneAt`, the core row reads `K .typeBFanHeavyCentre`)
  and at G's canonical shoulders, core and completion/central/cross/outside
  incidences (`triangularShoulders`, `triangularCore`, `triangularCompletion`,
  …), not over arbitrary predicates; the arbitrary-predicate forms remain only
  as library laws (`TriangularFanCoreLaw`, …) instantiated at G's objects.

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
- **Per-peel retest (fix2-TR).**  The per-stage answers before the terminal
  set (saturated, exit `(4)` with the stage's canonical witness, peel) are the
  definition of `canonicalPeelStep`; the former last clause of
  `K .typeAExitFourFiniteDescent` restated that definition and is removed.  The
  retest is asked on the ledger at each receiver's terminal set
  (`typeAExitFourRetestDichotomy`, key 2000): the terminal set is the first
  stage at which the answer is not "saturated with an exit-`(4)` witness".
  Exits `(1)`--`(3)` are asked again there (keys 2002-2010).  The no arm's node
  `[92]` is recorded under Paper findings.

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

## [118] → [123] → [124]: the route-8 alternative of `[123]`, closed at `[124]`

*fix2-TR, then close-C3.*  fix2-TR sent the two-support entry `[118]` (the
yes arm of `[117]`) through the unified ledger `selectedTypeBRoute8Continuation`
(tex 1134, edge `(residual)--(pressure)`).  close-C3 closes it at `[124]`
instead, because on this arm the entry is a route-`8` entry of the collection
`𝒳_A` that carries the large-budget deficit (`[113]` yes): that is the
route-`8` alternative of `thm:large-budget-route8-only` ("If that two-support
entry is a route-8 entry, then `prop:typeA-route8-closure-from-nogo`
applies", tex 17124-17127), and `prop:typeA-route8-closure-from-nogo`
(tex 12758-12785) derives (T1)--(T5) of `def:typeA-terminal-two-carrier`
(tex 12636-12668) on exactly this path.  See Closed from G's facts,
"[118]/[124]".  The unified ledger of `[123]` is still entered from the
`[113]`-no arm, which reaches `[181]`, `[183]`--`[186]`.

## [123]: the deterministic procedure, now paper-exact

*fix2-TR.*  `route8DescentChain` (`Statements/RouteEight.lean`) is the paper's
deterministic procedure (`thm:large-budget-route8-only`, tex 17095-17135),
iterated `|\tilde\Xi|` times from the empty peeling: `route8DescentStep` runs
the reduced-rate test; on a pass it takes the lexicographically first
two-support entry of the current unpeeled ledger (`route8LexFirst`, key
`route8IndexKey`: sorted vertex codes of `X`, then `w`, then `u`, in G's fixed
enumeration, tex 6419) and peels it when it is target-defect; otherwise it
stops.  `route8DescentChain_stageOutcome` (`Contracts/RouteEight/Descent.lean`)
proves the terminal stage is a recorded peel chain with exact accounting that
fails the rate or passes it with a true two-support entry.  The former
`Classical.epsilon` stage is removed.

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

- **Paper** (diagram tex:1204, 1229-1246; `prop:single-graph-sparse-pressure-routing`).
  The [131] "count holds: free pairs" edge enters the [137] diamond
  "coupled excess D_all>0?"; D_all = 0 goes to [138], D_all > 0 to [139].
- **Lean.** The free side runs `freePairCoupledExcessDichotomy`
  (`hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/FibrePressure.lean`),
  which reads its predecessor `K .freePairEntropySandwich` ([131] "count holds")
  and splits the same overload predicate as the blocked side's
  `coupledExcessDichotomy`: `K .sparsePressureOverload` versus its literal
  negation `K .sparsePressureNearCubic` at G's canonical certified ledger.  On
  the independent branch both arms run `freePairSurplusEstimateRow`
  (`HomogeneousBottleneckRows/FreePairCoupledExcess.lean`, contract lemma
  `Graph.Contracts.SurplusPair.spineSurplusEstimate_of_pairSandwich`) and close
  through `runAndCloseIncompatible … (K .surplusAbove) (K .spineSurplusEstimate)`.
  Caller: `Assembly.Internal.strictSurplusIndependent`
  (`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict/Independent.lean`).
- **Difference.** The D_all > 0 arm on the free side is closed by [138]'s
  estimate instead of continuing to [139].  An earlier version of
  `freePairCoupledExcessDichotomy` published the estimate itself as its no-arm
  key, so its keys were not complements; it now has the exact complement keys
  above.
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

## [181]/[183]: the committed maximal ledger `P₀`, now paper-exact

*fix2-TR.*  `P₀ = canonicalRoute8Partition` is the partition of
`canonicalRoute8DemandRecord`, the lexicographically first maximizing ledger
(tex 15537: "choose once and for all the lexicographically first ledger
maximizing first `|Ξ₃|`, then `|Ξ₂|`"): among the node-`[349]` records it
minimizes `route8LedgerKey` (the classes `Ξ₃`, `Ξ₂`, `Ξ_res` as sorted entry
keys, then `A(ξ)` entry by entry; `canonicalRoute8DemandRecord_lexFirst`,
`Statements/CanonicalRouteEight.lean`).  Key 349 now publishes the pinned
record (`Route8DemandLedgerPinnedStatement`), and node `[181]`'s yes arm names
G's canonical witness-free entry `ξ*` (`canonicalRoute8UnpaidEntry`).

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
  the implication fails.  Each failure key is pinned to the same canonical
  object as its test (`∃ x, canonicalX = some x ∧ ¬ Q x`).  The [179] and [180]
  outcome splits are exact P/¬P at the pinned object:
  `Nonempty (PairSystemEarlyOutcome returns)` at G's canonical return system
  (`K .pairSystemEarlyOutcome` / `K .pairSystemNoEarlyOutcome`) and
  `Nonempty (PairIncrementEarlyOutcome serial)` at G's canonical serial system
  (`K .pairIncrementEarlyOutcome` / `K .pairIncrementNoEarlyOutcome`).  No
  outcome is chosen by `canonicalChoice`.  The paper's precedence is kept:
  [179] lists the routed alternatives (i)--(iv) before the serial (v) (tex
  5110-5130), and [180] reads "periodic sparse-exit/Type B, or full-modulus
  arithmetic" (diagram tex 1213).  On the negative arm coverage yields the
  serial system (`canonicalPairSerialSystem`, a serial system on exactly the
  canonical returns) or the arithmetic input (`pairSerialDemandSystemRow`,
  `pairSerialArithmeticRow`).  The paper claims "exactly one" occurs.  The Lean
  does not prove exclusivity; the precedence decides, and when both (iv) and
  (v) hold the branch takes the Type B continuation, as the paper does.
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
  reads its diagram predecessor [129] (`K .baselineSpineDemand`) and the [125]
  active family, and splits `Graph.HasSparsePairBlocker activation Π(𝒜₀)`
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
- **Difference.** Earlier the test read clauses (d)/(e) only.  One addition:
  on the blocked arm, before [132], the exact decision
  `pairResponseObstructionDichotomy` (keys 2900/2901) tests clause (e) at the
  same activation and closes its positive arm against the [125] survivor.
  That arm is the paper's own dead clause (see Closed from G's facts, "[130]--[134]
  blocker (e)"), closed at the node from G's ledger rather than only asserted.

## `def:surplus-blockers` (d), (e): the determination certificate of `r_π`

*Group SP (Surplus / Pair / [144]).*

- **Paper** (tex 2897-2903; `lem:sparse-pair-dependence-exit`, tex 4675-4718).
  (d) is "a boundary-degree-profile coordinate which prevents a quotient or
  replacement from staying in a single fibre"; (e) is "a target-response
  coordinate witnessing a target-defective quotient, target-complete
  compression, or support-dependence event".  In the lemma both arise from an
  inclusion-minimal determination of `r_π` from a subfamily `B`.
- **Lean.** `SparsePairDetermination` is that determination: a functional,
  rank-reducing attempted declared quotient of G's pair-response family at the
  activation, with an inclusion-minimal certificate of `r_π`, whose labels
  carry G's exact response data (`SparsePairExactValuation`: a valuation of
  the quotient labels equal, at every `c ∈ ℛ_Π`, to the pair (boundary-degree
  profile, `canonicalCoordinateResponse`) of `c` read on G's piece at the
  determination support `Z` -- the `𝐝_∂` and response components of
  `ρ^ex`, `def:exact-response-profile`).  So two coordinates the quotient
  identifies have the same response and the same boundary-degree profile on G
  (`SparsePairDetermination.canonicalResponse_eq_of_label_eq`,
  `SparsePairDetermination.profile_eq_of_label_eq`): the quotient is
  target-complete on G's coordinates, as the paper's determination quotient
  is (it comes from `lem:target-rank-circuit`, a *functional admissible* rank
  quotient; `def:target-complete-quotient` (a), (b)).
  `SparsePairDEProfileObstructionAt` (d) adds that the quotient identifies
  `r_π` with a determiner `b` (`label b = label r_π`, the case `ℬ = {b}` of
  `lem:target-rank-circuit`) and that these two identified states, `r_π` and
  `b` read on G's piece at `Z`, lie in different boundary-degree fibres
  (`lem:degree-profile-fibres`).  `SparsePairDEResponseObstructionAt` (e) adds
  one of the three events: `ResidualTargetDefect` among `{r_π} ∪ B`,
  `ReplacementSupport` of the determination support, or a whole-graph support
  with a strictly smaller closed representative.
- **Difference.** Earlier, (d) compared the two demands' declared supports of
  every pair with no attempted identification, and later it compared any two
  coordinates of `{r_π} ∪ B` under a quotient with a free labelling and
  valuation.  Both were generically true: a round-2 audit check
  manufactured the free determination for
  every `b` profile-separated from `r_π`.  With the valuation tied to G's
  response, the manufactured quotient no longer qualifies: it would identify
  `b` with `r_π` only if G's two readings at `Z` respond identically to every
  `∂Z`-context.  (e) omitted the support-dependence event.
- **Is (d) dead at G?** Yes, after the completeness check (fix2 follow-up).
  An earlier verdict in this pass ("no ledger fact refutes (d), live test")
  rested on an incomplete construction: the determination quotient's
  valuation read only the response component of `ρ^ex`, not the `𝐝_∂`
  component, i.e. the admissibility the paper requires of it was missing.
  With it built, [130] publishes `lem:degree-profile-fibres` at G's pair
  family (`K .pairDegreeProfileFibres`, idx 2902) and closes clause (d)
  against it (keys 2903/2904); see Closed from G's facts, "[130] blocker (d)".
  (e) is closed at G as well (same section).

## [131]: `lem:mixed-sparse-spine-dependence` is the paper's statement, with no consumer

*Group SP (Surplus / Pair / [144]).*

- **Paper** (tex 4872-4887).  If `ℐ_spine ∪ ℛ_{𝒜₀}` is not independently
  target-testable, G has a sparse surplus exit or some pair has a blocker of
  type (d) or (e).
- **Lean.** `MixedSparseSpineDependenceStatement` (key 203) is exactly that at
  G's canonical spine family and canonical activation, at G's own quotient:
  `canonicalMixedDependenceQuotient` is the canonical functional admissible
  declared quotient of `ℐ_spine ∪ ℛ_{𝒜₀}` that is not label-injective (it
  exists exactly when the union is not independently target-testable), and
  the statement is `∀ q, canonicalMixedDependenceQuotient … = some q →
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

- **Lean.** `SurplusPresentationStatement` (the deficit safety, join slack,
  routing-label count and spine scale) is the third component of the one
  presentation-law fact `K .cubicBaseline` (`PresentationLawsStatement`),
  published at the entry by `cubicBaselineRow`.  The surplus, pair and [144]
  rows read it, the dyadic target (from its Type B component) and `3 ≤ δ` /
  `¬ LengthOK 2` (from its cubic component) with `inputs.get`.  No
  surplus/pair/[144] row reads a `Data` field.  (Integration: the former key
  `surplusPresentation`, idx 2200, published at [125], was folded into this
  entry fact and deleted.)

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
  once at the entry as the fourth component (`SpinePresentationLawsStatement`)
  of the one presentation-law fact `K .cubicBaseline`; the dyadic target is read
  from its Type B component (integration: the former key
  `spinePresentationLaws`, idx 2302, was folded in and deleted); node `[16]` is the
  row `hssTargetCycleRow` (`K .hssTargetCycle`, idx 2303) closed against
  `K .selection`.  `3 ≤ δ` / `δ = 3` are read from `K .cubicBaseline`.

## fix2-TR: Type A and Route 8 round-2 repairs (paper-exact)

- **[86] (`lem:typeA-exclusion`, key 343).**  Alternative (iv), the admissible
  silent-core residual profile, is "obtained from a saturated receiver" (def
  10790): it now asks `∃ receiver ∈ saturatedReceivers X`.  The contract derives
  it from `N₀(X) < 0`, `σ(X) = 0` and node `[13]`'s routing
  (`zeroSurplusRoutingAt_of_normalized`) through the unsaturated discharge
  (`card_le_scaled_deficiency_of_no_saturated`); the row reads
  `K .remainderNormalized`.  `Route8PiecesClassifiedStatement` follows.
- **[111] (key 160 removed).**  `[111]` is a definition node:
  `𝒳_A := route8SurvivorComponents`, `D_A := route8Deficit`
  (`def:typeA-large-budget-deficit`).  Its "carrying `D_A(𝒳_A)`" is the `[113]`
  inequality, decided at `[113]`.  The former key published a tautology of the
  filter and is deleted with its row and contract.
- **(b) of `def:typeA-trace-basin` (tex 10744-10775).**  A response quotient
  (`ResponseQuotient`) keeps, identifies or forgets each declared entry:
  identification is an equivalence on the entry's readings (which placed
  entries coincide and which are incident on its declared support); forgetting
  is the total identification.  A realization carries kept entries exactly and
  identified entries up to the quotient's identification.  Target-completeness
  is asked only against outside contexts compatible with the boundary profile
  (`ProfileCompatible`: glued to `\rho_u(B_u)`, every label keeps degree `≥ δ`).
- **[106] global scope (key 101).**  The smaller representative is the
  canonical delocalization's own closed representative
  (`Classical.choose (delocalization.2.closedRepresentative covers)`), not a
  free graph.
- **[102] → [89].**  The per-peel clause of `K .typeAExitFourFiniteDescent`
  was a definitional tautology of `canonicalPeelStep` and is removed; the
  retest is asked on the ledger at the terminal sets (key 2000).
- **514/515 (`def:typeA-recorded-window-shadow-hit`, tex 16229).**  Stated at
  G's recorded corridor `canonicalRecordedCorridor` of the two units, not at
  every `P`-avoiding path.
- **[160]/[56] rate test (keys 264/265).**  The decision reads the arm's
  density fact (`K .netDeficiencyCap` on the `[24]` arm, `K .denseDeficiencyBelow`
  on the `[56]` arm) as its predecessor.
- **[186] (key 506).**  The unused `K .route8DemandLedger` requirement is removed.
- **[121]--[122].**  The budget fact carries `1 ≤ δ` read from
  `K .cubicBaseline` (`Route8PrivateCarrierBudgetStatement`); the
  `Incompatible` closure reads no presentation law.
- **[89]/[93] (keys 54, 57).**  The saturated receiver and the visible-entry
  receiver are pinned: `∃ w, canonicalSaturatedReceiverAt X₀ = some w ∧ …` and
  `∃ w, canonicalVisibleReceiverAt X₀ = some w ∧ …`.
- **Not changed: the `\tilde{\mathcal X}` handoff filter
  (`SeparatorHandoffAt`, audit item 8).**  Restricting it to saturated
  receivers and eligible loads at `∅` (exit (7) of the unpeeled state) on the
  route-8 side alone breaks `lem:typeA-unified-deficit`'s partition in Lean:
  the Type B sublinear ledger's handoff class (`handoffChar`, TB scope) and the
  extracted-core census (unsaturated receivers of deleted regions) use the same
  predicate, so a piece with a separator only at an unsaturated receiver would
  lie in both the unified class and the handoff class.  The restriction has to
  be made jointly with the Type B group.

## [176] on an empty eligible family: flagged to the cold owner (fix pass TB, #14)

- **Status (closure of `[173]`'s no-arm).** The absorbed-configuration
  residual `[174]` is closed at `[173]` against `K .route8Rate` (see "Closed
  from G's facts", `[173]`/`[174]`), and `Assembly/Absorbed/*` is removed; the
  absorbed-lane wiring described here is no longer run.  The graph-level
  statements and contracts are kept.

- **Paper.** [175] "selected corridor meets a high-degree vertex?"; no →
  [176] "graph-realized (F5) configuration: closed by [154]--[157],
  [165]--[168]"; yes → [177].  `lem:exact-collision-test` (tex 7883-7902):
  on [174] "the residual carries linearly many cold windows, and it lies on the
  bounded arm of node [153] … its cold mass was charged as the
  configuration-extraction loss"; `lem:absorbed-germ-fan-data` restores that
  loss half-edge by half-edge.  The paper has no case with no selected
  corridor.
- **Lean.** On `K .coldNoPositiveGerm` (routed candidates empty) and
  `K .typeBAbsorbedHalfEdgeAbsent` (no eligible half-edge outside the
  candidates), the eligible family `ColdEligibleHalfEdge` is empty
  (`K .absorbedGermSplit`: every eligible `ε` is a candidate or has its first
  high centre).  [176]'s rows `[154]`--`[157]` run on it
  (`nearCubicColdTable`) and the arm returns the `[187]` cold outcome
  `K .coldBranchClosed`, as [176]'s G2 arm does.
- **Completeness check so far (path root → [173] → [174] → [175]).**

  | Paper object | Lean object / key |
  |---|---|
  | `P₀`, hot/cold windows, ambient-cubic windows | `canonicalWindowPacking`, `canonicalHotWindows`, `canonicalColdWindows`, `AmbientCubicWindow` (`Statements/Spine.lean`) |
  | selected branch-excess half-edges `𝒜_br` (corridor and cross-window) | `ColdSelectedHalfEdge`, `ColdEligibleHalfEdge`, `ColdGermOccurrence = Eligible ⊕ CrossWindow` (`Statements/Spine.lean:987`, `:1007`, `:1056`) |
  | per-window excess `9`, `|𝒜_br| = Σ (interior stubs − 2)` | `coldInteriorBranchExcess` (`Statements/Spine.lean:839`), `card_allSelectedStubs` (`ColdGermFamily.lean:879`) |
  | corridors, first failures (F1)--(F5), routing | `K .coldReturnCorridors`, `K .coldCorridorState`, `K .coldFailureRouting`, … (`Assembly/Absorbed/Prerequisites.lean`) |
  | candidates, extraction, loss `≤ (δ+1)·B·σ(G)` | `K .coldGermCandidates` (`ColdGermFamilyWitness`, `Statements/Spine.lean:1800-1855`) |
  | [153] linear/bounded arm | `K .coldMassLinear` / `K .coldMassBounded` (`Statements/Spine.lean:963`, `:974`) — **not read on the [174] path**; whether it is on the ledger depends on the branch reaching [57] (`Assembly/NearCubic/Spine.lean`) |
  | [173]/[174] exact collision | `K .exactCollisionFails`, `K .absorbedConfigurationResidual` (`Statements/Spine.lean:3660-3700`) |
  | [175] split | `K .absorbedGermSplit`, `K .coldPositiveGerm` / `K .coldNoPositiveGerm`, `K .absorbedGermFanData`, `K .typeBAbsorbedHalfEdge(Absent)`, `K .typeBAbsorbedCharge` |

- **What the check shows, about G.** On this arm the routed candidates are
  empty and every eligible half-edge is a candidate, so no eligible half-edge
  exists; the cross-window occurrences that are not candidates are charged to
  the loss (`ColdGermFamilyWitness`) and are **not** in [175]'s split, which
  quantifies over eligible half-edges only.  The [174] inequality
  `n + s·σ_R ≤ A·(|𝒫_hot| + C) + s·σ_W` does not force an eligible half-edge
  (hot windows, non-ambient-cubic cold windows and `σ_W` can carry it), and
  the paper's reading "the cold mass is the configuration-extraction loss" is
  the [153] bounded-arm fact, which the [174] path does not read.  So the
  decision needs objects of the cold family that are not yet read on this path:
  the [153] arm at G on the [174] path, and [175]'s treatment of cross-window
  occurrences.  These belong to the cold/Spine owner (hs-wt-F5); the Type B
  pass leaves the arm unchanged and does not claim it closed, dead or a paper
  error.

## [153]/[154]--[157]/[163]/[176]/[187]: the cold chain at G's objects (fix2-SC, 2026-09-27)

*Family F5.  No deviation from the paper; recorded so that the ledger shape can
be checked against the tex.*

- **[30] the second representative `E` is G's.**  `def:cold-bounded-germ` /
  `lem:cold-corridor-first-failure` (tex 7147-7152, 7296): "the canonical
  representative determined by the repeated cold corridor state", "with the same
  retained cut-state".  `ColdCorridorStateStatement` now pins the second
  representative of every exchange germ (outside corridors and cross-window
  exchanges) to `Graph.ColdCorridor.rowRepresentative` of the germ's own support
  (`BoundedGerm.HasCanonicalSecond`): the `Precedes`-least canonical piece with
  the support piece's boundary-degree profile whose completions keep the
  baseline.  G1/G2, the trichotomy `[32]`--`[34]`, `[71]`, `[406]` and the table
  are evaluated at that `E`.
- **[30] the cut state is `ρ^ex_{T(J)}(J)`'s retained part** (tex 7187-7197).
  `coldCutStatePresentation`: `T(J)` is the entry interface (foot and the window
  of `ε`) and the head interface (the head and the window it meets:
  `Corridor.headInterfaceVertex`, the successor window only at the terminal
  segment); the two active half-edges are `ε` and the dart by which the corridor
  leaves the head (`Corridor.headHalfEdge`); the offsets are read at the entry
  window and at the head interface (`coldWindowOffset`, cold windows only, `0`
  when no cold window is met); every declared coordinate is read through its
  clause (`coldClausePositions`: a (D1) boundary-degree entry is supported at
  its labelled boundary vertex and reads its G-degree; the other generating
  kinds read their declared positions' embedded incidence datum -- the paper's
  "value in the embedded support", tex 5902).  The head-side data move along
  the corridor.
- **[154] G1/G2, [175], [153] mass, [145]/[147] split decisions read their
  predecessor** through `ExactLedger.get` (`coldGermFamilyPositive`,
  `coldGermNoneRealizing`, `absorbedGermSplit`, `coldStubExcess`,
  `hotColdPartition`).
- **[156] `K .coldGermRouted` (idx 71)** is stated at node `[153]`'s extracted
  family (`CanonicalActiveColdGerm`), like `[32]`--`[34]`.  Consequently
  **[187] `K .coldBranchClosed`** reads the length-changing patterns of that
  family (no germ of the family is shortening and silent), and G's table rows
  and short self-returns.
- **[157] the (F4) arm of the table is "enters a registry support"** (tex 7234):
  `ColdEntersHandoffRegistry` = the row support meets one of G's declared
  handoff supports.  It was "equals one", which left the handed-off arm nearly
  empty.  `[187]` uses the same predicate.
- **[34]** no longer publishes `¬ LengthChanging ↔ |E| = |Q|`, which holds by
  the definition of the increment (`BoundedGerm.not_lengthChanging_iff`).
- **`K .coldExchangeBound` (idx 177)** is `def:cold-corridor-first-failure`'s
  `M_cold` bound (tex 7200-7209, 7249-7252) at G's routed occurrence: it reads
  `[68]` and bounds every terminal retained corridor of G.  It was a statement
  over every corridor of every window set, true by definition and unread.  Node
  `[219]` does not consume it (its germs carry `M_cold` in `BoundedGerm.bounded`),
  so `[219]` no longer declares it.
- **[219] publishes the user-approved exact (F4) count** (tex 7318-7329):
  `#{ε : first failure (F4)} ≤ corridorLoss`, instantiated at G from the
  published witness (`coldF4_card_le_corridorLoss`).
- **[406] is read on the G2-silent arm** (`K .coldGermNoneDistinguishing`,
  `[605]`, now in its statement and read by the row): the configuration is a
  germ of G's silent extracted family.
- **[176] on the absorbed residual does not reuse [162].**  The paper states
  `[162]` only "on the dense-packing residual" (`lem:dense-cold-pass`,
  tex 7674-7694), and `def:neutral-equal-length-germ` is "on the dense residual,
  a terminal (F5) configuration" (tex 7700).  `lem:absorbed-germ-fan-data` (i)
  (tex 7917-7923) closes the absorbed branch's (F5) configurations -- terminal
  or repeated-state -- by the same lemmas.  The absorbed prerequisites no longer
  run `[162]`; node `[176]` publishes the silent family's neutral configuration
  without terminality (`K .coldAbsorbedNeutralConfiguration`, idx 2700,
  `NeutralConfigurationStatement`), and the symmetry split `[163]` reads it
  (`absorbedNeutralSymmetryDichotomy`).  Paper gap (registered, no sorry):
  the paper cites `lem:neutral-germ-symmetry` at `[176]`, whose definition
  assumes the dense residual's terminal configuration; the Lean runs the same
  split at the silent family's (F5) configuration, as `[176]` asserts, and
  does not supply the terminality the absorbed branch never had.
- **[210] `lem:target-rank-circuit`** is stated at node `[31]`'s surviving family
  `𝓘₀` (`canonicalSurvivingFamily?`), its only use.
- **[18]** reads the label census from the entry presentation fact
  (`K .cubicBaseline`, fifth conjunct of `CubicBaselineStatement`), and the six
  cold rows that need `5 ≤ order` / `3 ≤ order` derive it from that census
  (`five_le_windowOrder_of_labelCount`).

<a id="paper-errors"></a>

## Paper errors

Only claims of the paper shown false at G, with the Lean evidence.  None at
present: every entry formerly filed here is under "Paper findings (no sorry)",
closed by a user-approved repair, or carried by a returned residual (see
"Returned residuals").  The anchor `#paper-errors` is kept for the Lean
references.

## Paper findings (no sorry)

Each entry is a place where the paper is internally inconsistent, routes a
case differently from its diagram, or states a step that is empty, trivial or
unargued at G without being false there.  The Lean follows the paper's main
theorem and argument path; no `sorry` is involved.

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

### [82] `c ≤ 1` without B2: "`N₀(X) ≥ 0`" (tex 1020, `lem:typeB-exclusion` tex 14349, `rem:typeB-status`)
- **Paper claim.** Node [82]: "yes: certificate-closed or B2-paid;
  `N₀(X) ≥ 0` outside route 8", on the [81] yes arm "`c ≤ 1`, or `c ≥ 2` with
  B2".
- **Completeness check (every object the paper builds on G on the path
  [65] → [67] → [68]no → [78] → [79] → [80]yes → [81]yes → [82]).**

  | Paper object (tex) | Lean canonical object / key (file:line) |
  |---|---|
  | assigned support `X = (Y_X, H_X)`, `def:typeB-assigned-ledger` 12909 | `TypeBLaneMember` (`Statements/TypeBLanes.lean:79`), canonical supports (`Statements/CanonicalTypeB.lean`), `K .typeBFanEntry` |
  | `N₀(X₀) < 0`, [61] | `TypeBCanonicalLane` (`Contracts/TypeB/Support.lean:108`), `K .negativeSupport` |
  | normal form, [67] | `K .highCentreNormalForm` (`Statements/TypeB.lean:853`) |
  | degree split, [68]/[78] | `K .typeBFanDegreeFourCentres` (`Statements/TypeBLanes.lean:201`) |
  | degree-4 profile `c`, `D_B`, [79] | `K .typeBFanDegreeFourProfile` (`Statements/TypeBLanes.lean:218`) |
  | fan-safe graph, cap, [70] | `K .fanCertificateCap` (`Statements/TypeBLanes.lean:330`) |
  | certificate labelling `S_h`, [80] | `canonicalFanCertificateLabelling` (`Statements/TypeB.lean:201`), `K .fanCertificateMarked` (`TypeBLanes.lean:342`) |
  | direct fan-window cycles excluded | `K .typeBDirectCycleFree` (`TypeBLanes.lean:361`) |
  | B1 hybrid entries, `lem:typeB-hybrid-B1` | `K .typeBHybridEntry` (`TypeBLanes.lean:373`) |
  | fan envelope `E_h` | `typeBFanEnvelope` = `TypeBRefinedSupport.fanEnvelope` (`Statements/TypeB.lean:178`, `TypeBCanonicalB2.lean:188`) |
  | candidate entries, `def:typeB-candidate-ledger`; ledger items, reserve, `def:typeB-ledger-carriers` | `CandidateData.IsCandidate` (`TypeBCanonicalB2.lean:331`), `ordinaryDeficiencyReserve` (`OrdinaryDeficiencyReserve.lean:245`) |
  | B2, `def:typeB-bridge-statements` | `TypeBB2At` (`Statements/TypeB.lean:232`), `DisjointChoice` (`TypeBCanonicalB2.lean:502`) |
  | B2 failure → minimal obstruction, `lem:typeB-bridge-to-overlap` | `not_hasDisjointChoice_iff_overlapObstruction` (`Contracts/TypeB/Support.lean:389`), `canonicalOverlapObstruction` (`Statements/TypeB.lean:242`) |
  | [81] test | `K .typeBDegreeFourLedger` / `K .typeBDegreeFourOverlap` (`TypeBLanes.lean:412`, `:425`) |
  | Step 1 of `lem:typeB-exclusion` | left disjunct of `K .typeBDegreeFourClosed` (`TypeBLanes.lean:460`) |
  | Step 2: B2 ledger, post-ledger hygiene, Type A discharge | `TypeBB2LedgerAt` (`TypeBLanes.lean:440`), `disjointLedgerCoreClosure` (`Contracts/TypeB/Ledger.lean:24`) |
  | `N₀(X)`, (B-ledger) | `typeBScaledNetCharge` (`Statements/TypeB.lean:280`), `augmentedLedgerWith_add_card` (`TypeBEnvelopeCharge.lean:1135`), `remainingCore_le_scaledNetCharge` (`:1167`) |
  | bridge-residual bound, `lem:typeB-bridge-deficit-bound` | `TypeBBridgeDeficitBoundAt` (`Statements/TypeB.lean:269`) |

  Every object is on G's ledger or is a canonical object of G at [82]; none is
  missing.
- **The step the paper does not give, about G.** In the case `c ≤ 1` at every
  assigned centre of G's Type B support `X` and B2 failing at `X` (G's
  canonical `[71]` labelling present at every centre, and no choice of
  candidate entries on the assigned fan envelopes of `X` with disjoint ledger
  supports; then G's canonical minimal overlap obstruction exists), the claim
  "`N₀(X) ≥ 0` outside route 8" needs Step 2 of `lem:typeB-exclusion`:
  pairwise disjoint nonnegative entries for the different centres.  Step 1 is
  "a local calculation at a single fan center.  It does not identify disjoint
  paying ledger items for different centers.  The required disjointness is
  exactly the refined support ledger B2" (tex 14435-14437); `rem:typeB-status`
  repeats it, and `prop:typeB-global-local-bridge` sends a remaining
  obstruction to the fan mass.  No construction of the paper on this path
  supplies that disjointness at `c ≤ 1`, and none of the objects above
  implies it.
- **What the Lean does.** No `sorry`, no repair and no claim that the case is
  live or dead: at [85] (`typeBDegreeFourExclusionResidualRow`) the case is by
  definition a Type B bridge residual (`def:typeB-bridge-statements` (ii):
  B1 supplied, B2's disjoint-incidence part fails), and the paper's own
  `lem:typeB-bridge-deficit-bound` charges it to the assigned surplus
  (`TypeBBridgeDeficitBoundAt`), which is [84]'s label "certificate failures
  and B2 failures charged to assigned surplus".  The B2-paid case keeps its
  whole deficit in the remaining core (`K .typeBDegreeFourClosed`, right
  disjunct).  `K .typeBExcluded` is [74]'s key and is not used on this arm.

### [92] after peeling: the unsaturated charge does not close once a load is peeled (tex 1095, 11753, 11785)

*Final fix pass TA; refiled by fix2-TR (no sorry: a diagram inconsistency).*

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

### [113] diagram box vs `rem:why-unified`: the large-budget deficit is tested, not asserted

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
  The positive arm continues to `[114]`--`[124]` and closes on every arm
  (`[116]`, `[122]`, and `[118]` at `[124]`); the
  negative arm enters the unified target-defect/route-8 ledger
  (`selectedTypeBRoute8Continuation`, `Assembly/RouteEight/TypeBContinuation.lean`)
  and reaches `[123]`, `[181]`, `[183]`--`[186]`.
  Caller: `selectedRouteEightResidual` (`Assembly/RouteEight/Residual.lean`).
- **Why this is a paper finding.**  The paper itself (`rem:why-unified`)
  retracts the box's deduction and replaces it by the unified procedure of
  `thm:large-budget-route8-only`, whose stage test is this inequality; the
  Lean follows the paper's own correction: no arm is assumed, the positive arm
  is the paper's own `[113]` fact, and the negative arm is sent to the unified
  ledger the paper introduces for exactly this mass.  Kernel-checked.

### [348] paper inconsistency: `lem:typeA-unified-carriers` (tex 15362) vs `thm:main` (tex 369-372)

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
  `K .route8QuotientResidual` is returned as `Route8QuotientOutcome` (see
  "Returned residuals", [#residual-187-route-8-quotient](#residual-187-route-8-quotient))
  through `SelectedRouteEightBoundary` to the `OtherReturnedOutcome` disjunct of
  `SelectedLedgerBoundaryResult` (`Assembly/Final.lean`).  The
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
- **Realization class.**  A response quotient keeps, identifies or
  forgets each declared entry (`ResponseQuotient`); a realization
  (`QuotientRealization`) is a boundaried state in the basin's
  boundary-degree fibre carrying kept entries exactly and identified entries up
  to the identification, through one label-fixing placement; target-completeness
  is asked against profile-compatible contexts (`ProfileCompatible`).

### [170]/[172a] scale range: the absent-completion failure at the smallest scales (tex 6907-6917, 7985-7987, 8030-8038, 8332-8365, 8418-8420)

- **Question.** At the smallest scale indices no completion support exists,
  so the absent state survives at every member, `S_{d,q,c} = A_{d,q,c}`, and
  the cleared ratio `W_{a,b}|S| ≤ F_{a,b}|A|` fails at every blocked member
  (every registered row has `F_{a,b} < W_{a,b}`).  Then the negative arm of
  `[170]` is always taken and fact 71 (`BlockedBarrierFailureStatement`)
  follows from fact 70 (`BlockedClassMemberStatement`).  Does the paper range
  over those scales?
- **Lean.** `blockedCoordinate` ranges over the scale indices
  `j < separatedScaleCount n = ⌊log₂ n⌋` at scale `2^j`, `j ≥ 0`, with every
  registered row `(a,b)`, `a,b ≥ 1`, `a+b ≤ 14`.  `separatedScaleCount := Nat.log2`
  is fixed in `Problem.lean` and is the same `L` as `windowPackageBits`
  (`[158]`/`[159]` and the `[171]` closure).
- **Paper.** `lem:p13-window-package` (tex 6907-6917) uses
  "`⌊log₂ n⌋ − O(1)` separated dyadic scales", with the `O(1)` loss attributed
  to endpoint collisions with reserved boundary and tie-breaking choices, not
  to small scales; it names no minimum scale.  Every retained scale carries
  every barrier (tex 6887-6899, 6917; "one coordinate per barrier, separated
  scale, and packed window", tex 8418-8420; `def:window-realization-test`
  counts `L` scales with the full `W_*/F_*`, tex 7619-7630).  The per-row form
  "`2^j ≥ a+b+1`" is not in the paper.  The only lower anchor is the target
  itself (`Mers = {2^j − 1 : j ≥ 2}`, tex 1965; blocked at scale `2^j` means
  no `C_{2^j}` through the window, tex 7985-7987), which would drop `j = 0, 1`
  but not the rows `a + b ≥ 2^j` at `j = 2, 3`.  The paper itself records the
  phenomenon at `[172a]` (tex 8034-8038): "If every graph in the fibre has no
  completion, the absent-completion state survives and `S = A`.  Whenever
  `F < W`, every nonempty such fibre fails the ratio without supplying an
  overlap."
- **Verdict.** The paper's scale family includes scales at which no
  completion exists for some barrier: whichever `O(1)` scales are dropped, the
  paper does not drop every scale `2^j ≤ 14` (`j ≤ 3`), and at any such scale
  the rows with `a + b ≥ 2^j` have no completion.  The Lean range is not wider
  than the paper's in a way a restriction could repair: dropping `j = 0, 1`
  (the only drop the tex supports) would change `L` (fixed in `Problem.lean`,
  shared with `[158]`/`[159]`/`[171]`) and would leave the first failure at
  `j = 2`, rows `a + b ≥ 4`.  The statements of `[170]`, `[171]` and `[172a]`
  are unchanged.  `[172a]` is the paper's own open leaf; its forced negative
  arm is the paper's absent-completion remark, realized at the first exposure
  coordinate.
- **No Lean improvement available here (user ruling on Lean improvements).**
  Neither re-derivation closes or tightens a path.  Restricting to `j ≥ 2`
  changes `L` (fixed in `Problem.lean`) and leaves the forced failure at
  `j = 2`.  `fact71_of_fact70` closes nothing: it shows that the positive arm
  `[170]` → `[171]` is never taken, so every trivial-neutral path reaches
  `[172a]`.  The derived description of `[172a]` (the retained coordinate
  has scale index 0 and `S = A`) needs `F_{a,b} < W_{a,b}` and `a, b ≥ 1` at
  every registered row.  Those hold only at the concrete certificate
  (`native_decide` at `spineData`) and are not a published presentation law.
  Publishing them needs a new `Data` field populated in `Problem.lean`, so it
  is not implemented.
- **Lean evidence** (scratch analyses, not imported):
  `analysis-172a/RankZero.lean` — `barrierState_scaleOne_none` (scale `2^0`),
  `surviving_eq_apriori` (`S = A` at scale index 0),
  `relative_fails_scaleZero`, `retained_scale_zero` (the retained coordinate
  of fact 71 has scale index 0), `fact71_of_fact70` at the registered data
  (with `table_strict`: `F_{a,b} < W_{a,b}` for all 91 rows, `native_decide`);
  `analysis-172a/ScaleTwo.lean` — `barrierState_scaleTwo_none` (scale `2^1`);
  `c5/ScaleLeLegs.lean` — `barrierState_none_of_scale_le_legs`: no completion
  support whenever `2^j ≤ a + b` (legs `≥ 1`), covering the rows `a+b ≥ 4` at
  `2^2` and `a+b ≥ 8` at `2^3`.

## Closed from G's facts

Branches the paper keeps that are refuted at G by facts already on G's
ledger at the node, and closed there with `closeIncompatible`.  They are not
paper errors: nothing the paper claims is false; the branch is simply never
inhabited at G.

### [130] blocker (d) of `def:surplus-blockers` is empty at G: the determination quotient is admissible (tex 2897; tex 4673-4689; tex 5839, 5876-5883, 6018-6029, 9160-9180)

*Group SP (Surplus / Pair / [144]).*

- **Paper claim.** (d) is "a boundary-degree-profile coordinate which prevents
  a quotient or replacement from staying in a single fibre"; in
  `lem:sparse-pair-dependence-exit` it is produced when "the determination
  attempts to identify states with different boundary degree profiles"
  (tex 4686-4689).
- **Faithful Lean statement.** `SparsePairDEProfileObstructionAt`: the
  determination's quotient identifies `r_π` with a determiner `b`, and the two
  readings on G's piece at the determination support lie in different fibres.
  The determination (`SparsePairDetermination`) is the paper's: its quotient
  comes from `lem:target-rank-circuit`, which extracts it from a *functional
  admissible* rank quotient (tex 9160-9180, `def:curvature-target-dependence`
  (b)), and an admissible quotient is target-complete
  (`def:admissible-rank-quotient`, tex 6018-6029): every identification
  preserves the boundary-degree profile (`def:target-complete-quotient` (a),
  tex 5876-5883; `def:boundary-degree-profile`, tex 5839: "two boundaried
  states with different boundary degree profiles are never eligible to be
  identified").  In the Lean this is `SparsePairExactValuation`.
- **Why it is closed.** The determination's own quotient cannot identify two
  states in different fibres, which is the only way (d) arises.  Lean
  evidence: `not_sparsePairDEProfileObstructionAt`
  (`Graph/SparseEntropySandwich.lean`), and at G
  `not_pairProfileObstruction_of_fibres`
  (`Contracts/SurplusPair/PairSchedule.lean`).
- **Closed at the node, from G's ledger.** On [130]'s blocked arm,
  `pairDegreeProfileFibresRow` publishes `lem:degree-profile-fibres` at G's
  pair family and G's canonical activation (`K .pairDegreeProfileFibres`,
  idx 2902, read from `K .dependentPairFamily`).  The exact decision
  `pairProfileObstructionDichotomy` then splits clause (d) at that activation
  (`K .pairProfileObstruction` 2903 / `K .pairNoProfileObstruction` 2904), and
  `strictSurplusDependent` closes its positive arm by `closeIncompatible …
  (K .pairDegreeProfileFibres) (K .pairProfileObstruction)`.
- **Representation.** No `sorry`.  The clause is kept as the paper states it;
  [130]'s blocked arm is driven by clauses (a)--(c) and (f).

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
- **Why it is closed.** Each of the three events is a named sparse surplus exit
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
- **Closed at the node, from G's ledger.** On [130]'s blocked arm the exact
  decision `pairResponseObstructionDichotomy` (`Strategy/SurplusRows.lean`)
  reads `K .dependentPairFamily`, which pins G's canonical activation, and
  splits "some scheduled pair has a type-(e) obstruction at that activation"
  (`K .pairResponseObstruction`, idx 2900) against its literal negation
  (`K .pairNoResponseObstruction`, idx 2901).  The (e) arm is closed in
  `Assembly.Internal.strictSurplusDependent` by
  `closeIncompatible … (K .sparseSurplusSurvivor) (K .pairResponseObstruction)`
  (`instIncompatibleSparseSurplusSurvivorPairResponseObstruction`, contract
  `not_pairResponseObstruction_of_survivor`).  [132] then runs on the
  no-(e) ledger.
- **Representation.** No `sorry` (nothing unprovable is claimed).  The clause
  is kept as the paper states it.  Its arm is closed at [130] against G's
  survivor.  No other predicate replaces it.

### [144] the capped arm is closed by the audited pattern (tex 1238-1252, 5653-5690, 5805-5812)

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
  audit, in the paper's order (d2ded0e has the same order).  The paper sends
  the capped arm to [138].
- **Why it is closed.** The audit's own output, `K .homogeneousBottleneckPattern`,
  is a role-homogeneous same-token pattern of size at least `L_geom` in the
  role fibre of G's overloading token at that same ledger; the caps say no
  token carries one.  So on the paper's own path the caps test has only its
  failing arm (and `D_all > 0` at [137] already forces the audits to find the
  pattern).  The paper's capped route to [138] is the [137] no-arm, not a
  [144] arm.
- **Evidence.** `Contracts.SurplusPair.not_homogeneousCapsHold_of_pattern`
  (`Graph/Contracts/SurplusPair/OverloadClass.lean`, kernel-checked):
  `HomogeneousBottleneckPatternSchema → HomogeneousCapsHoldStatement → False`.
- **Closed at the node, from G's ledger.** The decision
  `homogeneousBottleneckDichotomy` is kept in the paper's order.  Its caps arm
  is closed in `selectedBottleneckDischarge` (`Assembly/Surplus/Local.lean`) by
  `closeIncompatible … (K .homogeneousBottleneckPattern) (K .homogeneousCapsHold)`
  (`instIncompatibleHomogeneousBottleneckPatternCapsHold`,
  `Strategy/HomogeneousBottleneckRows/FibrePressure.lean`).  That is the
  decision's own predecessor fact about G's overloading token, refuting the
  caps at the same canonical certified ledger.  The paper's `[138]` route
  from this arm (`homogeneousCapsCloseRow`) is no longer run.  The row module
  is kept, unwired.
- **Representation.** No `sorry`.  [144a] is unchanged.

### [23](i)/[37]: the target-defective terminal is closed by [12] at G (tex 9220, 9388)

- **Branch.** Case (i) of `lem:curvature-dependence-routing` (node `[37]`,
  "a target-defective quotient"), the terminal of the decision `[36]`,
  `[23]` `ContextDefectStatement`.
- **Why it is closed.** The certificate's quotient is admissible, so `[12]`
  (`K .targetCompleteContextUniversality`, on G's ledger at the entry) refutes
  a separating context for any pair it identifies
  (`Contracts.Spine.contextDefect_false_of_contextUniversality`).
- **Closed at the node.** `Assembly/NearCubic/Spine.lean`:
  `closeIncompatible defectHistory (K .targetCompleteContextUniversality)
  (K .contextDefect)`.  The definitional character of `[11]`/`[12]` stays
  under Paper findings (no sorry) ("[11], [12], [36]/[37]").

### [118]/[124]: the `[113]`-yes two-support entry of `𝒳_A` is the terminal obstruction (tex 12636-12668, 12670-12696, 12758-12785, 17124-17127)

- **Branch.** `[113]` yes (`K .route8LargeBudgetDeficit` on `𝒳_A`), `[115]`
  no (`K .route8NoSmallCoreEntry`), `[117]` yes (`K .route8TwoCarrierEntry`):
  the former factor choice `Route8DeficitBlock_holds` of the three route-8
  products ([186], [187] Type B sublinear, [187] [348]), 120 paths each.
- **Faithfulness.** The paper puts every fact used here on this path.
  `prop:typeA-route8-closure-from-nogo` (tex 12758-12785) takes a route-8
  collection carrying the large-budget deficit (here `[113]` yes), obtains the
  two-support entry by `prop:typeA-route8-carrier-reduction` (here `[117]`
  yes, the canonical `ι₂`), states that it is a true route-8 residual entry
  (T2) "since the collection survives only through route 8", that
  `α_𝒳(ξ) ≥ 2` (T3) by `lem:typeA-one-terminal-collapse` (here `[115]` no),
  and that the declared deletion witnesses (T5) exist.
  `thm:large-budget-route8-only` (tex 17124-17127) routes a route-8
  two-support entry to exactly this proposition.  The Lean statements match
  (T2)/(T5) at `ι₂`: `Route8TrueTwoCarrierEntryStatement` is "no exit-(4)
  witness at `ι₂`", derived from `K .route8TrueResidual` (the
  `TargetCompleteMinimal`/no-exit-(4) clause of (R1)--(R4)) and the
  minimum-degree baseline (`route8TrueTwoCarrierEntry`,
  `Contracts/RouteEight/TwoCarrier.lean`); `Route8CarrierDeletionWitnesses` is
  (T5) at `ι₂` (`route8CarrierDeletionWitnesses`).  Neither is stronger than
  the paper's: both are proved from G's facts at the node.
- **Why it is closed.** `thm:typeA-two-carrier-nogo` (tex 12670-12696):
  `route8SurvivorTwoCarrierExit` (`Contracts/RouteEight/Terminal.lean`) turns
  the deletion witnesses, the selected basin of the true residual and
  `α ≥ 2` into the canonical exit-(4) witness at `ι₂`
  (`lem:typeA-two-carrier-deletion-canonical`,
  `lem:typeA-carrier-deletion-exit`); `route8TrueTwoCarrierEntry_false`
  refutes it against (T2).
- **Closed at the node.** `Assembly/RouteEight/Residual.lean`,
  `selectedRouteEightCollection` (now `: False`), arm `.left twoCarrier`:
  `route8TrueTwoCarrierEntryRow`, `route8CarrierDeletionWitnessesRow`, then
  `route8TwoCarrierExitRow.runAndCloseIncompatible witnesses
  (K .route8TrueTwoCarrierEntry) (K .route8TwoCarrierExit)` with `elimClosed`
  (instance `instIncompatibleRoute8TrueTwoCarrierEntryTwoCarrierExit`).
  `Route8DeficitBlock_holds` and the `Route8Deficit` disjunction are removed
  from `Assembly/Residuals/Route8Blocks.lean`; `TypeAArm` carries
  `Route8DeficitBlock_fails` directly.

### [173]/[174] the absorbed-configuration residual is empty at G: the failed exact collision against the private-carrier rate (tex 915-940, 1325, 7648-7670, 7883-7916; tex 1136-1150)

*Family F5 (Spine / Cold / NearCubic).*

- **Tag.** On the dense double-yes arm (`[160]` → `[161]`) the paper's own dead
  branch.  On the spine (`[24]`) and `[147]` arms, **Lean improvement**: the
  paper routes the path through both facts but reads the rate asymptotically
  (`τ_win < 3/13`, tex 1138) and keeps `[174]`--`[177]` live; the exact readings
  on G's ledger close it.
- **Paper claim.** Part V (tex 915-940) sends the no-edge of `[173]`
  ("exact collision test holds?", `lem:exact-collision-test`, tex 7883) to the
  absorbed-configuration residual `[174]`, then `[175]`--`[177]`, and `[177]`
  into Type B `[65]` → `[77]` → Part IX, whose no-two-support branch consumes
  the private-carrier rate `τ < 3/13` at `[120]`--`[122]` (tex 1136-1138).
- **Where the two facts sit on the paper's paths.** Every path into `[57]`
  carries the rate before `[173]`: on the dense residual `[160]` decides
  `τ(θ) < 1/4` and then `τ(θ) < 3/13`, and only the double-yes arm enters
  `[161]` → `[25]` → … → `[57]` (tex 1325, `lem:dense-deficiency-routing`,
  tex 7648-7670: "only the double-yes arm enters [161]"); on the spine the
  rate is the paper's `τ_win < 3/13` of `[122]`, which the Lean decides
  exactly at the entry of the route-8 continuation (`nearCubicRouteEightEntry`,
  its failure retained at `[187]`); on the `[147]` arm (`θ < 1/78`) it is
  derived (`route8RateFromColdBelowRow`).  The absorbed lane's own
  continuation reaches `[120]` (`[177]` → `[65]` → `[77]`), where the paper
  consumes the same rate.  So both facts are on the paper's paths through
  `[173]`'s no-edge: no wiring defect.
- **Why it is closed.** `K .exactCollisionFails` is `N₀(R₀) ≥ 0` at the
  remainder `R₀` of the fixed maximum packing, `|R₀| + s·σ(R₀) ≤ s·def⁺(R₀)`
  (`τ ≥ 1/4`); `K .route8Rate` is the census rate
  `(δs+1)·e(R₀,W) + δ·slack < δ·|R₀|` (`τ < 3/13`); node `[29]`'s boundary
  demand gives `def⁺(R₀) ≤ e(R₀,W)`.  Then
  `δ|R₀| ≤ δs·def⁺(R₀) ≤ δs·e(R₀,W) ≤ (δs+1)·e(R₀,W) < δ|R₀|`, i.e.
  `3|R₀| ≤ 12·def⁺ ≤ 12·e < 13·e + 3·slack < 3|R₀|`.  On the paper's dense
  double-yes arm this is the paper's own dead branch outright (`[160]`'s first
  test is `[56]`'s collision in exact form); on the other arms the paper reads
  both rates asymptotically, and the exact readings on G's ledger are
  incompatible.
- **Statement dependence.** The closure uses the Lean form of `[173]`'s no-arm,
  `N₀(R₀) ≥ 0` (`def⁺(R₀) − σ(R₀) ≥ |R₀|/4`, the collision of `[56]` itself,
  see "[57] and [173]" above).  The paper's displayed form of the failure,
  `15p₁₃ + σ_W − σ_R ≥ |R|/4` (tex 7885-7888), is implied by it through the stub
  supply of `[29]` but does not by itself contradict the rate.
- **Evidence.** `Contracts.RouteEight.exactCollisionFails_route8Rate_false`
  (`Graph/Contracts/RouteEight/CollisionRate.lean`, kernel-checked):
  `BoundaryDemandStatement → Route8RateStatement → ExactCollisionFailsStatement → False`,
  over any `Parameters` and object.
- **Closed at the node, from G's ledger.** `selectedNetChargeContinuation`
  (`Assembly/NetCharge/Continuation.lean`): the `.right` arm of
  `exactCollisionDichotomy` is
  `closeIncompatible failsHistory (K .exactCollisionFails) (K .route8Rate)`
  with `.elimClosed`
  (`instIncompatibleExactCollisionFailsRoute8Rate`,
  `Strategy/SpineRows/ExactCollisionDichotomy.lean`).  The boundary demand is
  read at the residual's own baseline, `boundaryDemand_of_baseline` of the
  input's `baseline`, which is exactly the term `boundaryDemandRow` publishes
  as `K .boundaryDemand`.  `K .route8Rate` is a `FactKeys.Has` requirement of
  `selectedNetChargeContinuation`, so every caller carries it.
- **Paths removed.** `Assembly/Absorbed/*` (`selectedAbsorbedGermPrerequisites`,
  `selectedAbsorbedGermResidual`, `selectedAbsorbedFanData`,
  `selectedAbsorbedFanChargeContinuation`, `SelectedAbsorbedGermBoundary`) is
  deleted; `SelectedNetChargeBoundary` is `SelectedRouteEightBoundary`.
  - `Route8JointBalanceOutcome_product` ([186]), `TypeBSublinearOutcome_product`
    and `Route8QuotientOutcome_product`: the continuation factor loses
    `AbsorbedLane` (12 arms: `NetChargeLaneBlock_absorbedGerm`,
    `AbsorbedGermBlock_positive` / `_none`, each × the 6 B-chain arms), 68 → 56
    arms, 1360 → 1120 paths each on the pre-`[124]` base (240 removed from
    each); merged with the `[124]` deficit-holds closure the continuation is
    62 → 50 arms and each product 1240 → 1000 paths (240 removed from each).
  - `ColdBranchClosedOutcome` ([187], local cold-terminal exclusion): the
    absorbed-germ product `ColdBranchClosedOutcome_product` (100 paths) and its
    blocks (`ColdBranchClosedAbsorbedCommon`, `E1`--`E4`, `W1`--`W5`,
    `X1`--`X5`) are removed; the 4 linear singletons remain.
  - `[153]`: the 20 absorbed-lane subtypes
    (`Node153ResidualOutcome_{denseAtOrAbove_coldBelow, denseAtOrAbove_bounded, denseRate, realized_coldBelow, realized_bounded}_absorbed_{high, lowNonrep, lowWedgeFree, lowWedge}`)
    are removed; the 3 linear subtypes remain.
  - The arm blocks `NetChargeLaneBlock_absorbedGerm`, `AbsorbedGermBlock_*`,
    `AbsorbedGerm`, `AbsorbedLane` (`Residuals/Route8Blocks.lean`) and the
    absorbed alternative of `BChainLane` with `NetChargeArms.absorbed`
    (`Residuals/ArmBlocks.lean`) are removed.
- **Representation.** No `sorry`.  The graph-level absorbed-lane contracts
  and rows (`Contracts/TypeB/Entry.lean`, `ColdCorridorRows/AbsorbedGerm*`) are
  kept; the rows `absorbedGermSplitRow` / `absorbedGermFanDataRow` still run on
  the `[153]` linear arms.

### [146] yes on [160]'s first complement: `θ < 1/78` forces `τ(θ) < 1/4` (tex 1325-1343, 6946-6962, 7648-7684, 7536-7538)

- **Paper path.** [158] no → [159] → [160] first test no (`τ(θ) ≥ 1/4`,
  `K .denseDeficiencyAtOrAbove`) → [162] "run [22]--[24] and [145]--[157] on
  the dense residual" (`lem:dense-cold-pass`, tex 7674-7684, explicitly
  including "the route-8 arm [146]/[147]") → [146] yes (`θ < 1/78`,
  `K .coldRoute8Below`).  The paper routes this path; it is not a Lean-only
  prefix.
- **Why it is closed.** `def:cold-window-ledger` (tex 6946-6962): `τ(θ) < 1/4`
  iff `θ < 1/73`, `τ(θ) < 3/13` iff `θ < 1/78`; so `θ < 1/78` forces
  `τ(θ) < 3/13 < 1/4` (the ledger table, tex 7536-7538, rows 1 and 3).  In
  the exact forms at G's canonical packing (`X = n − 13p`, `T = C_sp⌈√n⌉`):
  `195p + 109T < 3X` against `3X ≤ 180p + 12T`.
- **Evidence.** `Contracts.Spine.denseDeficiencyBelow_of_coldRoute8Below`
  (`Graph/Contracts/Spine/NetCharge.lean`, generic in the parameters):
  `ColdRoute8BelowStatement → DenseDeficiencyBelowStatement`.
- **Closed at the node, from G's ledger.** `nearCubicDensePassAtOrAbove`
  (`Assembly/NearCubic/Survivor/Unrealized.lean`), the `.left` arm of
  `coldRoute8Dichotomy` (where `[146]` publishes `K .coldRoute8Below`):
  `closeIncompatible belowHistory (K .denseDeficiencyAtOrAbove) (K .coldRoute8Below)`
  (`instIncompatibleDenseDeficiencyAtOrAboveColdRoute8Below`,
  `Strategy/SpineRows/DenseNetDeficiencyCap.lean`).
- **Removed.** The prefix block
  `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow` (from
  `Route8LanePrefix`, `ColdRateArm`, and the [186], Type B sublinear and [348]
  products); the `[54]` subtype `Node54ResidualOutcome_unrealizedTauHighColdBelow`;
  the four `[153]` subtypes `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_*`;
  the cold-terminal window block `W4`
  (`ColdBranchClosedWindowUnrealizedTauAtOrAboveThetaBelow`).  The
  private-carrier rate failure carries no such path (its `[160]` arms never
  reach `[146]` yes).  Merged with the `[173]` closure (above), the four
  `[153]` subtypes and `W4` are already absent (the absorbed lane and the
  cold-terminal product are not entered); on the route-8 products this closure
  removes 200 of the 1000 paths.

### [53] bound arm on the [161] dense residual: the entropy cap is active (tex 1325-1343, 7630-7643, 7648-7669; `prop:entropy-high-theta`, tex 1405)

- **Paper path.** [158] no → [159] (`2^{b_𝒫} > |𝒢_{n,m}|`,
  `K .windowPackageUnrealized`) → [160] first test yes (`τ(θ) < 1/4`,
  `K .denseDeficiencyBelow`) → either [161] (second test yes) → [25] with the
  deficiency cap, or [162] (second test no) → [146] no → [153] bounded →
  [24] → [25]; then [50] high → [52] (`K .entropyPackageDemand`) → [53] bound
  (`K .entropyCapBound`) → [55] Residual C.  Both are paper paths.
- **Why it is closed.** With `J ≤ B` (the bound), `[52]`'s
  `(2^{rate·L·p})^d·n^{|R|} ≤ J^d`, `[159]`'s `B < 2^{b_𝒫·p}` and the table's
  `b_𝒫 ≤ (rate+1)·L` give `L·|R| < d·L·p`; `[160]`'s yes arm gives
  `|R| > s·stubs·p = 60p ≥ 10p = d·p`.  This is the paper's own
  dichotomy `θ ≤ θ_win + o(1)` (Residual C) against the dense residual
  `θ > θ_win + o(1)` (tex 7641-7643), in the exact forms at G.
- **Evidence.** `Contracts.Spine.entropyCapActive_of_denseUnrealized` and
  `windowPackageBits_le_succ_rate` (`Graph/Contracts/Spine/RemainderEntropy.lean`);
  the presentation slack `d ≤ s·stubs` (`10 ≤ 60`) is discharged at the
  registered numbers (`spineData_entropySlack`).
- **Closed at the node, from G's ledger.** `denseEntropyCapActiveRow`
  (`Assembly/NearCubic/DenseEntropy.lean`, requires `K .denseDeficiencyBelow`,
  `K .windowPackageUnrealized`, `K .entropyPackageDemand`; produces
  `K .entropyCapActive`), run with `runAndCloseIncompatible … (K .entropyCapBound)
  (K .entropyCapActive)` (`instIncompatibleEntropyCapBoundActive`,
  `Strategy/EntropyClosure.lean`) on the `.right` arm of `entropyCapDichotomy`
  in `nearCubicLargeBudgetDenseRate` and `nearCubicLargeBudgetRateFailed`
  (`Assembly/NearCubic/Spine.lean`).
- **Removed.** The lane entry "[161] prefix × high entropy" from the [186],
  Type B sublinear, [348] and cold-terminal products (the lane entry factor
  is now `Route8LaneEntry`, 15 arms); the `[153]` subtype
  `Node153ResidualOutcome_denseRate_absorbed_high`; the private-carrier rate
  failure subtype `Route8RateFailsOutcome_denseBelow_highEntropy`.  Merged with
  the `[173]` closure (above), the `[153]` subtype and the cold-terminal
  product are already absent; on the route-8 products this closure removes 50
  of the 1000 paths, leaving `15 × 50 = 750`.

### [146]-no × [158]-yes and [24] × [146]-no: the density order, closed for every `n ≥ N₀` (Lean improvement (not routed by the paper); tex 6937-6960, 6998-7045, 7537-7541, 8479-8498, 739, 774, 1276, 1304)

*Group C6 (asymptotic closures made exact).*

- **Paper.** Node `[146]` no is `θ ≥ 1/78` (`def:cold-window-ledger`, tex
  6937-6960: `τ(θ) < 3/13 ⟺ θ < 1/78`; the cold-branch ledger rows 1-3, tex
  7537-7539).  The paper's density estimates read `θ ≤ θ_win + o(1)` with
  `θ_win = 3/(2c_hot) = 0.012700…` (tex 6942, 8487): on a realized window
  package (`prop:p13-density`, tex 8479-8498, from `lem:p13-window-package`
  and `lem:skeleton-dominates`), and at node `[24]` on the bounded arm of
  `[153]` (tex 739, 774; Part XI caption tex 1304).  Since `θ_win < 1/78`,
  the two estimates are incompatible for large `n`.  The paper never draws
  this conclusion: it routes the bounded arm to `[24]` → `[25]` and keeps the
  realized `[146]`-no arm alive through `[148]`--`[157]`.
- **Faithfulness verdict.** Every fact used sits on the path in the paper:
  `[158]` yes precedes `[22]` (Part I caption, tex 778); `[146]` no is the arm
  that runs `[148]`--`[153]` (tex 1276, 1304); `[24]` is reached exactly from
  the bounded arm of `[153]` (tex 739, 774).  The Lean closure uses only
  these facts at G's canonical packing `P₀`, so it is the paper's own dead
  branch made exact; since the paper does not route it, it is registered as
  a Lean improvement (user ruling).
- **Exact statement at G.**  `[146]` no gives the linear lower bound
  `δn ≤ A·p₁₃ + D·T(n)` with `A = δ·13 + (δs+1)·15 = 234`,
  `D = (δs+1) + δ·F·s = 109` (`Contracts.Spine.densityOrderLower_of_coldRoute8AtOrAbove`).
  The realized package gives `2·118·L·p₁₃ ≤ (L+1)(3n + T(n))`, `L = ⌊log₂ n⌋`
  (`Graph.two_mul_exponent_le_scale_mul_edgeBudget` with
  `rate·L ≤ bits`); node `[24]` gives the same with the additive slack
  `densitySlack·rate·L·T(n)`.  Combined (`Graph.densityOrderBound_of_lower_cap`):
  `2rL·δn ≤ A(L+1)(δn + T) + L·T·(A·S + 2rD)` with `S = 0` (realized) or
  `S = densitySlack·rate` (`[24]`).  With the rate margin `A = 234 < 2r = 236`
  this is false for every `n ≥ N₀` (`Graph.densityOrderBound_false_of_large`),
  `N₀ = max(2^(⌊2A/(2r−A)⌋+1), (2·(2A + A·S + 2rD)·C_sp + 1)²)`:
  - realized: `N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235 ≈ 5.52·10⁷⁰`
    (`C_sp = 674741758654409437347844`, so the square term is `≈ 1.25·10⁵⁷`);
  - `[24]`: `N₀ = max(2^235, (2·M·C_sp + 1)²)`, `M = 26192 + 55224·(1 + 4·B_cold)`,
    `B_cold = overlapBound` (the square term dominates).
- **Lean.** Library: `Hypostructure/Graph/DensityOrder.lean` (vocabulary-free
  arithmetic core and the cutoff), `Graph/Statements/DensityOrder.lean`,
  `Graph/Contracts/Spine/DensityOrder.lean`.  Keys (idx 6600-6605):
  `realizedDensityOrder`, `realizedOrderLarge`, `realizedOrderSmall`,
  `boundedDensityOrder`, `boundedOrderLarge`, `boundedOrderSmall`.  Rows and
  decisions: `Graph/Strategy/SpineRows/DensityOrder.lean`
  (`realizedDensityOrderRow`, `boundedDensityOrderRow`,
  `realizedOrderDichotomy`, `boundedOrderDichotomy`, instances
  `instIncompatibleRealizedDensityOrderLarge`,
  `instIncompatibleBoundedDensityOrderLarge`).
- **Closed at the node.** `Assembly/NearCubic/Survivor/Realized.lean`
  (`[146]` no arm of `nearCubicRealized`, before `[148]`):
  `closeIncompatible largeHistory (K .realizedDensityOrder) (K .realizedOrderLarge)`;
  `Assembly/NearCubic/Survivor/Unrealized.lean` (`[24]` on the bounded arms of
  `nearCubicDensePassAtOrAbove` and `nearCubicDensePassRateFailed`):
  `closeIncompatible largeHistory (K .boundedDensityOrder) (K .boundedOrderLarge)`.
  The small arms continue exactly as before, with the two facts on the
  ledger; see "Bounded-size residuals".

## Bounded-size residuals

A returned residual on the small arm of an exact size dichotomy carries, one
`get` per fact, the combined bound and `n < N₀`: G is a counterexample with
fewer than `N₀` vertices.  No hypothesis is added to the theorem and
`Problem.lean` is unchanged.

- **Realized arm (`[158]` yes, `[146]` no; `N₀ = 2^235`), facts
  `K .realizedDensityOrder`, `K .realizedOrderSmall`:**
  `Route8RateFailsOutcome_realized_*` (4 subtypes); `Node54ResidualOutcome_realizedBounded`;
  `Node153ResidualOutcome_realized_linear` (through `Node153LinearBlock_realized`);
  `ColdBranchClosedOutcome_linearRealizedDistinguished`,
  `ColdBranchClosedOutcome_linearRealizedSilent`; and every product path whose
  prefix is `Route8LanePrefixBlock_realizedColdAtOrAbove`: 200 of the 750 paths
  of each of `Route8JointBalanceOutcome_product`, `TypeBSublinearOutcome_product`,
  `Route8QuotientOutcome_product`.
- **`[24]` arm (`[158]` no, `[146]` no, bounded arm of `[153]`;
  `N₀ = max(2^235, (2·(26192 + 55224·(1 + 4·B_cold))·C_sp + 1)²)`), facts
  `K .boundedDensityOrder`, `K .boundedOrderSmall`:**
  `Route8RateFailsOutcome_denseAtOrAbove_*` (4) and `Route8RateFailsOutcome_denseBelow_*` (3);
  `Node54ResidualOutcome_unrealizedTauHighBounded`,
  `Node54ResidualOutcome_unrealizedRateFailsBounded`; and every product path
  whose prefix is `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`:
  200 of the 750 paths of each route-8 product.
- **Consequently every one of the eleven `Route8RateFailsOutcome_*` subtypes
  (`[187]`, private-carrier rate failure) and every bounded `[54]` subtype is
  now a bounded-size residual.**
- **Paths removed (the large arms, `N₀ ≤ n`):** the whole `[146]`-no
  continuation of the realized arm and the whole `[24]` continuation of both
  dense bounded arms, at every `n ≥ N₀`.
- **Not split: the net-deficiency cap (`SufficientlyLargeForNetCap`).**  The
  paper consumes the cap at `[57]` and at `[113]`, and states explicitly that
  it imposes no sufficient-order condition there (`rem:no-sufficient-order`,
  tex 7960-7965; `lem:exact-collision-test`, tex 7868-7905): `[57]`/`[173]` is
  decided exactly on the object, and `[113]` is an exact test (register entry
  "[113] diagram box vs `rem:why-unified`").  Of the three producers of
  `K .netDeficiencyCap`, the `[24]` one now lies entirely under the size
  split above; on the `[146]`-yes and `[161]` producers the absorbed arm of
  `[173]` is contradicted exactly (no condition on `n`) by the facts already
  on those ledgers (`coldRoute8Below` or `denseDeficiencyBelow` with
  `exactCollisionFails`, `stubSupply`, `hotColdPartition`; scratch
  `analysis-153/Closure153.lean`, closures A and B), which is the prefix/absorbed
  lanes' own work.  A split on `SufficientlyLargeForNetCap` would therefore
  close nothing and only add a residual.
- **Diameter ≤ 11 / Moore bound.** Checked against every uncapped count of
  the returned residuals; it closes or tightens nothing:
  - `[186]` open units `O` (`Route8JointBalanceStatement`,
    `Statements/RouteEightPinned.lean:314`) are demand units of entries over
    linearly many zero-surplus components of `G[R]`.  A per-component bound
    `|X| ≤ 1 + 3(2^11 − 1) = 6142` gives only `O ≤ c·b`, linear in the
    boundary incidence, which the residual's own inequalities already allow.
  - `[162]` counts a corridor's length (`ColdDenseHeavyEntrySpecAt`).  The
    corridor lies in `G − X_cold`, which contains hot and non-ambient-cubic
    windows, not in `R`, and it is a simple path, not a shortest one.
  - `[172a]` counts labelled near-cubic skeletons in two conditional fibres
    (`Statements/Spine.lean:732-810`), not pieces of `G`.
  - `B_cold` (hence `densitySlack` and the `[24]` cutoff) bounds first-failure
    supports `J`, which always meet two cold windows of `P₀` (tex 7204-7210,
    7336-7345).  So the `P₁₃`-free diameter argument does not reach them and
    does not lower `N₀`.
- **Merged shape (with the `[173]`, `[124]`, `[146]`-yes and `[53]` closures).**
  The absorbed-lane `[153]` subtypes, the cold-terminal product (window blocks
  `W1`/`W3`) and `Route8RateFailsOutcome_denseBelow_highEntropy` no longer
  exist, so the size facts sit on: the 11 rate-failure subtypes, the 3 bounded
  `[54]` subtypes, `Node153ResidualOutcome_realized_linear`, the 2 realized
  cold-terminal singletons, and 400 of the 750 paths of each route-8 product
  (200 through each of the two prefix blocks).

<a id="cycle-counting"></a>

## Cycle counting at G (port-cycles, 2026-09-28)

**Lean improvement (not routed by the paper).**  The cycle-count analyses
(scratch `cycle-count/All.lean`, `All2.lean`) are ported into a vocabulary-free
library and published as 8 facts of G on the entry prefix, so every residual
carries them (one `Holds` conjunct and one `get` each, next to
`K .singleBoundaryShape`).  No decision is added, moved or removed; no split.

- **Library** (Mathlib + `FiniteObject`, no EG names):
  `Graph/CycleCounting/Cycles.lean` (cycle sets through a vertex, pair counts,
  cycle decomposition at `h`, exact fibre count, global double count),
  `Graph/CycleCounting/Components.lean` (components of `G − h`, the two-per-block
  dichotomy, parity, returns, cross splits, residues),
  `Graph/CycleCounting/Meeting.lean` (star, meeting and theta arithmetic),
  `Graph/CycleCounting/Arithmetic.lean` (`5σ`, Cauchy–Schwarz, `16σ²`, matching
  counts, heavy centre, pigeonhole), `Graph/CycleCounting/Object.lean` (the
  properties at any `FiniteObject` from the generic hypotheses: baseline 3, no
  proper baseline, no bridge (`EdgeContraction.HasReturn`), target avoidance with
  the dyadic length law, independent high vertices).
- **Statements** `Graph/Statements/CycleCounting.lean`; **contracts**
  `Graph/Contracts/Spine/CycleCounting.lean` (`<key>_holds`, hypotheses exactly
  ledger facts); **rows** `Graph/Strategy/SpineRows/CycleCounting.lean`; wired in
  `Assembly/Entry.lean`.

| idx | key | fact at G | inputs (`inputs.get`) | placement |
|---:|---|---|---|---|
| 6900 | `neighbourhoodPairCount` | every `h`: `G[N(h)]` a matching (tex 2244, at every vertex), `C(d_h,2) − ⌊d_h/2⌋ ≤ #nonadjacent pairs of N(h)`, `d_h − 2 ≤` partners of each `x ∈ N(h)` | selection (avoidance), cubicBaseline (`LengthOK 4`) | after the presentation laws (`cycleNeighbourhoodRow`) |
| 6901 | `starCycleConstraint` | two paths of `G − h` from `x` to distinct `y, z ∈ N(h)`, meeting only at `x`: `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`) | selection, cubicBaseline (dyadic law) | same row |
| 6902 | `meetingCycleConstraint` | any two such paths meet at `t` with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` | selection, cubicBaseline | same row |
| 6903 | `highDegreePairSum` | `H = {d ≠ δ}`: `σ = Σ_H(d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h,2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H|Σ_H C(d_h,2)`, `2Σ_H C(d_h,2) ≤ 16σ²`, heavy centre `σ ≤ |H|(d_h − 3)` unless `σ = 0` | cubicBaseline, minDegreeBaseline | after `[1]`--`[3]` (`highDegreePairSumRow`) |
| 6904 | `vertexDeletionComponents` | every `h`: `G − h` connected, or `d_h = 2·#blocks(h)` even with exactly two neighbours of `h` per component | cubicBaseline, minDegreeBaseline, noProperBaseline (tex 720), bridgeless (tex 2144) | after `[8]` (`cutVertexCyclesRow`) |
| 6905 | `cyclesThroughVertex` | every `h`: `C(d_h,2) ≤ #cycles(h)` if `G − h` connected, else `2·#pairs(h) = d_h` and `d_h/2 ≤ #cycles(h)` | same | same row |
| 6906 | `cutVertexBlockPaths` | `G − h` disconnected: block `{a, b}` of each neighbour; `a → b` paths of `G − h` have `|r| + 2 ≠ 2^k`; returns of `ha` end by `bh`; `a → b` paths avoiding `ha, hb` avoid `h` (`≡ 3 mod 4` at length `2^j − 1`); cross paths split at `h` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, at length `2^j − 1`) | same + selection, dyadic law | same row |
| 6907 | `cycleDoubleCount` | `2Σ_H #cycles(h) ≤ n·#cycles(G)`, `2Σ_H L_h ≤ n·#cycles(G)`, `#cycles(G) ≤ 2^m` | cubicBaseline, minDegreeBaseline, noProperBaseline, bridgeless, slackIndependent (tex 2107) | after `[9]`/`[10]` (`cycleDoubleCountRow`) |

Every residual's fact count rises by 8 (table below).  No residual case is
closed by these facts (no closure added).

## Returned residuals

The current description of every returned residual of
`SelectedLedgerBoundaryResult` (`Assembly/Final.lean`).  Each residual is ONE
outcome abbrev in `Assembly/Residuals.lean`: the explicit conjunction of every
fact on its maximal ledger, in ledger order, built at its return by one
`ExactLedger.get` per fact (the return theorem named below).  The maximal
ledger is the set of facts that every path reaching the residual carries after
each path is brought, by the rows whose requirements it carries, to the same
fact set (fix4).  A fact that some paths carry and others cannot derive,
because its prerequisite is an arm of a decision that the path did not take
(running that decision on the path would open a second branch), is listed
under the entry with its gating decision; it is not carried.

`K .minDegreeBaseline` (`δ(G) ≥ δ`, `def:counterexample`, tex 714, 1370)
is published at the entry by `minDegreeBaselineRow`, directly after
`K .cubicBaseline`, from the selected object's own baseline proof (before, the
baseline was only the input field `selected.baseline`).  Every residual below
carries it: one `Holds` conjunct after `K .cubicBaseline` and one `get` in
each return theorem; in the fact lists below it is listed last.

Rows run on the paths that lacked them (fix4): `[149]`--`[152]`
(`nearCubicColdStubFacts`) on the `[147]` arms and on `[161]` (with `[22]`'s
cap, `liveHotBarrierCapRow`); `[25]`--`[34]`, `[48]` and `[58]`'s localization
on the linear arms of `[153]`, with `[175]`'s split and `[177]`'s fan data on
their extracted family; the cold corridors, states, first failures, (F1)/(F3)
readings and (F4) transfer on every net-charge lane; `[67]`/`[69]`'s normal form and landing lemmas, `[177]`'s
absorbed charge, `[112]`'s burden and `[114]`'s cores on every lane into
`[123]`; `[131]`'s dependence prefix, cubic budget, skeleton room and `[21]`'s
domination on the blocked side of the pair chain; `[135]`'s envelope on its
free side.

| Residual (abbrev) | Node | Form | Paths | Facts |
|---|---|---|---:|---:|
| `Node20aOutcome` | [20a] | single | 1 | 103 |
| `NearCubicTargetDefectOutcome` | [187] (near-cubic target defect) | single | 1 | 83 |
| `Node144aOutcome_*` | [144a] | 6 subtypes | 6 | 81 generic; 84, 85, 85, 86, 86, 87 |
| `BlockedBarrierOverlapOutcome_*` | [172a] | 2 subtypes (`[160]` arm) | 2 | 90 generic; 91, 92 |
| `PairConditionalFactorizationOutcome_*` | [182] | 6 subtypes | 6 | 71 generic; 74, 77, 80, 83, 86, 89 |
| `Route8JointBalanceOutcome_product` | [186] | product: lane entry (15 = 3 prefix × 4 entropy + [161] × 3 low entropy) × continuation (50) | 750 (400 bounded-size) | 98 generic; 118–157 |
| `PairTypeBOutcome_*` | [187] ([179]/[180] Type B entry) | 4 subtypes | 4 | 80 generic; 83, 86, 92, 95 |
| `TypeBSublinearOutcome_product` | [187] (Type B sublinear failure) | product: lane entry (15) × continuation (50) | 750 (400 bounded-size) | 81 generic; 101–140 |
| `Route8QuotientOutcome_product` | [187] ([348], route-8 quotient failure) | product: lane entry (15) × continuation (50) | 750 (400 bounded-size) | 83 generic; 103–142 |
| `Route8RateFailsOutcome_*` | [187] (private-carrier rate failure) | 11 subtypes (all bounded-size) | 11 | 62 generic; 67–71 |
| `ColdBranchClosedOutcome_linear*` | [187] (local cold-terminal exclusion) | 4 singletons (2 bounded-size) | 4 | 76 generic; 85, 86 (dense), 84, 84 (realized) |
| `Node153ResidualOutcome_*` | [153] | 3 subtypes (linear arms; 1 bounded-size) | 3 | 61 generic; 65, 66, 66 |
| `Node162ResidualOutcome_*` | [162] | 2 subtypes (`[160]` arm) | 2 | 65 generic; 66, 67 |
| `Node54ResidualOutcome_*` | [54] | 5 subtypes (3 bounded-size) | 5 | 60 generic; 63, 63, 66, 67, 68 |

**Path-count re-probe (final integration, after C1, C2, C3, C5, C6).**  The
elaborated-ledger probe (`PathProbe`, call-site `known` lists from the root)
finds 1170 call-site paths at each of `route8JointBalanceReturn`,
`route8QuotientReturn` and `typeBSublinearReturn`, with 1170 distinct fact sets.
Minus the generic keys, 750 of them are exactly the 750 block combinations of
`Route8LaneEntry × NetChargeContinuation` (every combination occurs once).  The
other 420 = 4 × 105 are the four fan/certificate pairs that do not occur (heavy-centre fan with the
`[81]` certificates, degree-four fan with the `[72]` certificates).  The
probe reads both branches of `cases degreeFour` in
`TypeB/Internal/Certificate.lean` for every caller, but each caller fixes
`degreeFour` (`BChainFanFor`), so only the matching certificate test runs.
Per-path totals from the probe: [186] 100–139, [348] 85–124, Type B
sublinear 83–122 facts, equal to the table.

**Hoisting re-probe (2026-09-28, branch `hoist-facts`).**  The `[20a]`
facts were moved to the earliest point where the keys each one reads are on
the ledger (see Node [20a], Placement): 11 keys into the entry prefix
(`packingOrderBound`, `noSuppressionChordViolation`, `specWitnessStructure`,
`bridgeless`, `remainderDeficiencyBelowCut`, `windowCutCapacity`,
`primitiveCarrierCount`, `singleBoundaryShape`, `surplusDartIdentity`,
`highDegreeCountBound`, `admissibleQuotientsLabelInjective`) and 19 to the top
of the strict arm of `[19]` (`sparseUpperEnvelope`, `baselineSpineDemand`,
`edgeSurplusIdentity`, `ceilSqrtAboveScale`, `orderAboveScaleSquare`,
`sixVertexExtremalEnvelope`, `highDegreePositive`, `highDegreeSurplusCapacity`,
`canonicalCapacityExplicit`, the seven canonical-capacity counts,
`paperBudgetBound`, `paperBudgetCertifies`, `pairCodeConfiguration`).  No
decision was added, moved or removed, so the path counts are unchanged.  The
same probe (`PathProbe`, call-site `known` lists from the root), run at every
generic return theorem and at the four Type B entry subtype returns, finds: 1
path at `[20a]` (95 facts) and at the near-cubic target defect (30); 6 at
`[144a]` (75–78); 2 at `[172a]` (83–84); 6 at `[182]` (66–80); 1170 each at
`[186]` (110–149), `[348]` (95–134) and Type B sublinear (93–132); 11 at the
rate failure (59–63); 4 at the cold-terminal exclusion (76–78); 3 at `[153]`
(57–58); 2 at `[162]` (58–59); 5 at `[54]` (55–60); and 1 at each Type B entry
subtype.  On every path every generic key is present, every hoisted key the
path carries is a key of its generic residual (none is in an arm block), and
no path lacks a hoisted key published above it.  `[135]`'s envelope on the free
side of the pair chain, `[129]`'s row on `[125]` and the four downstream
`bridgelessRow` runs are no longer separate rows: their keys are on the ledger
from the hoisted rows.

**Reuse of facts (2026-09-28, branch `reuse-facts`; user: "I want it where possible ... making as much of the proof as reusable as possible and re-invoking it with the corresponding residual where it helps").**  No row moved, no decision added, moved or removed; every re-invocation runs an existing row, unchanged, on another ledger that carries every key it reads, once per ledger.
- `K .freePairCountFails` (`sparseExitFreePairCountRow`, contract `freePairCountFails_at`, reads only strict-arm facts) runs again at the top of `[130]`'s dependent arm (`Surplus/Strict/Dependent.lean`).  On the independent arm it is the no-arm of `[131]`'s decision, so no ledger publishes it twice.  It is now a generic fact of `[144a]` (73), `[182]` (63) and the `[179]`/`[180]` Type B entry (72 common), and no longer an extra fact of the free/independent subtypes.
- The 45 `[20a]` witness-level keys (rows `sparseExitWitnessFactsRow`, `sparseExitRealizedContextsRow`, `sparseExitBoundaryRow`, `sparseExitCompressionRow`, `sparseExitDeletionRow`, `sparseExitCombinationRow`) run again on `[187]`'s near-cubic target defect (30 → 75 facts): that ledger carries the same `K .sparseTargetDefectResidual`, i.e. the same canonical witness `sparseTargetDefectWitness`, so the keys are the same facts about the same object.
- **Spec-generic contracts.**  Each of the 45 statements is now `AtSparseTargetDefectWitness data object <Key>AtWitness` (`Graph/Statements/SparseExitResidual.lean`, definitionally the old statement), and each contract is split into `<key>_of_spec` (any witness `w` with `w.Spec`, not only the canonical one) and `<key>_holds := atWitness_of_spec <key>_of_spec`.  None of the 45 needs canonicity beyond this transport; 10 do not even use `w.Spec` (`witnessActualOutsideNegative`, `witnessReadingsCycleFree`, `witnessReadingGluesNotSmallerBaseline`, `realizedContextsNegative`, `twoBoundaryLowOutsideSide`, `twoBoundaryOutsideClosure`, `twoBoundaryNoTargetSum`, `droppedEdgeTightDeficit`, `armOneForcedPath`, `wholeCutEdgeSurplusBound`).
- **No other canonical witness exists on a survivor ledger.**  `not_spec_of_survivor` (`Graph/Contracts/Spine/SparseExitResidual.lean`): a `Spec` witness is clause (b) of `def:named-surplus-exits`, against `K .sparseSurplusSurvivor`.  Every residual below the survivor arm of `[20]` (`[144a]`, `[182]`, the Type B entries, `[172a]`, `[186]`, `[153]`, `[162]`, `[54]`, the other `[187]` outcomes) carries that key, so the scratch witnesses `w'` (the `[144a]` routing's pinned defect) and `w''` (the `[179]` obstruction defect, `specWitness_of_obstructionDefect`) cannot be built there; the `[179]` target-defect alternative is already refuted on those ledgers by `declaredSparseSurplusExit_of_obstructionDefect`.  No new key, no ported lemma was needed.
- **Re-probe (`PathProbe`, same call-site probe as the hoisting re-probe).**  Path counts unchanged everywhere.  `[20a]` 1 path, 95 facts (unchanged); near-cubic target defect 1 path, 75 (was 30); `[144a]` 6 paths, 76/77/77/78/78/79 (each +1); `[182]` 6 paths, free 66/69/72 (unchanged: the key moved from the extras to the generic) and blocked 75/78/81 (each +1); Type B entry subtypes: independent unchanged, dependent +1; `[172a]`, `[153]`, `[162]`, `[54]`, cold-terminal and rate-failure fact sets unchanged.

Every return site calls its subtype or product return theorem, and
`SelectedLedgerBoundaryResult` lists the subtypes and products themselves (the
generic abbrevs remain as the common conjunct of each subtype and product,
read by the generic return theorem each subtype and product return calls).

**Arm threading (integration pass).**  A shared function reached from several
upstream arms takes one explicit arm argument, a proof of a `Prop` about G
assembled from arm blocks, each built at the call site where the arm's keys
are in scope by the block's `.ret` (one `get` per key on the single ledger);
a function reached from one arm takes that arm's `FactKeys.Has` instances.
The arm props are in `Assembly/Residuals/ArmBlocks.lean`:
`DenseTauArm` (`[160]` arm of the dense pass: `nearCubicDenseLinear`,
`selectedCanonicalReplacementContinuation`), `Node153Arm`
(`nearCubicColdOccurrence`), `ColdRateArm` / `DensityCapArm`
(`nearCubicLargeBudgetColdRate` / `DensityCap`; with `EntropyArm` on
`nearCubicRouteEightEntry`; `EntropyArmLow` alone on `nearCubicRateFailedExit`),
`NetChargeArms` (the lane entry `Route8LaneEntry`, prefix with entropy:
`selectedNetChargeContinuation` and every lane), the Type A lane arms (`TypeAEntryArms`, `TypeALaneArms`,
`TypeAExitFourArms`), `BChainArms` (the lane before the Type B chain) with
`BChainFanFor` on the certificate walk, and `Route8Arms` (lane entry ∧
continuation) on `selectedTypeBRoute8Continuation` and
`selectedRouteEightUnifiedResidual`.  No history is merged and no other carrier
is introduced.  The B-chain factor of `Route8Blocks.lean` lists only its 6
realized fan/certificate arms (the B2 test `[72]` runs only after a heavy-centre
fan and `[81]` only after a degree-four fan), so the net-charge continuation
had 68 arms and the route-8 products 1360 paths (the earlier count 2 × 5 fan ×
certificate combinations, 104 arms and 2080 paths, included 4 unrealized
fan/certificate pairs).  Two closures from G's facts remove continuation arms:
the `[113]`-yes/`[117]`-yes arm at `[124]` removes the `Route8DeficitBlock_holds`
factor choice (6 arms), and the `[173]` no-arm removes the absorbed lane (12
arms).  The continuation has 50 arms; with the 15-arm lane entry
(`Route8LaneEntry`, after the `[146]` and `[53]` lane-entry closures) each
route-8 product has 750 paths.

<a id="open-constructions"></a>
<a id="residual-20a"></a>

### Node [20a] (thm:main (i), tex 339-346)

- **Configuration at G.** The strict-surplus named sparse exit of [20]: the attempted-quotient target defect and its registered structure, on the strict arm of [19].
- **Pinned target-defect pair.** `[125]` and `[20]` are stated at one canonical witness `sparseTargetDefectWitness` (`Statements/SurplusPair.lean`: the `Classical.choose` of clause (b)'s pair, support `Z` and separating context `O`): `SparseTargetDefectResidualStatement` is `∃ w, sparseTargetDefectWitness = some w ∧ w.Spec`, and `SparseTargetDefectStructureStatement` is `∃ w, sparseTargetDefectWitness = some w ∧ BoundTargetDefectGeometryAt … Z (piece of w.first) (piece of w.second) O`, proved from `[125]`'s own witness by `boundTargetDefectGeometryAt_of_separated`.  Formerly the two were independent existentials, so `[20]`'s pair, `Z` and `O` need not have been `[125]`'s.
- **Lean.** `Node20aOutcome` (`Assembly/Residuals.lean`); return theorem `node20aReturn`; reached by 1 path (distinct ledger histories from the root).
- **Facts carried (19).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAbove`: Node `[19]`, above arm: the degree surplus exceeds the registered scale threshold.
  16. `K .sparsePairExit`: Node `[132]`, exit arm of `lem:sparse-pair-dependence-exit`: the dependence of a blocked pair's response coordinates is settled by a sparse surplus exit of `def:named-surplus-exits` rather than by a canonical blocker.
  17. `K .sparseTargetDefectResidual`: Node `[125]`, the sole nonterminal named-exit payload: clause (b) of `def:named-surplus-exits` at G's canonical witness `sparseTargetDefectWitness` (the identified pair of declared coordinates, their canonical support `Z` and the separating context `O`).
  18. `K .sparseTargetDefectStructure`: Node `[20]`: the bound target-defect geometry at the same canonical witness as `[125]` (the same pair, support `Z` and separating context `O`), with its proved target-free negative constituents.
  19. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
- **Enrichment on the `[20a]` path (84 more facts, 103 in all).** Type A rows in `hypostructure/Hypostructure/Graph/Strategy/SpineRows/SparseExitResidual.lean` (plus the existing `bridgelessRow` and `exactWindowJoinPressureRow`); no decision, no split, one residual.  **Placement (hoisted, 2026-09-28; user: "move the facts as far up as possible so that the other branches can also benefit").**  Each row runs right after the last producer of the keys it actually reads (`inputs.get`), on the shared prefix; rows whose keys have different earliest points were split by key (no key restated, no new split).  11 keys are published in the entry prefix (`Assembly/Entry.lean`) and are carried by every residual; 19 at the top of the strict arm of `[19]` (`Assembly/Final.lean`, before `[20]`) and are carried by every strict-surplus residual (`[20a]`, `[144a]`, `[182]`, `[187]` Type B entry); the other 46 (the 45 that read `K .sparseTargetDefectResidual`, and `K .freePairCountFails`) stay on the `[20a]` arm.  The duplicate runs downstream were removed: `bridgelessRow` in `NearCubic/DensePass.lean`, `NearCubic/Survivor/Realized.lean`, `NetCharge/Continuation.lean`, `Surplus/Strict/Dependent.lean`; `exactWindowJoinPressureRow` (`[135]`) in `Surplus/Strict/Independent.lean` and `Surplus/Strict/Dependent.lean`; `[129]`'s `baselineSpineDemandRow` in `Surplus/Strict.lean` (its key is now published by `sparseExitBaselineSpineDemandRow`, which reads only entry facts and `K .surplusAbove`).  The paper strategy is unchanged: no decision is added, moved or removed.  Statements: `Graph/Statements/SparseExitResidual.lean`, `Graph/Statements/CanonicalCapacityExplicit.lean`; contracts (`<key>_holds`): `Graph/Contracts/Spine/SparseExitResidual.lean`; vocabulary-free library: `Graph/GluedReadingMaps.lean`, `Graph/SparseOrderArithmetic.lean` (incl. the finite check `ex(6, C₄) = 7`, `native_decide`), `Graph/DeclaredQuotientRank.lean`.  Tagged **Lean improvement (not routed by the paper)**: every fact is derived from the 19 facts above, at G, at `[125]`'s pinned witness `w = (first, second, Z, O)`, at `P₀`, and at G's canonical capacity presentation, canonical object ledger and canonical spine family.  ¬K4 is `K .orderAboveScaleSquare`; ¬K5 follows from `K .sixVertexExtremalEnvelope`; K6 is ¬`K .surplusAbove`, and its quantitative form is `K .canonicalLedgerDeficit` / `K .pairCountDeficit`.  Registered constants of the presentation (not ledger facts): `Assembly/Surplus/RegisteredConstants.lean`.
  20. `K .bridgeless` (existing key, existing `bridgelessRow`): `lem:bridgeless` at G.  *Published at: entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`).*
  21. `K .sparseUpperEnvelope` (existing key, existing `exactWindowJoinPressureRow`): `m + 2 ≤ (δ−1)n` and the exact window-join identity at `P₀`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`exactWindowJoinPressureRow`).*
  22. `K .baselineSpineDemand` (existing key, new row `sparseExitBaselineSpineDemandRow`): `[129]`'s baseline spine demand, its survivor premise replaced by the replacement exclusion and selection.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitBaselineSpineDemandRow`).*
  23. `K .freePairCountFails` (existing key, new row `sparseExitFreePairCountRow`): node `[131]`'s full-schedule entropy count fails at G's canonical objects, unconditionally.  *Published at: the `[20a]` arm, and (reuse, 2026-09-28) the same row again at the top of `[130]`'s dependent arm (`Surplus/Strict/Dependent.lean`), so every dependent-arm residual (`[144a]`, the blocked `[182]` subtypes, the dependent Type B entry subtypes) carries it.  Not hoisted above `[130]`: on the independent arm the key is the no-arm of the paper's `[131]` decision `freePairEntropyDichotomy`; there it comes from that decision, so no ledger publishes it twice.*
  24. `K .witnessReadingsNotTargetComplete` (idx 6615): **The readings are not target-complete.**
  25. `K .witnessActualOutsideNegative` (idx 6616): **Neither reading has an accepted cycle at `G − Z`.**
  26. `K .witnessReadingsCycleFree` (idx 6617): **Both reading pieces are cycle-free** (each embeds in G).
  27. `K .witnessSupportOrderBound` (idx 6618): **`|Z| + 1 ≤ n`.**
  28. `K .witnessReadingGluesNotSmallerBaseline` (idx 6619): **No reading's gluing with `G − Z` is a lexicographically smaller baseline object** (¬K3).
  29. `K .noSuppressionChordViolation` (idx 6620): **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Published at: entry prefix, after `[4]` (`entrySelectionFactsRow`).*
  30. `K .edgeSurplusIdentity` (idx 6606): **Edge–surplus identity**: `2m = δ·n + σ`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`).*
  31. `K .surplusDartIdentity` (idx 6607): **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Published at: entry prefix, after `[9]`/`[10]` (`degreeCountRow`).*
  32. `K .highDegreeCountBound` (idx 6608): **High-degree count**: `|H| ≤ σ`.  *Published at: entry prefix, after `[9]`/`[10]` (`degreeCountRow`).*
  33. `K .packingOrderBound` (idx 6611): **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Published at: entry prefix, after `[4]` (`entrySelectionFactsRow`).*
  34. `K .ceilSqrtAboveScale` (idx 6612): **`C + 1 ≤ ⌈√n⌉`.**  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`).*
  35. `K .orderAboveScaleSquare` (idx 6613): **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`).  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`).*
  36. `K .sixVertexExtremalEnvelope` (idx 6614): **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`).*
  37. `K .remainderDeficiencyBelowCut` (idx 6663): **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Published at: entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`).*
  38. `K .windowCutCapacity` (idx 6664): **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Published at: entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`).*
  39. `K .witnessOutsideNotRealized` (idx 6621): **`O` is not realized in `G − Z`.**
  40. `K .realizedContextsNegative` (idx 6622): **Both readings are negative in every context realized in `G − Z`.**
  41. `K .negativeSubGluingNotSmallerBaseline` (idx 6623): **No negative sub-gluing is a lexicographically smaller baseline object**: the negative reading `N` at `O`, against every sub-context `O' ≤ O`.
  42. `K .cycleSubContextSeparates` (idx 6624): **The O-part of one positive cycle still separates**: a sub-context `O' ≤ O` with `P` positive and `N` negative, every `O'`-internal vertex of `O'`-degree at most `2`, and `glue N O'` not a baseline object.
  43. `K .pathSpectrumSplit` (idx 6625): **The path-length spectrum split** at the witness: for the positive reading `P` and the negative reading `N` at `O`, either (i) labels `a ≠ b` of `∂Z`, a path `π : a → b` of `ret_P` and an `O`-path `σ : b → a` meeting no other label with `|π| + |σ| = 2^k` (`k ≥ 2`), such that every `a → b` path `π'` of `ret_N` has `|π'| ≠ |π|` and `|π'| + |σ| ≠ 2^j` for every `j ≥ 2`; or (ii) every accepted cycle of `glue ret_P O` meets three distinct labels.
  44. `K .admissibleQuotientsLabelInjective` (idx 6626): **Every admissible quotient of G is label-injective** on its family.  *Published at: entry prefix, after `[13]` (`sparseExitQuotientsRow`).*
  45. `K .singleBoundaryShape` (idx 6627): **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Published at: entry prefix, after `[8]` (`singleBoundaryShapeRow`).*
  46. `K .positiveSupportBoundaryTwo` (idx 6628): **`2 ≤ |∂Z ∩ X⁺|`** for one declared support `X⁺ ∈ {A, B}`.
  47. `K .supportCutEdgesTwo` (idx 6629): **`2 ≤ e(∂Z, V ∖ Z)`.**
  48. `K .boundaryLowInsideVertex` (idx 6630): **A boundary vertex with at most two neighbours in `Z`.**
  49. `K .outsideLowVertex` (idx 6631): **An outside vertex with at most two outside neighbours and a neighbour in `Z`.**
  50. `K .twoBoundaryLowOutsideSide` (idx 6632): **`∂Z = {a, b}` with an interior vertex: one terminal has at most two neighbours in `T' = (V ∖ Z) ∪ {a, b}`.**
  51. `K .twoBoundarySupportClosure` (idx 6633): **2-sum closure on the `Z` side**: if `a ≁ b` and both have two neighbours in `Z`, then `G[Z]` has an `a`–`b` path `P` with `|P| + 1` accepted.
  52. `K .twoBoundaryOutsideClosure` (idx 6634): **2-sum closure on the outside side** (interior arm).
  53. `K .twoBoundaryNoTargetSum` (idx 6635): **The length-set constraint at `∂Z = {a, b}`**: an `a`–`b` path in `Z` and a `b`–`a` path in `T'` (not both single edges) never sum to an accepted length.
  54. `K .outsideOrBoundaryLarge` (idx 6636): **`2 ≤ |W|` or `3 ≤ |∂Z|`.**
  55. `K .droppedEdgeTightDeficit` (idx 6637): **Every G-edge a reading drops at `G − Z` has an endpoint below the baseline there.**
  56. `K .notBothReadingsWhole` (idx 6638): **At most one reading is whole**: `¬ (Z ⊆ A ∧ Z ⊆ B)`.
  57. `K .firstWholeOrientation` (idx 6639): **Whole case `Z ⊆ A`: `A` positive and `B` negative at `O`.**
  58. `K .firstWholeDeficitNonempty` (idx 6640): **Whole case `Z ⊆ A`: `1 ≤ |Z ∖ B|`.**
  59. `K .firstWholeDeficitStructure` (idx 6641): **Whole case `Z ⊆ A`: the deficit set `Z ∖ B` is internal, has no `∂Z`-neighbour, and is isolated in every gluing of `ret_B`.**
  60. `K .firstWholeDeficitSum` (idx 6642): **Whole case `Z ⊆ A`: `δ·|Z ∖ B| ≤ Σ (δ − deg)` in every gluing of `ret_B`.**
  61. `K .secondWholeOrientation` (idx 6643): **Whole case `Z ⊆ B`: `B` positive and `A` negative at `O`.**
  62. `K .secondWholeDeficitNonempty` (idx 6644): **Whole case `Z ⊆ B`: `1 ≤ |Z ∖ A|`.**
  63. `K .secondWholeDeficitStructure` (idx 6645): **Whole case `Z ⊆ B`: the deficit set `Z ∖ A` is internal, has no `∂Z`-neighbour, and is isolated in every gluing of `ret_A`.**
  64. `K .secondWholeDeficitSum` (idx 6646): **Whole case `Z ⊆ B`: `δ·|Z ∖ A| ≤ Σ (δ − deg)` in every gluing of `ret_A`.**
  65. `K .deletedSupportReduction` (idx 6647): **Whole case (`Z ⊆ A` with `S = Z ∖ B`, and `Z ⊆ B` with `S = Z ∖ A`): `G − S` is lexicographically smaller than G, has no accepted cycle, and fails `δ ≥ 3`.**
  66. `K .deletedSupportDeficientVertex` (idx 6648): **Whole case: a deficient vertex of `G − S` exists, and every one lies in `Z ∩ B`, is internal to `Z`, and has a neighbour in `S`.**
  67. `K .deletedSupportDeficitSums` (idx 6649): **Whole case: the deficit sums** `1 ≤ Σ_T (3 − deg_{G−S}) = Σ_T (d_S − (deg − 3)) ≤ e(S, T)`, with equality `= e(S, T)` when every `T`-neighbour of `S` has degree `3`.
  68. `K .deletedSupportEdgeRestoration` (idx 6650): **Whole case: one restoring edge forces an accepted closing path**: if adding `xy` to `G − S` restores `δ ≥ 3`, then `G − S` has a `y → x` path of length `ℓ` with `ℓ + 1` accepted.
  69. `K .deletedSupportEdgeSetRestoration` (idx 6651): **Whole case: any restoring edge set forces an accepted cycle through a new edge.**
  70. `K .firstKeepsAllNotWhole` (idx 6652): **Keeps-all for `A` with `Z ⊄ A`**: `Z ⊄ B`, and both readings' profiles differ from the whole piece's.
  71. `K .secondKeepsAllNotWhole` (idx 6653): **Keeps-all for `B` with `Z ⊄ B`**: `Z ⊄ A`, and both readings' profiles differ from the whole piece's.
  72. `K .highDegreePositive` (idx 6609): **At least one high-degree vertex**: `1 ≤ |H|`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`).*
  73. `K .highDegreeSurplusCapacity` (idx 6610): **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every high vertex has all its neighbours among the `n − |H|` baseline vertices).  *Published at: top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`).*
  74. `K .pairArmExcluded` (idx 6654): **The pair arm does not occur**: `¬ (∂Z = Z = {a, b})` (equal profiles on a two-vertex all-boundary support force equal readings, against the separation at `O`).
  75. `K .twoBoundaryForcesArmOne` (idx 6655): **`|∂Z| = 2` forces arm (i) of the spectrum split**, `∂Z = {a, b}` inside one declared support, an interior vertex of `Z`, and `{a, b}` separating the interior from `V ∖ Z`.
  76. `K .armOneForcedPath` (idx 6656): **Arm (i) gives a forced path in `G[Z]`**: a simple `a–b` path `p` of `G[Z]` between two boundary vertices with `|p| + 1 ≤ |Z|` and `|p| + s = 2^k` (`k ≥ 2`, `s ≥ 1`, `(|p| + s) % 4 = 0`).
  77. `K .twoBoundaryForcedPathCross` (idx 6657): **`|∂Z| = 2`, the K1 × K2 cross constraint**: `∂Z = {a, b}` carries the forced path `p ⊆ G[Z]` (`|p| + s = 2^k`); no simple `b → a` path `q` in `T' = (V ∖ Z) ∪ {a, b}` (not both single edges) has `|p| + |q|` accepted; and if `a ≁ b` with both terminals of `T'`-degree `≥ 2`, the outside closure `q` exists with `|q| + 1` accepted and `|p| + |q|` not accepted.
  78. `K .supportSteinerMinimal` (idx 6658): **`Z` is a minimum connected set containing `A ∪ B`.**
  79. `K .steinerVerticesCut` (idx 6659): **Every vertex of `Z ∖ (A ∪ B)` is a cut vertex of `G[Z]`.**
  80. `K .wholeSupportEqual` (idx 6660): **The whole case pins `Z`**: `Z ⊆ A ⇒ Z = A ∧ B ⊆ A`, and `Z ⊆ B ⇒ Z = B ∧ A ⊆ B`.
  81. `K .wholeDeficitBoundaryCount` (idx 6661): **Whole case: `|S| + |∂Z| ≤ |Z|`** (`S = Z ∖ B` resp. `Z ∖ A`).
  82. `K .wholeCutEdgeSurplusBound` (idx 6662): **Whole case: `e(S, T) ≤ D_T + σ`**, with `D_T = Σ_T (3 − deg_{G−S})`.
  83. `K .canonicalCapacityExplicit` (idx 6665): **G's canonical capacity presentation is the explicit one**: the recorded blocker activation of G's active family on the node-`[19]` packing.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityRow`).*
  84. `K .primitiveCarrierCount` (idx 6666): **`|𝔘_sp(G)| = 4n + 2σ`.**  *Published at: entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`).*
  85. `K .canonicalTokenCount` (idx 6667): **The exact token count at the canonical presentation**: `|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`: `|𝔗_cap| = 4n + 3σ + 15ν`).  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  86. `K .canonicalBlockedFreePartition` (idx 6668): **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  87. `K .canonicalLedgerDeficit` (idx 6669): **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`, `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  88. `K .pairCountDeficit` (idx 6670): **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  89. `K .canonicalCertificationCriterion` (idx 6671): **The certification criterion at the canonical presentation**: its canonical certified ledger exists iff `|Π_free| ≤ B`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  90. `K .canonicalOverloadOfFits` (idx 6674): **If the free side fits `B`, the blocked side is overloaded**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load `> M₀` and carries an `L_geom` role-homogeneous matching or star.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  91. `K .canonicalFreeExcessOfCapped` (idx 6675): **If every token carries load `≤ M₀`, the free side exceeds `B`**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`).*
  92. `K .paperBudgetBound` (idx 6672): **The paper's budget at the canonical spine family fits the certification budget**: `E_paper ≤ B`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`).*
  93. `K .paperBudgetCertifies` (idx 6673): **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`).*
  94. `K .pairCodeConfiguration` (idx 6676): **Where G sits in the pair-code chain**: either the `[137]`→`[143]` configuration holds at the canonical objects (blocked pair, `[137]` count, canonical pattern, overload, caps fail), or G's canonical first failure exists and yields the `[182]` residual, or the target defect of the canonical return system's obstruction coordinates, or that obstruction's handoff together with the Type B fan entry `[65]`.  *Published at: top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`).*
  95. `K .specWitnessStructure` (idx 6677): **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Published at: entry prefix, after `[4]` (`entrySelectionFactsRow`).*
  96. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  97. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  98. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  99. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  100. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  101. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  102. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  103. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*

<a id="residual-187-near-cubic-target-defect"></a>

### Node [187] (near-cubic target defect) (thm:main (vi), tex 369-378)

- **Configuration at G.** The sparse target-defect exit of [20] on the at-or-below-surplus arm of [19].
- **Pinned target-defect pair.** `[125]` and `[20]` are stated at one canonical witness `sparseTargetDefectWitness` (`Statements/SurplusPair.lean`: the `Classical.choose` of clause (b)'s pair, support `Z` and separating context `O`): `SparseTargetDefectResidualStatement` is `∃ w, sparseTargetDefectWitness = some w ∧ w.Spec`, and `SparseTargetDefectStructureStatement` is `∃ w, sparseTargetDefectWitness = some w ∧ BoundTargetDefectGeometryAt … Z (piece of w.first) (piece of w.second) O`, proved from `[125]`'s own witness by `boundTargetDefectGeometryAt_of_separated`.  Formerly the two were independent existentials, so `[20]`'s pair, `Z` and `O` need not have been `[125]`'s.
- **Lean.** `NearCubicTargetDefectOutcome` (`Assembly/Residuals.lean`); return theorem `nearCubicTargetDefectReturn`; reached by 1 path (distinct ledger histories from the root).
- **Distinct fact sets.** One: the single return site (`selectedNearCubicBranch`, exit arm of `sparseSurplusSurvivorDichotomy`, then `selectedSparseTargetDefectExit`) carries exactly the 83 keys below, so the generic residual is the only node and has no subtypes.
- **Facts carried (83).**  Items 1–30 are the path's facts; items 31–75 are the 45 witness-level facts of `[20a]` re-invoked here (reuse, 2026-09-28): this ledger carries the same `K .sparseTargetDefectResidual`, i.e. `[125]`'s canonical witness `sparseTargetDefectWitness` (`w = (first, second, Z, O)`), so the six `[20a]` witness rows run again after `selectedSparseTargetDefectExit` (`Assembly/Final.lean`, `selectedNearCubicBranch`), once each, unchanged: the same keys about the same object.  None of them reads `K .surplusAbove`.  Each contract is now `atWitness_of_spec` applied to its Spec-generic `<key>_of_spec` (`Graph/Contracts/Spine/SparseExitResidual.lean`).
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparsePairExit`: Node `[132]`, exit arm of `lem:sparse-pair-dependence-exit`: the dependence of a blocked pair's response coordinates is settled by a sparse surplus exit of `def:named-surplus-exits` rather than by a canonical blocker.
  17. `K .sparseTargetDefectResidual`: Node `[125]`, the sole nonterminal named-exit payload: clause (b) of `def:named-surplus-exits` at G's canonical witness `sparseTargetDefectWitness` (the identified pair of declared coordinates, their canonical support `Z` and the separating context `O`).
  18. `K .sparseTargetDefectStructure`: Node `[20]`: the bound target-defect geometry at the same canonical witness as `[125]` (the same pair, support `Z` and separating context `O`), with its proved target-free negative constituents.
  19. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  20. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  21. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  22. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  23. `K .bridgeless`: `lem:bridgeless` at G.  *Hoisted (entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`); `[20a]` item 20).*
  24. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  25. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  26. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  27. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  28. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  29. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  30. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  31. `K .witnessReadingsNotTargetComplete`: **The readings are not target-complete.**  *Re-invoked (`sparseExitWitnessFactsRow`, same key and canonical witness as `[20a]` item 24).*
  32. `K .witnessActualOutsideNegative`: **Neither reading has an accepted cycle at `G − Z`.**  *Re-invoked (`sparseExitWitnessFactsRow`, same key and canonical witness as `[20a]` item 25).*
  33. `K .witnessReadingsCycleFree`: **Both reading pieces are cycle-free** (each embeds in G).  *Re-invoked (`sparseExitWitnessFactsRow`, same key and canonical witness as `[20a]` item 26).*
  34. `K .witnessSupportOrderBound`: **`|Z| + 1 ≤ n`.**  *Re-invoked (`sparseExitWitnessFactsRow`, same key and canonical witness as `[20a]` item 27).*
  35. `K .witnessReadingGluesNotSmallerBaseline`: **No reading's gluing with `G − Z` is a lexicographically smaller baseline object** (¬K3).  *Re-invoked (`sparseExitWitnessFactsRow`, same key and canonical witness as `[20a]` item 28).*
  36. `K .witnessOutsideNotRealized`: **`O` is not realized in `G − Z`.**  *Re-invoked (`sparseExitRealizedContextsRow`, same key and canonical witness as `[20a]` item 39).*
  37. `K .realizedContextsNegative`: **Both readings are negative in every context realized in `G − Z`.**  *Re-invoked (`sparseExitRealizedContextsRow`, same key and canonical witness as `[20a]` item 40).*
  38. `K .negativeSubGluingNotSmallerBaseline`: **No negative sub-gluing is a lexicographically smaller baseline object**: the negative reading `N` at `O`, against every sub-context `O' ≤ O`.  *Re-invoked (`sparseExitRealizedContextsRow`, same key and canonical witness as `[20a]` item 41).*
  39. `K .cycleSubContextSeparates`: **The O-part of one positive cycle still separates**: a sub-context `O' ≤ O` with `P` positive and `N` negative, every `O'`-internal vertex of `O'`-degree at most `2`, and `glue N O'` not a baseline object.  *Re-invoked (`sparseExitRealizedContextsRow`, same key and canonical witness as `[20a]` item 42).*
  40. `K .pathSpectrumSplit`: **The path-length spectrum split** at the witness: for the positive reading `P` and the negative reading `N` at `O`, either (i) labels `a ≠ b` of `∂Z`, a path `π : a → b` of `ret_P` and an `O`-path `σ : b → a` meeting no other label with `|π| + |σ| = 2^k` (`k ≥ 2`), such that every `a → b` path `π'` of `ret_N` has `|π'| ≠ |π|` and `|π'| + |σ| ≠ 2^j` for every `j ≥ 2`; or (ii) every accepted cycle of `glue ret_P O` meets three distinct labels.  *Re-invoked (`sparseExitRealizedContextsRow`, same key and canonical witness as `[20a]` item 43).*
  41. `K .positiveSupportBoundaryTwo`: **`2 ≤ |∂Z ∩ X⁺|`** for one declared support `X⁺ ∈ {A, B}`.  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 46).*
  42. `K .supportCutEdgesTwo`: **`2 ≤ e(∂Z, V ∖ Z)`.**  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 47).*
  43. `K .boundaryLowInsideVertex`: **A boundary vertex with at most two neighbours in `Z`.**  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 48).*
  44. `K .outsideLowVertex`: **An outside vertex with at most two outside neighbours and a neighbour in `Z`.**  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 49).*
  45. `K .twoBoundaryLowOutsideSide`: **`∂Z = {a, b}` with an interior vertex: one terminal has at most two neighbours in `T' = (V ∖ Z) ∪ {a, b}`.**  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 50).*
  46. `K .twoBoundarySupportClosure`: **2-sum closure on the `Z` side**: if `a ≁ b` and both have two neighbours in `Z`, then `G[Z]` has an `a`–`b` path `P` with `|P| + 1` accepted.  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 51).*
  47. `K .twoBoundaryOutsideClosure`: **2-sum closure on the outside side** (interior arm).  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 52).*
  48. `K .twoBoundaryNoTargetSum`: **The length-set constraint at `∂Z = {a, b}`**: an `a`–`b` path in `Z` and a `b`–`a` path in `T'` (not both single edges) never sum to an accepted length.  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 53).*
  49. `K .outsideOrBoundaryLarge`: **`2 ≤ |W|` or `3 ≤ |∂Z|`.**  *Re-invoked (`sparseExitBoundaryRow`, same key and canonical witness as `[20a]` item 54).*
  50. `K .droppedEdgeTightDeficit`: **Every G-edge a reading drops at `G − Z` has an endpoint below the baseline there.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 55).*
  51. `K .notBothReadingsWhole`: **At most one reading is whole**: `¬ (Z ⊆ A ∧ Z ⊆ B)`.  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 56).*
  52. `K .firstWholeOrientation`: **Whole case `Z ⊆ A`: `A` positive and `B` negative at `O`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 57).*
  53. `K .firstWholeDeficitNonempty`: **Whole case `Z ⊆ A`: `1 ≤ |Z ∖ B|`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 58).*
  54. `K .firstWholeDeficitStructure`: **Whole case `Z ⊆ A`: the deficit set `Z ∖ B` is internal, has no `∂Z`-neighbour, and is isolated in every gluing of `ret_B`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 59).*
  55. `K .firstWholeDeficitSum`: **Whole case `Z ⊆ A`: `δ·|Z ∖ B| ≤ Σ (δ − deg)` in every gluing of `ret_B`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 60).*
  56. `K .secondWholeOrientation`: **Whole case `Z ⊆ B`: `B` positive and `A` negative at `O`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 61).*
  57. `K .secondWholeDeficitNonempty`: **Whole case `Z ⊆ B`: `1 ≤ |Z ∖ A|`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 62).*
  58. `K .secondWholeDeficitStructure`: **Whole case `Z ⊆ B`: the deficit set `Z ∖ A` is internal, has no `∂Z`-neighbour, and is isolated in every gluing of `ret_A`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 63).*
  59. `K .secondWholeDeficitSum`: **Whole case `Z ⊆ B`: `δ·|Z ∖ A| ≤ Σ (δ − deg)` in every gluing of `ret_A`.**  *Re-invoked (`sparseExitCompressionRow`, same key and canonical witness as `[20a]` item 64).*
  60. `K .deletedSupportReduction`: **Whole case (`Z ⊆ A` with `S = Z ∖ B`, and `Z ⊆ B` with `S = Z ∖ A`): `G − S` is lexicographically smaller than G, has no accepted cycle, and fails `δ ≥ 3`.**  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 65).*
  61. `K .deletedSupportDeficientVertex`: **Whole case: a deficient vertex of `G − S` exists, and every one lies in `Z ∩ B`, is internal to `Z`, and has a neighbour in `S`.**  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 66).*
  62. `K .deletedSupportDeficitSums`: **Whole case: the deficit sums** `1 ≤ Σ_T (3 − deg_{G−S}) = Σ_T (d_S − (deg − 3)) ≤ e(S, T)`, with equality `= e(S, T)` when every `T`-neighbour of `S` has degree `3`.  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 67).*
  63. `K .deletedSupportEdgeRestoration`: **Whole case: one restoring edge forces an accepted closing path**: if adding `xy` to `G − S` restores `δ ≥ 3`, then `G − S` has a `y → x` path of length `ℓ` with `ℓ + 1` accepted.  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 68).*
  64. `K .deletedSupportEdgeSetRestoration`: **Whole case: any restoring edge set forces an accepted cycle through a new edge.**  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 69).*
  65. `K .firstKeepsAllNotWhole`: **Keeps-all for `A` with `Z ⊄ A`**: `Z ⊄ B`, and both readings' profiles differ from the whole piece's.  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 70).*
  66. `K .secondKeepsAllNotWhole`: **Keeps-all for `B` with `Z ⊄ B`**: `Z ⊄ A`, and both readings' profiles differ from the whole piece's.  *Re-invoked (`sparseExitDeletionRow`, same key and canonical witness as `[20a]` item 71).*
  67. `K .pairArmExcluded`: **The pair arm does not occur**: `¬ (∂Z = Z = {a, b})` (equal profiles on a two-vertex all-boundary support force equal readings, against the separation at `O`).  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 74).*
  68. `K .twoBoundaryForcesArmOne`: **`|∂Z| = 2` forces arm (i) of the spectrum split**, `∂Z = {a, b}` inside one declared support, an interior vertex of `Z`, and `{a, b}` separating the interior from `V ∖ Z`.  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 75).*
  69. `K .armOneForcedPath`: **Arm (i) gives a forced path in `G[Z]`**: a simple `a–b` path `p` of `G[Z]` between two boundary vertices with `|p| + 1 ≤ |Z|` and `|p| + s = 2^k` (`k ≥ 2`, `s ≥ 1`, `(|p| + s) % 4 = 0`).  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 76).*
  70. `K .twoBoundaryForcedPathCross`: **`|∂Z| = 2`, the K1 × K2 cross constraint**: `∂Z = {a, b}` carries the forced path `p ⊆ G[Z]` (`|p| + s = 2^k`); no simple `b → a` path `q` in `T' = (V ∖ Z) ∪ {a, b}` (not both single edges) has `|p| + |q|` accepted; and if `a ≁ b` with both terminals of `T'`-degree `≥ 2`, the outside closure `q` exists with `|q| + 1` accepted and `|p| + |q|` not accepted.  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 77).*
  71. `K .supportSteinerMinimal`: **`Z` is a minimum connected set containing `A ∪ B`.**  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 78).*
  72. `K .steinerVerticesCut`: **Every vertex of `Z ∖ (A ∪ B)` is a cut vertex of `G[Z]`.**  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 79).*
  73. `K .wholeSupportEqual`: **The whole case pins `Z`**: `Z ⊆ A ⇒ Z = A ∧ B ⊆ A`, and `Z ⊆ B ⇒ Z = B ∧ A ⊆ B`.  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 80).*
  74. `K .wholeDeficitBoundaryCount`: **Whole case: `|S| + |∂Z| ≤ |Z|`** (`S = Z ∖ B` resp. `Z ∖ A`).  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 81).*
  75. `K .wholeCutEdgeSurplusBound`: **Whole case: `e(S, T) ≤ D_T + σ`**, with `D_T = Σ_T (3 − deg_{G−S})`.  *Re-invoked (`sparseExitCombinationRow`, same key and canonical witness as `[20a]` item 82).*
  76. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  77. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  78. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  79. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  80. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  81. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  82. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  83. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*

<a id="residual-144a"></a>

### Node [144a] (thm:main (ii), tex 347-353)

- **Configuration at G.** The same-token Type B handoff of [144] on the strict-surplus survivor, or (the paper error at [144]) the unresolved same-label pattern pair.
- **The paper step it carries.** `lem:same-token-bottleneck-routing` (tex 5585-5620) routes the two equal-label pattern edges of G's canonical routing to a same-token Type B handoff; where no handoff is produced (`K .typeBHandoffFails`), the unresolved same-label pattern pair (`K .sameTokenPatternUnresolved`: readings profile-separated, neither a sparse exit nor target-complete) and the explicit replacement candidates of tex 5594 (`K .sameTokenReadingsNotReplacement`) are carried instead.
- **Lean.** Generic residual `Node144aOutcome` (`Assembly/Residuals.lean`), the 81 facts common to every path, return theorem `node144aReturn`; reached by 6 paths (distinct ledger histories from the root), with 6 distinct fact sets, each a subtype `Node144aOutcome_<label>` (`Assembly/Residuals/Node144aOutcome.lean`) of the generic residual (`.toGeneric`), returned by `node144a<Label>Return`. The six subtypes replace the generic disjunct of `SelectedLedgerBoundaryResult` and `StrictSurplusBoundaryResult`.
- **Generic residual: facts on every path (81).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAbove`: Node `[19]`, above arm: the degree surplus exceeds the registered scale threshold.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .openPortSuppression`: `def:open-port-suppression`: the literal compatible family and its simultaneous delete-and-add graph.
  18. `K .openPortSuppressionSafe`: `lem:open-port-suppression-safe`: every vertex surviving a suppressible family of open ports has degree at least three.
  19. `K .singleOpenPortSuppressionWitness`: `lem:single-open-port-suppression-witness`: an open tight port has a simple shoulder-to-shoulder path in the vertex-deleted graph whose restored length is an accepted dyadic cycle length.
  20. `K .suppressedFamilyCriticalCycle`: `lem:suppressed-family-critical-cycle`: a nonempty suppressible family has an accepted suppressed cycle using added chords, and every such cycle expands to a forbidden source-cycle length.
  21. `K .sparseSlackSurplus`: Node `[126]`, `lem:sparse-slack-surplus`: the sparse slack identity `m = (3/2)n + (1/2)σ(G)`, cleared of division at the registered baseline.
  22. `K .activeSurplusFamily`: Node `[127]`, `lem:sparse-excess-port-extraction`, with the family half of `lem:surviving-active-family`: the excess selector `𝒫_exc` has exactly `σ(G)` members, every selected port has a centre strictly above the baseline and an endpoint exactly at it, and therefore carries exactly `δ − 1` shoulders.
  23. `K .sparsePortActivation`: Node `[128]`, `lem:sparse-port-activation`, clauses (a)--(d): at a selected port carrying a shoulder pair, the port carries the return path `R_p ⊆ G − c(p)x(p)` whose first edge after `x(p)` is a shoulder, an open port carries the suppression witness `Q_p ⊆ G − x(p)` whose restored length is accepted, and a ...
  24. `K .activeSurplusDemands`: Node `[125]`, `def:active-surplus-demands` with `lem:surviving-active-family`: the active family is the excess-port family, it has `σ(G)` members, and every member carries its canonical return path.
  25. `K .baselineSpineDemand`: Node `[129]`, `def:baseline-spine-demand` with `lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and `def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later surplus accounting is measured against, evaluated in both directions; the room an edge count above the cubic one buys ...
  26. `K .dependentPairFamily`: Node `[130]`, blocked arm of "blocker-free?": at G's canonical activation some scheduled pair has a nonempty blocker set over all six clauses of `def:surplus-blockers` (`Π_blk ≠ ∅`).
  27. `K .pairDegreeProfileFibres`: Node `[130]`, `lem:degree-profile-fibres` at G's pair family.
  28. `K .pairNoProfileObstruction`: Node `[130]`, blocker clause (d) absent at G's canonical activation.
  29. `K .pairNoResponseObstruction`: Node `[130]`, blocker clause (e) absent at G's canonical activation.
  30. `K .blockedPairNoExit`: Node `[132]`, blocker arm: the exact negation of `sparsePairExit`.
  31. `K .canonicalBlockerRoute`: Node `[132]`, blocker arm: no sparse surplus exit occurs, and the blocked pair of `[130]` at G's canonical activation has its canonical blocker `Φ_can(π) = min_≺ 𝖡𝗅𝗄(π)` of `def:canonical-blocker-ledger`.
  32. `K .canonicalPairLedger`: Nodes `[130]`--`[134]`, `def:sparse-pair-response`'s pair schedule with `def:canonical-blocker-ledger` and `lem:canonical-blocker-ledger-no-overcount`: `Π(𝒜₀)` has `C(σ(G),2)` members, and at every reading of the closed clause list of `def:surplus-blockers` the canonical charge is single-valued, so `Π_blk` and ...
  33. `K .sparseUpperEnvelope`: `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's `m ≤ 2n − 2` at its own `δ = 3`.
  34. `K .capacityTokenLedger`: Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with `lem:primitive-carrier-supply`, `def:capacity-token-ledger` with `lem:capacity-token-supply` and `lem:token-ledger-no-overcount`, and `def:same-token-patterns`: `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 3(δ−1)n`, the manuscript's `≤ 6n`, spent against the ...
  35. `K .blockedPairEntropySetup`: Node `[137]`: the exact capacity presentation and node-`[129]` baseline realization, assembled through `FactInputs.get` before the entropy split.
  36. `K .blockedPairEntropySandwich`: Node `[137]`, yes arm of the entropy count at every declared capacity presentation: `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)` for the ledger's free side.
  37. `K .roleFibrePartition`: Node `[137]`, `lem:exact-surplus-pair-charge-partition` with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and `thm:sharp-surplus-overload-audit` (b)--(c): at the object's capacity-token ledger, `C(𝒜₀,2)` decomposes exactly into `Π_free` and the class/token/role fibres, the class and subtype loads sum to ...
  38. `K .fibrePressure`: Nodes `[137]`--`[143]`, `lem:capacity-token-high-load` with `cor:forced-homogeneous-same-token-scale`, `thm:sharp-classwise-homogeneous-token-budget` (e) and `thm:sharp-surplus-overload-audit` (d): the object's *own* capacity-token ledger realizes the coupled high-load display `C(s,2) ≤ E + L_max|𝔗_cap|`, a role ...
  39. `K .sparsePressureOverload`: Node `[137]`, overload arm of `prop:single-graph-sparse-pressure-routing` (b) with `cor:coupled-single-graph-overload-budget` and `cor:quantified-homogeneous-class-overload`: some capacity-token ledger of the object has `D_all > 0`, and a role fibre absorbing its share over the `Q_st|𝔗_cap|` slots carries a ...
  40. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  41. `K .highCentreNormalForm`: Node `[67]`, the standing law: every high centre of the object has its neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` -- cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside `{h}` for a nonadjacent pair.
  42. `K .homogeneousBottleneckPattern`: Nodes `[140]`, `[142]`, `[143]`, the geometric audit of the selected overload: its token supports a role-homogeneous same-token `L_geom`-matching or `L_geom`-star, with every declared same-root connector configuration.
  43. `K .homogeneousCapsFail`: Node `[144]`, the other arm: the exact complement of the fixed caps.
  44. `K .bottleneckRouting`: Node `[144]`, `lem:same-token-bottleneck-routing` itself: the concrete homogeneous pattern in the current object's canonical capacity presentation yields a sparse-surplus exit or the common Type B fan-ledger entry.
  45. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  46. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  47. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  48. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  49. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  50. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  51. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  52. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  53. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  54. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  55. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  56. `K .edgeSurplusIdentity`: **Edge–surplus identity**: `2m = δ·n + σ`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 30).*
  57. `K .ceilSqrtAboveScale`: **`C + 1 ≤ ⌈√n⌉`.**  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 34).*
  58. `K .orderAboveScaleSquare`: **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 35).*
  59. `K .sixVertexExtremalEnvelope`: **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 36).*
  60. `K .highDegreePositive`: **At least one high-degree vertex**: `1 ≤ |H|`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 72).*
  61. `K .highDegreeSurplusCapacity`: **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every high vertex has all its neighbours among the `n − |H|` baseline vertices).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 73).*
  62. `K .canonicalCapacityExplicit`: **G's canonical capacity presentation is the explicit one**: the recorded blocker activation of G's active family on the node-`[19]` packing.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityRow`); `[20a]` item 83).*
  63. `K .canonicalTokenCount`: **The exact token count at the canonical presentation**: `|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`: `|𝔗_cap| = 4n + 3σ + 15ν`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 85).*
  64. `K .canonicalBlockedFreePartition`: **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 86).*
  65. `K .canonicalLedgerDeficit`: **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`, `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 87).*
  66. `K .pairCountDeficit`: **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 88).*
  67. `K .canonicalCertificationCriterion`: **The certification criterion at the canonical presentation**: its canonical certified ledger exists iff `|Π_free| ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 89).*
  68. `K .canonicalOverloadOfFits`: **If the free side fits `B`, the blocked side is overloaded**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load `> M₀` and carries an `L_geom` role-homogeneous matching or star.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 90).*
  69. `K .canonicalFreeExcessOfCapped`: **If every token carries load `≤ M₀`, the free side exceeds `B`**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 91).*
  70. `K .paperBudgetBound`: **The paper's budget at the canonical spine family fits the certification budget**: `E_paper ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 92).*
  71. `K .paperBudgetCertifies`: **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 93).*
  72. `K .pairCodeConfiguration`: **Where G sits in the pair-code chain**: either the `[137]`→`[143]` configuration holds at the canonical objects (blocked pair, `[137]` count, canonical pattern, overload, caps fail), or G's canonical first failure exists and yields the `[182]` residual, or the target defect of the canonical return system's obstruction coordinates, or that obstruction's handoff together with the Type B fan entry `[65]`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 94).*
  73. `K .freePairCountFails`: Node `[131]`, count fails at G's canonical objects, unconditionally: the same row and contract as on `[20a]` (`sparseExitFreePairCountRow`), run once at the top of `[130]`'s dependent arm (reuse, 2026-09-28).
  74. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  75. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  76. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  77. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  78. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  79. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  80. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  81. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes.** Label = class arm of `[139]`/`[141]` times arm of `[144]`'s handoff decision.
  - *`Node144aOutcome_windowHandoff`* ([139] yes (token in 𝔗_W, audit [140]); [144] handoff): 84 facts, the 81 common facts and:
    - `K .windowClassOverload`: Node `[139]`, yes arm: the overloading token of node `[137]` lies in `𝔗_W`, so the branch enters the window-incidence audit `[140]`.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_windowFails`* ([139] yes (token in 𝔗_W, audit [140]); [144] handoff fails): 85 facts, the 81 common facts and:
    - `K .windowClassOverload`: Node `[139]`, yes arm: the overloading token of node `[137]` lies in `𝔗_W`, so the branch enters the window-incidence audit `[140]`.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.
  - *`Node144aOutcome_remainderHandoff`* ([139] no, [141] yes (token in 𝔗_R, audit [142]); [144] handoff): 85 facts, the 81 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassOverload`: Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch enters the remainder-surplus audit `[142]`.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_remainderFails`* ([139] no, [141] yes (token in 𝔗_R, audit [142]); [144] handoff fails): 86 facts, the 81 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassOverload`: Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch enters the remainder-surplus audit `[142]`.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.
  - *`Node144aOutcome_primitiveHandoff`* ([139] no, [141] no (primitive token, audit [143]); [144] handoff): 86 facts, the 81 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassAbsent`: Node `[141]`, no arm: the selected overloading token lies in `𝔗_prim`, so that same witness enters `[143]`.
    - `K .primitiveClassOverload`: Node `[143]` entry: the overloading token is primitive.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_primitiveFails`* ([139] no, [141] no (primitive token, audit [143]); [144] handoff fails): 87 facts, the 81 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassAbsent`: Node `[141]`, no arm: the selected overloading token lies in `𝔗_prim`, so that same witness enters `[143]`.
    - `K .primitiveClassOverload`: Node `[143]` entry: the overloading token is primitive.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.

<a id="residual-172a"></a>

### Node [172a] (thm:main (iii), tex 354-358)

- **Configuration at G.** The first failed conditional graph-count inequality of lem:scale-additivity on the dense-packing branch, with its minimal same-scale barrier overlap.
- **Lean.** Generic residual `BlockedBarrierOverlapOutcome` (`Assembly/Residuals.lean`), the facts common to both paths; return theorem `blockedBarrierOverlapReturn`; reached by 2 paths (distinct ledger histories from the root), with 2 distinct fact sets, each its own subtype in `Assembly/Residuals/BlockedBarrierOverlapOutcome.lean` (below). Wired: `selectedCanonicalReplacementContinuation` takes the `[160]` arm (`DenseTauArm`) and returns `blockedBarrierOverlapSubtypesReturn`.
- **Common facts (90).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
  21. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  22. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  23. `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
  24. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  25. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  26. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  27. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  28. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  29. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  30. `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
  31. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  32. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  33. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  34. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  35. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  36. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  37. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  38. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  39. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  40. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  41. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  42. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  43. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  44. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  45. `K .coldCutStatesDistinct`: Node `[153]`, distinct-states arm: G's pinned cut states along each retained cold corridor are pairwise distinct up to the first failure.
  46. `K .coldHeavyEntryTerminal`: Node `[162]`, test arm: a retained corridor of G first failing at a heavy centre before its terminal segment is still terminal.
  47. `K .denseColdCorridorsTerminal`: Node `[162]`: every return corridor of the dense hot/cold pass is the terminal (F5) subcase because its selected shortest path lies in the induced-window-free normalized remainder.
  48. `K .coldFailureCycle`: `lem:cold-corridor-first-failure` (F1): a first failure that closes an accepted cycle is excluded at G by target avoidance.
  49. `K .coldFailureDefectRoute`: `lem:cold-corridor-first-failure` (ii): an (F2) pair of prefixes of one of G's corridors is a target-defective quotient.
  50. `K .coldFailureCompression`: `lem:cold-corridor-first-failure` (F3): a first failure that is a compression of G is excluded by uncompressibility.
  51. `K .coldHandoffTransfer`: `lem:cold-corridor-first-failure` (F4): an (F4) first failure transfers the corridor to its declared handoff interface of G.
  52. `K .coldFailureRouting`: `lem:cold-corridor-first-failure`: the routing (F1)--(F5) of G's first failures, with (F2) excluded on the (★) arm.
  53. `K .coldExchangeBound`: `def:cold-corridor-first-failure`: the `M_cold = Q_cold + 30` exchange bound on the retained corridor of every selected half-edge of G that reaches its successor stub before `Q_cold + 1` states.
  54. `K .coldGermCandidates`: Node `[153]`: a positive current-residual bounded-germ family.
  55. `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
  56. `K .absorbedGermSplit`: Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy — every selected branch-excess half-edge's first-failure support is subcubic (a charged candidate germ) or meets a heavy centre whose neighbours all sit at the threshold (node `[10]`).
  57. `K .absorbedGermFanData`: Node `[177]`, `lem:absorbed-germ-fan-data` (ii): every selected branch-excess half-edge outside node `[153]`'s exact subcubic candidate class meets a vertex of degree above the threshold, a heavy centre, and is decorated handoff fan data for Type B.
  58. `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
  59. `K .coldGermNoneDistinguishing`: Node `[154]`, the exact complement of `coldGermSomeDistinguishing`: every active configuration is silent (G3 or the equal-length table).
  60. `K .coldNeutralEqualLengthTerminal`: Node `[163]`, `def:neutral-equal-length-germ`: the marked terminal corridor piece and the canonical exact-cut-state representative selected for it have equal length and edge count, preserve the boundary profile and baseline, and have the same target response in every outside context.
  61. `K .coldGermRouted`: `lem:cold-bounded-germ-trichotomy`: every bounded configuration of G's extracted family is routed (G1, G2 or G3).
  62. `K .coldGermSilent`: `lem:cold-bounded-germ-trichotomy` (G3): the silent configurations of G's extracted family.
  63. `K .coldGermDistinguished`: `lem:cold-bounded-germ-trichotomy` (G2): the hit-distinguished configurations of G's extracted family.
  64. `K .coldGermRealized`: `lem:cold-bounded-germ-trichotomy`: the realized configurations of G's extracted family (G1 is closed, so none is hit-realized).
  65. `K .coldSameInterfaceTable`: `lem:cold-same-interface-table`: the finite same-interface table of G's silent configurations.
  66. `K .coldBranchClosed`: `thm:cold-branch-quantitative-closure`, local part: the local cold-terminal exclusion at G (no global terminal contradiction).
  67. `K .coldCanonicalNeutralConfiguration`: Node `[163]`, no-arm: no neutral zero-increment germ of the incoming extracted family has a graph-realized second strand; its `E` is therefore the canonical-replacement case of `[165]`--`[166]`.
  68. `K .coldCanonicalReplacementSwap`: Node `[165]`: for every neutral configuration, replacing `Q` by a distinct canonical representative `E` gives a baseline, target-avoiding graph with the same vertex and edge counts, while `E` strictly precedes `Q` in the fixed canonical piece order.
  69. `K .coldCanonicalReplacementTrivial`: Node `[166]`: refined minimality forces every neutral configuration's canonical replacement to be the corridor piece itself, `E = Q`.
  70. `K .blockedClassMember`: Node `[169]`, `def:blocked-class`: on the trivial neutral-configuration residual the object's own labelled skeleton lies in the blocked class `𝓑(𝒫)` of the fixed maximal packing (near-cubic, windows present, no accepted cycle through a window), and `card 𝓑(𝒫) ≤ skeletonBudget`.
  71. `K .blockedBarrierOverlap`: Node `[170]`, the exact complement (`lem:barrier-failure-overlap`): the conditional saving fails at a specific window, scale, and barrier row; the retained value is the actual oversized conditional fibre, before the overlap lemma constructs its support.
  72. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  73. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  74. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  75. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  76. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  77. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  78. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  79. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  80. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  81. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  82. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  83. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  84. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  85. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  86. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  87. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  88. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  89. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  90. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes** (one per distinct fact set; the two paths differ only by the arm of the `[160]` rate split through which the dense-packing residual enters the dense hot/cold pass `[162]`; each subtype implies the generic residual by `.toGeneric`).
  - `BlockedBarrierOverlapOutcome_DeficiencyAtOrAbove`, `[160]` first test no (`τ(θ) ≥ 1/4`); return theorem `blockedBarrierOverlapReturn_DeficiencyAtOrAbove`. Extra facts:
    72. `K .denseDeficiencyAtOrAbove`: Node `[160]`, first test, no arm: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
    - Total: 91 facts.
  - `BlockedBarrierOverlapOutcome_DeficiencyBelowRateFails`, `[160]` first test yes (`τ(θ) < 1/4`), second test no (private-carrier rate fails); return theorem `blockedBarrierOverlapReturn_DeficiencyBelowRateFails`. Extra facts:
    72. `K .denseDeficiencyBelow`: Node `[160]`, first test, yes arm: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison, the `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance.
    73. `K .route8RateFails`: Node `[160]`, second test, no arm: the complement of the private-carrier rate reading (`3/13 ≤ τ`), the manuscript's delicate density interval, carried as its own branch.
    - Total: 92 facts.

<a id="residual-182"></a>

### Node [182] (thm:main (iv), tex 359-363)

- **Configuration at G.** The first failed coverage implication of [178], [179] or [180] on the strict-surplus pair-code chain.
- **Lean.** `PairConditionalFactorizationOutcome` (`Assembly/Residuals.lean`); return theorem `pairConditionalFactorizationReturn`; reached by 6 paths (distinct ledger histories from the root) with 6 distinct fact sets, one subtype each in `Assembly/Residuals/PairConditionalFactorizationOutcome.lean`.
- **Generic residual: facts common to all six paths (71).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAbove`: Node `[19]`, above arm: the degree surplus exceeds the registered scale threshold.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .openPortSuppression`: `def:open-port-suppression`: the literal compatible family and its simultaneous delete-and-add graph.
  18. `K .openPortSuppressionSafe`: `lem:open-port-suppression-safe`: every vertex surviving a suppressible family of open ports has degree at least three.
  19. `K .singleOpenPortSuppressionWitness`: `lem:single-open-port-suppression-witness`: an open tight port has a simple shoulder-to-shoulder path in the vertex-deleted graph whose restored length is an accepted dyadic cycle length.
  20. `K .suppressedFamilyCriticalCycle`: `lem:suppressed-family-critical-cycle`: a nonempty suppressible family has an accepted suppressed cycle using added chords, and every such cycle expands to a forbidden source-cycle length.
  21. `K .sparseSlackSurplus`: Node `[126]`, `lem:sparse-slack-surplus`: the sparse slack identity `m = (3/2)n + (1/2)σ(G)`, cleared of division at the registered baseline.
  22. `K .activeSurplusFamily`: Node `[127]`, `lem:sparse-excess-port-extraction`, with the family half of `lem:surviving-active-family`: the excess selector `𝒫_exc` has exactly `σ(G)` members, every selected port has a centre strictly above the baseline and an endpoint exactly at it, and therefore carries exactly `δ − 1` shoulders.
  23. `K .sparsePortActivation`: Node `[128]`, `lem:sparse-port-activation`, clauses (a)--(d): at a selected port carrying a shoulder pair, the port carries the return path `R_p ⊆ G − c(p)x(p)` whose first edge after `x(p)` is a shoulder, an open port carries the suppression witness `Q_p ⊆ G − x(p)` whose restored length is accepted, and a ...
  24. `K .activeSurplusDemands`: Node `[125]`, `def:active-surplus-demands` with `lem:surviving-active-family`: the active family is the excess-port family, it has `σ(G)` members, and every member carries its canonical return path.
  25. `K .baselineSpineDemand`: Node `[129]`, `def:baseline-spine-demand` with `lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and `def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later surplus accounting is measured against, evaluated in both directions; the room an edge count above the cubic one buys ...
  26. `K .sparseUpperEnvelope`: `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's `m ≤ 2n − 2` at its own `δ = 3`.
  27. `K .pairOverlapFirstFailure`: Node `[178]`: the route-independent least failed pair extension, with the failed pair's canonical connected response support.
  28. `K .mixedSparseSpineDependence`: Node `[131]`, `lem:mixed-sparse-spine-dependence` at G's canonical spine family and activation: a non-independent mixed family gives a sparse exit or a type-(d)/(e) blocker.
  29. `K .exactCubicBaselineBudget`: Node `[131]`, the two-sided exact cubic baseline budget at the current residual's order and registered baseline.
  30. `K .incrementalSkeletonRoom`: Node `[131]`, the incremental skeleton room above the exact cubic baseline and its surplus-slack bound.
  31. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  32. `K .pairOverlapSystem`: Node `[178]`: the exact pair-response conditional fibre, realized joint states, realizing orders, obstructions, overlaps, and support unions.
  33. `K .pairConditionalFactorizationResidual`: Node `[182]`: the exact retained residual where one of the paper's `[178]`--`[180]` implications is not exhaustive.
  34. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  35. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  36. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  37. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  38. `K .bridgeless`: `lem:bridgeless` at G.  *Hoisted (entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`); `[20a]` item 20).*
  39. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  40. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  41. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  42. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  43. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  44. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  45. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  46. `K .edgeSurplusIdentity`: **Edge–surplus identity**: `2m = δ·n + σ`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 30).*
  47. `K .ceilSqrtAboveScale`: **`C + 1 ≤ ⌈√n⌉`.**  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 34).*
  48. `K .orderAboveScaleSquare`: **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 35).*
  49. `K .sixVertexExtremalEnvelope`: **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 36).*
  50. `K .highDegreePositive`: **At least one high-degree vertex**: `1 ≤ |H|`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 72).*
  51. `K .highDegreeSurplusCapacity`: **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every high vertex has all its neighbours among the `n − |H|` baseline vertices).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 73).*
  52. `K .canonicalCapacityExplicit`: **G's canonical capacity presentation is the explicit one**: the recorded blocker activation of G's active family on the node-`[19]` packing.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityRow`); `[20a]` item 83).*
  53. `K .canonicalTokenCount`: **The exact token count at the canonical presentation**: `|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`: `|𝔗_cap| = 4n + 3σ + 15ν`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 85).*
  54. `K .canonicalBlockedFreePartition`: **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 86).*
  55. `K .canonicalLedgerDeficit`: **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`, `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 87).*
  56. `K .pairCountDeficit`: **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 88).*
  57. `K .canonicalCertificationCriterion`: **The certification criterion at the canonical presentation**: its canonical certified ledger exists iff `|Π_free| ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 89).*
  58. `K .canonicalOverloadOfFits`: **If the free side fits `B`, the blocked side is overloaded**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load `> M₀` and carries an `L_geom` role-homogeneous matching or star.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 90).*
  59. `K .canonicalFreeExcessOfCapped`: **If every token carries load `≤ M₀`, the free side exceeds `B`**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 91).*
  60. `K .paperBudgetBound`: **The paper's budget at the canonical spine family fits the certification budget**: `E_paper ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 92).*
  61. `K .paperBudgetCertifies`: **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 93).*
  62. `K .pairCodeConfiguration`: **Where G sits in the pair-code chain**: either the `[137]`→`[143]` configuration holds at the canonical objects (blocked pair, `[137]` count, canonical pattern, overload, caps fail), or G's canonical first failure exists and yields the `[182]` residual, or the target defect of the canonical return system's obstruction coordinates, or that obstruction's handoff together with the Type B fan entry `[65]`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 94).*
  63. `K .freePairCountFails`: Node `[131]`, count fails at G's canonical objects.  On the free side it is the no-arm of `[131]`'s decision; on the blocked side the same row and contract as on `[20a]` (`sparseExitFreePairCountRow`) runs once at the top of `[130]`'s dependent arm (reuse, 2026-09-28).  Formerly an extra fact of the three free subtypes only.
  64. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  65. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  66. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  67. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  68. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  69. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  70. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  71. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes, one per distinct fact set (6).**  Each is `PairConditionalFactorizationOutcome ∧` its extra facts, with `.toGeneric` and a return theorem `pairConditionalFactorizationReturn_<label>` (one `get` per fact).  The side is the entry into the pair-code chain: free = `[130]` blocker-free arm and `[131]` free-pair count fails; blocked = `[130]` blocked arm with no (d)/(e) blocker, `[132]` no sparse exit, `[134]`--`[136]` token ledger and `[137]` blocked-side count fails.  The arm is the first failed implication: `[178]` factorization, `[179]` realizability, `[180]` increment coverage.
  - `PairConditionalFactorizationOutcome_freeFactorizationFails` (74 facts): the 71 above, plus
    - `K .independentPairFamily`
    - `K .freePairCodeUnrealized`
    - `K .pairFactorizationFails`
  - `PairConditionalFactorizationOutcome_freeRealizabilityFails` (77 facts): the 71 above, plus
    - `K .independentPairFamily`
    - `K .freePairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairRealizabilityFails`
  - `PairConditionalFactorizationOutcome_freeIncrementFails` (80 facts): the 71 above, plus
    - `K .independentPairFamily`
    - `K .freePairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairSystemRealizability`
    - `K .pairSystemNoEarlyOutcome`
    - `K .pairSerialDemandSystem`
    - `K .pairIncrementFails`
  - `PairConditionalFactorizationOutcome_blockedFactorizationFails` (83 facts): the 71 above, plus
    - `K .dependentPairFamily`
    - `K .pairDegreeProfileFibres`
    - `K .pairNoProfileObstruction`
    - `K .pairNoResponseObstruction`
    - `K .blockedPairNoExit`
    - `K .canonicalBlockerRoute`
    - `K .canonicalPairLedger`
    - `K .capacityTokenLedger`
    - `K .blockedPairEntropySetup`
    - `K .blockedPairCountFails`
    - `K .blockedPairCodeUnrealized`
    - `K .pairFactorizationFails`
  - `PairConditionalFactorizationOutcome_blockedRealizabilityFails` (86 facts): the 71 above, plus
    - `K .dependentPairFamily`
    - `K .pairDegreeProfileFibres`
    - `K .pairNoProfileObstruction`
    - `K .pairNoResponseObstruction`
    - `K .blockedPairNoExit`
    - `K .canonicalBlockerRoute`
    - `K .canonicalPairLedger`
    - `K .capacityTokenLedger`
    - `K .blockedPairEntropySetup`
    - `K .blockedPairCountFails`
    - `K .blockedPairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairRealizabilityFails`
  - `PairConditionalFactorizationOutcome_blockedIncrementFails` (89 facts): the 71 above, plus
    - `K .dependentPairFamily`
    - `K .pairDegreeProfileFibres`
    - `K .pairNoProfileObstruction`
    - `K .pairNoResponseObstruction`
    - `K .blockedPairNoExit`
    - `K .canonicalBlockerRoute`
    - `K .canonicalPairLedger`
    - `K .capacityTokenLedger`
    - `K .blockedPairEntropySetup`
    - `K .blockedPairCountFails`
    - `K .blockedPairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairSystemRealizability`
    - `K .pairSystemNoEarlyOutcome`
    - `K .pairSerialDemandSystem`
    - `K .pairIncrementFails`

<a id="residual-186"></a>

### Node [186] (thm:main (v), tex 364-368)

- **Configuration at G.** The visible-entry route-8 residual after [181], [183]-[185], with the joint balances of lem:typeA-unified-joint-balance.
- **Lean.** `Route8JointBalanceOutcome` (`Assembly/Residuals.lean`, the generic residual: the 98 keys common to every path); return theorem `route8JointBalanceReturn`, called once, at `Assembly/RouteEight/Local.lean` (`selectedRouteEightUnifiedResidual`, the quotient-free arm after `[123]`, `[181]`, `[183]`--`[185]`). The 750 paths from `selectedLedgerBoundary` carry 750 distinct fact sets (probe of the elaborated `known` at every call site, R06, 2026-09-27; B-chain count corrected at integration; 250 of the 1000 paths removed by the two lane-entry closures of Closed from G's facts, `[146]` on `[160]`'s first complement and `[53]` on the `[161]` dense residual), and form an exact product of arm blocks: `Route8JointBalanceOutcome_product := Route8JointBalanceOutcome ∧ Route8LaneEntry ∧ NetChargeContinuation` (`Assembly/Residuals/Route8JointBalanceOutcome.lean`; `.toGeneric`; return theorem `route8JointBalanceProductReturn`, parameterised by the arm blocks, each built by its block's `.ret` with one `get` per key). The factors are those of `Route8QuotientOutcome` (same composition, same incoming ledgers); the blocks are shared (`Assembly/Residuals/Route8Blocks.lean`). Every path is the 88 common keys plus exactly one block per factor, and every one of the `15 × 50 = 750` combinations occurs (`Route8LaneEntry = (Route8LanePrefix ∧ EntropyArm) ∨ (Route8LanePrefixBlock_unrealizedDenseBelow ∧ EntropyArmLow)`, `15 = 3·4 + 3`). Totals: 100 to 157 facts. Wired: the return site calls `route8JointBalanceProductReturn` with its `Route8Arms` argument.
- **Facts carried (98).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .largeBudgetResidual`: Node `[53]`, no arm — node `[55]`, Residual C: the joint package still fits the skeleton budget, and the branch is the large-budget residual.
  38. `K .netDeficiencyCap`: Node `[56]`: exact cleared finite form of the large-budget net-deficiency cap.
  39. `K .route8Rate`: Node `[120]`: the private-carrier rate reading of the census alone, `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13` with the `o(|R|)` allowance, `rem:route8-carrier-margin`), read from the arm's density fact.
  40. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  41. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  42. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  43. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  44. `K .coldFailureCycle`: `lem:cold-corridor-first-failure` (F1): a first failure that closes an accepted cycle is excluded at G by target avoidance.
  45. `K .coldFailureCompression`: `lem:cold-corridor-first-failure` (F3): a first failure that is a compression of G is excluded by uncompressibility.
  46. `K .coldHandoffTransfer`: `lem:cold-corridor-first-failure` (F4): an (F4) first failure transfers the corridor to its declared handoff interface of G.
  47. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  48. `K .typeBAbsorbedCharge`: Node `[177]`: every selected half-edge outside the subcubic candidates has its pinned absorbed Type B support, charged to the surplus of its centre.
  49. `K .highCentreNormalForm`: Node `[67]`, the standing law: every high centre of the object has its neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` -- cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside `{h}` for a nonadjacent pair.
  50. `K .sameCenterOpenPortCompatibility`: Node `[69]`, `lem:same-center-open-port-compatibility`.
  51. `K .triangularShoulderCompletion`: `lem:triangular-shoulder-completion`: the four completion-incidence conclusions for every triangular port at a heavy centre.
  52. `K .triangularPortReturn`: `lem:triangular-port-return`: deleting a triangular port edge leaves a simple return through a shoulder; its restored cycle is forbidden, and the shoulder tail contains a noncentral completion incidence.
  53. `K .route8BasinBurden`: Node `[112]`: the selected route-`8` residual carries the basin-burden lower side of `lem:typeA-route8-burden`.
  54. `K .route8CarrierCore`: Node `[114]`: canonical minimal carrier-core facts for every declared reading of the selected route-`8` residual.
  55. `K .typeBBridgeMass`: Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts for certificate residuals, overlap obstructions, and grouped decorated envelope residuals.
  56. `K .typeBBridgeSublinear`: `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been extracted into the Type A ledger, the remaining Type B bridge residual mass is paid by the assigned high-centre surplus.
  57. `K .route8UnifiedNegative`: Node `[123]`, `def:typeA-unified-negative`: the canonical collection of exactly the zero-surplus negative supports which produce no decorated Type B handoff, together with its cleared total deficit.
  58. `K .typeAExclusion`: Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the minimal counterexample: every negative zero-surplus canonical piece of a maximal packing's remainder carries an exit-`(4)` witness for a routed load, an admissible silent-core residual profile, or a produced decorated Type B handoff.
  59. `K .typeBBridgeReduction`: `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap` (`def:typeB-bridge-statements`), in the contrapositive the branch carries: every negative positive-surplus canonical piece of a maximal packing's remainder carries the B2 disjoint ledger with strictly negative remaining scaled core charge — every ...
  60. `K .route8PiecesClassified`: `thm:branch-kill`'s all-pieces classification: every negative piece of the canonical decomposition is silent-first when it has no ambient surplus, and is a Type B bridge component when it has positive surplus.
  61. `K .route8ExtractedEntryCensus`: `def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the extracted route-8 cores of the Type B bridge pieces (node `[123]`): the exact per-entry census of `lem:typeB-bridge-with-route8-core`'s collection `𝒜_X`.
  62. `K .typeBSublinearLedger`: `prop:typeB-bridge-sublinear`'s hypotheses, tested: the flat off-centre pair at every negative positive-surplus canonical piece and the grouped fan-assignment data at the negative zero-surplus handoff pieces.
  63. `K .route8UnifiedDeficit`: Node `[123]`, `lem:typeA-unified-deficit`: the unified collection carries the whole large-budget deficit — `|R| ≤ s·D̃_A + s·|∂R| + 2F·s·T(n)`.
  64. `K .route8QuotientFree`: The quotient-freeness of the unified census (tex 15360-15364): no entry's selected basin carries a nontrivial target-complete response quotient.
  65. `K .route8UnifiedEntryCensus`: Node `[123]`, `def:typeA-unified-entries` with `lem:typeA-unified-carriers` and `def:typeA-pressure-ledger`: every unified entry has its selected basin, at least two essential incidences, and is a route-8 entry with no exit-(4) witness or a target-defect entry through alternative (a) with its witness.
  66. `K .route8PeelingDescent`: Node `[123]`, `thm:large-budget-route8-only`'s procedure on the object-level census: from the empty peeling, target-defect peels (`lem:typeA-pressure-is-exit4-peel`, `lem:typeA-exit4-finite-descent`) reach a stage with a true two-carrier entry of the peeled ledger or a stage where the stage rate fails ...
  67. `K .route8StageRateFailed`: Node `[123]`, the repaired failed-stage arm: a recorded target-defect peel chain, the exact partition of the full ledger into reduced and peeled entries, both deficit inequalities, and failure of the sufficient stage rate.
  68. `K .route8DemandLedger`: `def:typeA-pressure-ledger` at the failed-rate stage: the maximal pinned 2/3-demand ledger over the unified collection, with its no-overcount counts and the canonical demand records of the unpaid target-defect entries.
  69. `K .route8DemandAbsorption`: Node `[123]`, `def:typeA-pressure-absorbers` with `lem:typeA-pressure-absorber-no-overcount`: on every committed maximal 2/3-demand ledger, a type-(A1)/(A2) absorption of its demand units — fresh single-use boundary incidences on the absorbed set and a disjoint type-(A2) dependence set — with the subtraction-free ...
  70. `K .route8DemandUnitCount`: The number of actual demand units equals the external demand defect.
  71. `K .route8OpenBoundarySaturated`: The (O2) maximal-absorption consequence on the same demand units.
  72. `K .route8WindowBlockers`: Node `[123]`, `def:typeA-open-window-blocker` with `lem:typeA-open-window-blocker-count`: every open demand unit of the committed absorption is assigned a packed window through a boundary incidence of its component support, and the open demand is exactly the window-blocker load partition `𝖯_open = Σ_P B_open(P)`.
  73. `K .windowShadowHitCycle`: The actual corridor/window cycle witnessing a recorded shadow hit.
  74. `K .windowShadowHitExcluded`: Selection excludes every recorded shadow hit on the same object.
  75. `K .route8UnpaidTwoCarrier`: Node `[181]`, (168.1): every unpaid entry of a maximal demand ledger is two-support.
  76. `K .route8UnpaidExitFourResidual`: Node 182: one-entry augmentation exhausts every unpaid entry with three private carriers; the no-exit-(4) arm routes to node 124, and the sole survivor consists of two-carrier unpaid entries with canonical exit-(4) witnesses.
  77. `K .route8UnifiedVisibleResidual`: Node `[184]`, `lem:typeA-unified-visible-ownership`: on the exact post-`[181]` unified entry family, every retained load is visibly owned by an actual receiver-entry return.
  78. `K .route8UnifiedVisibleOverload`: Node `[185]`, `lem:typeA-unified-visible-overload`: every retained visible excess entry lies at a receiver with an actually overloaded completion port.
  79. `K .route8JointBalance`: Node `[186]`, `lem:typeA-unified-joint-balance`: the failed peel rate, unified deficit, committed maximal demand ledger, and maximal type-(A1) absorption are read simultaneously.
  80. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  81. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  82. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  83. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  84. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  85. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  86. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  87. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  88. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  89. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  90. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  91. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  92. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  93. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  94. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  95. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  96. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  97. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  98. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Product of arm blocks (keys beyond the 98 common facts).**
  Structure: `Route8LaneEntry (15 = 3 prefix × 4 entropy + [161] × 3 low entropy; the `[146]` prefix and `[161]` × high entropy are closed, see "Closed from G's facts") × NetChargeContinuation`; `NetChargeContinuation = TypeALane ∨ TypeBHighSurplusLane` (50 = 2·22 + 6; the absorbed lane is closed at `[173]` and the deficit-holds choice at `[124]`, see "Closed from G's facts"); `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry (2) ∧ TypeAArm (22)`; `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour (3) ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour (3) ∧ Route8DeficitBlock_fails) ∨ TypeAArmBlock_dischargedRetest`; `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`; `BChain = BChainEntryBlock ∧ BChainFanCertificate (6)`, `BChainFanCertificate = (BChainFanBlock_heavyCentre ∧ (residual ∨ b2Choice ∨ overlapObstruction)) ∨ (BChainFanBlock_degreeFour ∧ (residual ∨ degreeFourClosed ∨ degreeFourOverlap))`.
  - Prefix factor (one of 4; `Route8LanePrefix` is the first three, `Route8LanePrefixBlock_unrealizedDenseBelow` enters only with `EntropyArmLow`):
    - `Route8LanePrefixBlock_realizedColdBelow` (2): window package realized; cold route-8 rate below (`nearCubicRealized` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` (6): window package realized; cold route-8 rate at or above, density cap (`nearCubicRealized` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .densityCap`
      - `K .windowPackageRealized`
      - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
      - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow`: closed at `[146]` (`θ < 1/78` forces `τ(θ) < 1/4`; see Closed from G's facts).
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` (7): window package unrealized; dense deficiency at or above; cold route-8 rate at or above, density cap (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .denseDeficiencyAtOrAbove`
      - `K .densityCap`
      - `K .windowPackageUnrealized`
      - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
      - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
    - `Route8LanePrefixBlock_unrealizedDenseBelow` (2): window package unrealized; dense deficiency below (`nearCubicUnrealized` → `nearCubicLargeBudgetDenseRate`)
      - `K .denseDeficiencyBelow`
      - `K .windowPackageUnrealized`
  - Entropy factor `EntropyArm` (one of 4):
    - `EntropyArmBlock_high` (3): remainder entropy high
      - `K .entropyCapBound`
      - `K .entropyPackageDemand`
      - `K .remainderEntropyHigh`
    - `EntropyArmBlock_lowNonrepetitive` (2): remainder entropy low; local type coordinate non-repetitive
      - `K .localTypeCoordinateNonrepetitive`
      - `K .remainderEntropyLow`
    - `EntropyArmBlock_lowRepetitiveWedgeFree` (4): remainder entropy low; local type coordinate repetitive; dominant rooted type wedge-free
      - `K .dominantRootedType`
      - `K .dominantRootedTypeWedgeFree`
      - `K .localTypeCoordinateRepetitive`
      - `K .remainderEntropyLow`
    - `EntropyArmBlock_lowRepetitiveWedge` (5): remainder entropy low; local type coordinate repetitive; dominant rooted wedge type
      - `K .dominantRootedType`
      - `K .dominantRootedWedgeType`
      - `K .independentObstructionTranslates`
      - `K .localTypeCoordinateRepetitive`
      - `K .remainderEntropyLow`
  - Continuation lanes:
    - `NetChargeLaneBlock_typeALowSurplus` (11): Type A low-surplus lane
      - `K .negativeSupport`
      - `K .netChargeCap`
      - `K .netChargeNegative`
      - `K .typeABoundedSupport`
      - `K .typeAExitFourFiniteDescent`
      - `K .typeALowSurplus`
      - `K .typeAPortReturn`
      - `K .typeAReceiverRouting`
      - `K .typeASaturatedExitEntry`
      - `K .typeASaturatedReceiver`
      - `K .typeASupport`
    - `NetChargeLaneBlock_typeBHighSurplus` (5): Type B high-surplus lane
      - `K .negativeSupport`
      - `K .netChargeCap`
      - `K .netChargeNegative`
      - `K .typeBAssignedSupport`
      - `K .typeBHighSurplus`
  - Type A entry `TypeAEntry` (one of 2):
    - `TypeAEntryBlock_visible` (4): visible entry
      - `K .typeAExitOneFree`
      - `K .typeAExitThreeFree`
      - `K .typeAExitTwoFree`
      - `K .typeAVisibleEntry`
    - `TypeAEntryBlock_noVisible` (2): no visible entry
      - `K .typeANoVisibleEntry`
      - `K .typeAVisibleFirstExcess`
  - Type A continuation arm (one of 3 kinds):
    - `TypeAArmBlock_decorated` (6): decorated handoff, then `TypeAExitFour` and `BChain`
      - `K .typeAExitFiveFree`
      - `K .typeAExitSevenEnvelope`
      - `K .typeAExitSevenHandoff`
      - `K .typeAExitSixFree`
      - `K .typeASaturatedHandoffExitFourFree`
      - `K .typeBDecoratedAssignedSupport`
    - `TypeAArmBlock_route8Residual` (5): route-8 residual, then `TypeAExitFour` and `Route8DeficitBlock_fails`
      - `K .route8ResidualProfile`
      - `K .typeAExitFiveFree`
      - `K .typeAExitSevenFree`
      - `K .typeAExitSixFree`
      - `K .typeASaturatedHandoffExitFourFree`
    - `TypeAArmBlock_dischargedRetest` (4): exit-four discharged retest
      - `K .typeAExitFourPeeled`
      - `K .typeAExitFourReceiverDischarged`
      - `K .typeAPeeledUnsaturatedDischarge`
      - `K .typeASaturatedHandoffExitFour`
  - Type A exit four `TypeAExitFour` (one of 3):
    - `TypeAExitFourBlock_absent` (1): absent
      - `K .typeAExitFourAbsent`
    - `TypeAExitFourBlock_peeledVisible` (7): peeledVisible
      - `K .typeAExitFourPeeled`
      - `K .typeAPeeledExitOneFree`
      - `K .typeAPeeledExitThreeFree`
      - `K .typeAPeeledExitTwoFree`
      - `K .typeAPeeledSaturatedReceiver`
      - `K .typeAPeeledVisibleEntry`
      - `K .typeASaturatedHandoffExitFour`
    - `TypeAExitFourBlock_peeledNoVisible` (5): peeledNoVisible
      - `K .typeAExitFourPeeled`
      - `K .typeAPeeledNoVisibleEntry`
      - `K .typeAPeeledSaturatedReceiver`
      - `K .typeAPeeledSilentExcess`
      - `K .typeASaturatedHandoffExitFour`
  - Route-8 deficit (one block; the deficit-holds arm is closed at `[124]`, see Closed from G's facts):
    - `Route8DeficitBlock_fails` (1): deficit fails
      - `K .route8LargeBudgetDeficitFails`
  - B-chain `BChain`:
    - `BChainEntryBlock` (7): carried on every B-chain arm
      - `K .compatiblePairFanClosure`
      - `K .compatiblePairTypeBRouting`
      - `K .fanCertificateCap`
      - `K .fanClosedPortTypeBRouting`
      - `K .typeBExclusionResidual`
      - `K .typeBFanEntry`
      - `K .typeBRoute8Entry`
    - `BChainFanBlock_degreeFour` (2): fan arm (one of 2)
      - `K .typeBFanDegreeFourCentres`
      - `K .typeBFanDegreeFourProfile`
    - `BChainFanBlock_heavyCentre` (6): fan arm (one of 2)
      - `K .triangularCrossShoulder`
      - `K .triangularFanCore`
      - `K .triangularFirstLanding`
      - `K .triangularPortTypeBRouting`
      - `K .typeBFanHeavyCentre`
      - `K .typeBFanLocalDichotomy`
    - `BChainCertificateBlock_residual` (2): certificate arm (one of 5)
      - `K .fanCertificateResidual`
      - `K .fanCertificateResidualMass`
    - `BChainCertificateBlock_b2Choice` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBB2Choice`
      - `K .typeBDirectCycleFree`
      - `K .typeBDisjointLedger`
      - `K .typeBExcluded`
      - `K .typeBHybridEntry`
    - `BChainCertificateBlock_degreeFourClosed` (5): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDegreeFourClosed`
      - `K .typeBDegreeFourLedger`
      - `K .typeBDirectCycleFree`
      - `K .typeBHybridEntry`
    - `BChainCertificateBlock_degreeFourOverlap` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDegreeFourOverlap`
      - `K .typeBDirectCycleFree`
      - `K .typeBGlobalLocalBridge`
      - `K .typeBHybridEntry`
      - `K .typeBOverlapObstructionMass`
    - `BChainCertificateBlock_overlapObstruction` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDirectCycleFree`
      - `K .typeBGlobalLocalBridge`
      - `K .typeBHybridEntry`
      - `K .typeBOverlapObstruction`
      - `K .typeBOverlapObstructionMass`

<a id="residual-187-pair-type-b"></a>

### Node [187] ([179]/[180] Type B entry) (thm:main (vi), tex 369-378)

- **Configuration at G.** A Type B entry produced by the [179] or [180] pair-system outcome, with its strict-surplus and sparse-survivor ancestry.
- **Lean.** Generic residual `PairTypeBOutcome` (`Assembly/Residuals.lean`), return theorems `pairTypeBSystemReturn`, `pairTypeBIncrementReturn`; subtypes and their return theorems in `Assembly/Residuals/PairTypeBOutcome.lean`.  Reached by 4 paths (the pair-code chain entered from the free side of [131], `selectedPairCodeChainIndependent`, or of [137], `selectedPairCodeChainDependent`, times the chain's two Type B arms), with 4 distinct fact sets, hence 4 subtypes; each return site calls its subtype's return theorem, and the boundary carries the disjunction of the 4 subtypes.
- **Generic residual: common facts (75), then its own arm as a disjunction.**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAbove`: Node `[19]`, above arm: the degree surplus exceeds the registered scale threshold.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .openPortSuppression`: `def:open-port-suppression`: the literal compatible family and its simultaneous delete-and-add graph.
  18. `K .openPortSuppressionSafe`: `lem:open-port-suppression-safe`: every vertex surviving a suppressible family of open ports has degree at least three.
  19. `K .singleOpenPortSuppressionWitness`: `lem:single-open-port-suppression-witness`: an open tight port has a simple shoulder-to-shoulder path in the vertex-deleted graph whose restored length is an accepted dyadic cycle length.
  20. `K .suppressedFamilyCriticalCycle`: `lem:suppressed-family-critical-cycle`: a nonempty suppressible family has an accepted suppressed cycle using added chords, and every such cycle expands to a forbidden source-cycle length.
  21. `K .sparseSlackSurplus`: Node `[126]`, `lem:sparse-slack-surplus`: the sparse slack identity `m = (3/2)n + (1/2)σ(G)`, cleared of division at the registered baseline.
  22. `K .activeSurplusFamily`: Node `[127]`, `lem:sparse-excess-port-extraction`, with the family half of `lem:surviving-active-family`: the excess selector `𝒫_exc` has exactly `σ(G)` members, every selected port has a centre strictly above the baseline and an endpoint exactly at it, and therefore carries exactly `δ − 1` shoulders.
  23. `K .sparsePortActivation`: Node `[128]`, `lem:sparse-port-activation`, clauses (a)--(d): at a selected port carrying a shoulder pair, the port carries the return path `R_p ⊆ G − c(p)x(p)` whose first edge after `x(p)` is a shoulder, an open port carries the suppression witness `Q_p ⊆ G − x(p)` whose restored length is accepted, and a ...
  24. `K .activeSurplusDemands`: Node `[125]`, `def:active-surplus-demands` with `lem:surviving-active-family`: the active family is the excess-port family, it has `σ(G)` members, and every member carries its canonical return path.
  25. `K .baselineSpineDemand`: Node `[129]`, `def:baseline-spine-demand` with `lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and `def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later surplus accounting is measured against, evaluated in both directions; the room an edge count above the cubic one buys ...
  26. `K .sparseUpperEnvelope`: `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's `m ≤ 2n − 2` at its own `δ = 3`.
  27. `K .pairOverlapFirstFailure`: Node `[178]`: the route-independent least failed pair extension, with the failed pair's canonical connected response support.
  28. `K .mixedSparseSpineDependence`: Node `[131]`, `lem:mixed-sparse-spine-dependence` at G's canonical spine family and activation: a non-independent mixed family gives a sparse exit or a type-(d)/(e) blocker.
  29. `K .exactCubicBaselineBudget`: Node `[131]`, the two-sided exact cubic baseline budget at the current residual's order and registered baseline.
  30. `K .incrementalSkeletonRoom`: Node `[131]`, the incremental skeleton room above the exact cubic baseline and its surplus-slack bound.
  31. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  32. `K .pairOverlapSystem`: Node `[178]`: the exact pair-response conditional fibre, realized joint states, realizing orders, obstructions, overlaps, and support unions.
  33. `K .pairConditionalFactorization`: Node `[178]`, factorizing arm: the exact retained pair-response system satisfies the manuscript's conditional product and concatenation clauses.
  34. `K .pairFailureOverlap`: Node `[178]`, `lem:pair-failure-overlap`: a minimal pair-code defect in the current conditional fibre whose canonical overlap support is connected.
  35. `K .pairDemandReturns`: Node `[179]`: the two literal demands of the failed pair, their canonical port returns, the connected `X_π ∪ R_p ∪ R_q` connector, and the graph-derived return-length bound used in `D_sp`.
  36. `K .pairSystemRealizability`: Node `[179]`: the exact obstruction satisfies one of the five outcomes of `lem:pair-system-realizability`.
  37. `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  38. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  39. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  40. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  41. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  42. `K .bridgeless`: `lem:bridgeless` at G.  *Hoisted (entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`); `[20a]` item 20).*
  43. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  44. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  45. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  46. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  47. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  48. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  49. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  50. `K .edgeSurplusIdentity`: **Edge–surplus identity**: `2m = δ·n + σ`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 30).*
  51. `K .ceilSqrtAboveScale`: **`C + 1 ≤ ⌈√n⌉`.**  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitBudgetRow`); `[20a]` item 34).*
  52. `K .orderAboveScaleSquare`: **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 35).*
  53. `K .sixVertexExtremalEnvelope`: **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitEnvelopeRow`); `[20a]` item 36).*
  54. `K .highDegreePositive`: **At least one high-degree vertex**: `1 ≤ |H|`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 72).*
  55. `K .highDegreeSurplusCapacity`: **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every high vertex has all its neighbours among the `n − |H|` baseline vertices).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`highDegreeSurplusRow`); `[20a]` item 73).*
  56. `K .canonicalCapacityExplicit`: **G's canonical capacity presentation is the explicit one**: the recorded blocker activation of G's active family on the node-`[19]` packing.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityRow`); `[20a]` item 83).*
  57. `K .canonicalTokenCount`: **The exact token count at the canonical presentation**: `|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`: `|𝔗_cap| = 4n + 3σ + 15ν`).  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 85).*
  58. `K .canonicalBlockedFreePartition`: **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 86).*
  59. `K .canonicalLedgerDeficit`: **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`, `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 87).*
  60. `K .pairCountDeficit`: **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 88).*
  61. `K .canonicalCertificationCriterion`: **The certification criterion at the canonical presentation**: its canonical certified ledger exists iff `|Π_free| ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 89).*
  62. `K .canonicalOverloadOfFits`: **If the free side fits `B`, the blocked side is overloaded**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load `> M₀` and carries an `L_geom` role-homogeneous matching or star.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 90).*
  63. `K .canonicalFreeExcessOfCapped`: **If every token carries load `≤ M₀`, the free side exceeds `B`**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitCanonicalCapacityCountsRow`); `[20a]` item 91).*
  64. `K .paperBudgetBound`: **The paper's budget at the canonical spine family fits the certification budget**: `E_paper ≤ B`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 92).*
  65. `K .paperBudgetCertifies`: **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 93).*
  66. `K .pairCodeConfiguration`: **Where G sits in the pair-code chain**: either the `[137]`→`[143]` configuration holds at the canonical objects (blocked pair, `[137]` count, canonical pattern, overload, caps fail), or G's canonical first failure exists and yields the `[182]` residual, or the target defect of the canonical return system's obstruction coordinates, or that obstruction's handoff together with the Type B fan entry `[65]`.  *Hoisted (top of the strict arm of `[19]`, before `[20]` (`sparseExitPairChainRow`); `[20a]` item 94).*
  67. `K .freePairCountFails`: Node `[131]`, count fails at G's canonical objects.  On the independent side it is the no-arm of `[131]`'s decision; on the dependent side the same row and contract as on `[20a]` (`sparseExitFreePairCountRow`) runs once at the top of `[130]`'s dependent arm (reuse, 2026-09-28).  Formerly an extra fact of the two independent subtypes only.
  68. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  69. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  70. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  71. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  72. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  73. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  74. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  75. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  - *Arm `system`* (one disjunct): `K .pairSystemEarlyOutcome`.
  - *Arm `increment`* (one disjunct): `K .pairSystemNoEarlyOutcome`, `K .pairSerialDemandSystem`, `K .pairIncrementCovered`, `K .pairIncrementEarlyOutcome`.
- **Subtypes** (`PairTypeBOutcome_<label> := PairTypeBOutcome ∧ <extra facts>`; each has `.toGeneric`):
  - **`PairTypeBOutcome_independentSystem`** ([130] independent (blocker-free) arm; [131] free-pair count fails; [179] early outcome); return theorem `pairTypeBIndependentSystemReturn`; 83 facts (80 common + 3 extra):
    38. `K .independentPairFamily`: Node `[130]`, blocker-free arm: the exact negation of `dependentPairFamily` at G's canonical activation (`Π_blk = ∅`).
    39. `K .freePairCodeUnrealized`: Node `[131]`, complementary arm: the free-pair code is not realized by the skeleton class.
    40. `K .pairSystemEarlyOutcome`: Node `[179]`, alternatives (i)--(iv), retained for their literal route; (iv) is the first-separator handoff of the obstruction's own overlap support at `P₀`.
  - **`PairTypeBOutcome_independentIncrement`** ([130] independent (blocker-free) arm; [131] free-pair count fails; [179] serial arm; [180] covered increment; [180] early outcome); return theorem `pairTypeBIndependentIncrementReturn`; 86 facts (80 common + 6 extra):
    38. `K .independentPairFamily`: Node `[130]`, blocker-free arm: the exact negation of `dependentPairFamily` at G's canonical activation (`Π_blk = ∅`).
    39. `K .freePairCodeUnrealized`: Node `[131]`, complementary arm: the free-pair code is not realized by the skeleton class.
    40. `K .pairSystemNoEarlyOutcome`: Node `[179]`, serial arm: the exact negation of `pairSystemEarlyOutcome`.
    41. `K .pairSerialDemandSystem`: Node `[179]`, alternative (v): the graph-realized serial demand system.
    42. `K .pairIncrementCovered`: Node `[180]`: corrected arithmetic or a periodic-response route.
    43. `K .pairIncrementEarlyOutcome`: Node `[180]`, periodic-response sparse-exit or Type B route.
  - **`PairTypeBOutcome_dependentSystem`** ([130] dependent arm (no blocker (d), no blocker (e)); [132] blocker arm; [137] blocked-side count fails; [179] early outcome); return theorem `pairTypeBDependentSystemReturn`; 92 facts (80 common + 12 extra):
    38. `K .dependentPairFamily`: Node `[130]`, blocked arm of "blocker-free?": at G's canonical activation some scheduled pair has a nonempty blocker set over all six clauses of `def:surplus-blockers` (`Π_blk ≠ ∅`).
    39. `K .pairDegreeProfileFibres`: Node `[130]`, `lem:degree-profile-fibres` at G's pair family.
    40. `K .pairNoProfileObstruction`: Node `[130]`, blocker clause (d) absent at G's canonical activation.
    41. `K .pairNoResponseObstruction`: Node `[130]`, blocker clause (e) absent at G's canonical activation.
    42. `K .blockedPairNoExit`: Node `[132]`, blocker arm: the exact negation of `sparsePairExit`.
    43. `K .canonicalBlockerRoute`: Node `[132]`, blocker arm: no sparse surplus exit occurs, and the blocked pair of `[130]` at G's canonical activation has its canonical blocker `Φ_can(π) = min_≺ 𝖡𝗅𝗄(π)` of `def:canonical-blocker-ledger`.
    44. `K .canonicalPairLedger`: Nodes `[130]`--`[134]`, `def:sparse-pair-response`'s pair schedule with `def:canonical-blocker-ledger` and `lem:canonical-blocker-ledger-no-overcount`: `Π(𝒜₀)` has `C(σ(G),2)` members, and at every reading of the closed clause list of `def:surplus-blockers` the canonical charge is single-valued, so `Π_blk` and ...
    45. `K .capacityTokenLedger`: Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with `lem:primitive-carrier-supply`, `def:capacity-token-ledger` with `lem:capacity-token-supply` and `lem:token-ledger-no-overcount`, and `def:same-token-patterns`: `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 3(δ−1)n`, the manuscript's `≤ 6n`, spent against the ...
    46. `K .blockedPairEntropySetup`: Node `[137]`: the exact capacity presentation and node-`[129]` baseline realization, assembled through `FactInputs.get` before the entropy split.
    47. `K .blockedPairCountFails`: Node `[137]`, free-side count fails: the exact negation of `blockedPairEntropySandwich`.
    48. `K .blockedPairCodeUnrealized`: Node `[137]`, complementary arm: at some declared capacity presentation the free side's code is not realized by the skeleton class.
    49. `K .pairSystemEarlyOutcome`: Node `[179]`, alternatives (i)--(iv), retained for their literal route; (iv) is the first-separator handoff of the obstruction's own overlap support at `P₀`.
  - **`PairTypeBOutcome_dependentIncrement`** ([130] dependent arm (no blocker (d), no blocker (e)); [132] blocker arm; [137] blocked-side count fails; [179] serial arm; [180] covered increment; [180] early outcome); return theorem `pairTypeBDependentIncrementReturn`; 95 facts (80 common + 15 extra):
    38. `K .dependentPairFamily`: Node `[130]`, blocked arm of "blocker-free?": at G's canonical activation some scheduled pair has a nonempty blocker set over all six clauses of `def:surplus-blockers` (`Π_blk ≠ ∅`).
    39. `K .pairDegreeProfileFibres`: Node `[130]`, `lem:degree-profile-fibres` at G's pair family.
    40. `K .pairNoProfileObstruction`: Node `[130]`, blocker clause (d) absent at G's canonical activation.
    41. `K .pairNoResponseObstruction`: Node `[130]`, blocker clause (e) absent at G's canonical activation.
    42. `K .blockedPairNoExit`: Node `[132]`, blocker arm: the exact negation of `sparsePairExit`.
    43. `K .canonicalBlockerRoute`: Node `[132]`, blocker arm: no sparse surplus exit occurs, and the blocked pair of `[130]` at G's canonical activation has its canonical blocker `Φ_can(π) = min_≺ 𝖡𝗅𝗄(π)` of `def:canonical-blocker-ledger`.
    44. `K .canonicalPairLedger`: Nodes `[130]`--`[134]`, `def:sparse-pair-response`'s pair schedule with `def:canonical-blocker-ledger` and `lem:canonical-blocker-ledger-no-overcount`: `Π(𝒜₀)` has `C(σ(G),2)` members, and at every reading of the closed clause list of `def:surplus-blockers` the canonical charge is single-valued, so `Π_blk` and ...
    45. `K .capacityTokenLedger`: Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with `lem:primitive-carrier-supply`, `def:capacity-token-ledger` with `lem:capacity-token-supply` and `lem:token-ledger-no-overcount`, and `def:same-token-patterns`: `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 3(δ−1)n`, the manuscript's `≤ 6n`, spent against the ...
    46. `K .blockedPairEntropySetup`: Node `[137]`: the exact capacity presentation and node-`[129]` baseline realization, assembled through `FactInputs.get` before the entropy split.
    47. `K .blockedPairCountFails`: Node `[137]`, free-side count fails: the exact negation of `blockedPairEntropySandwich`.
    48. `K .blockedPairCodeUnrealized`: Node `[137]`, complementary arm: at some declared capacity presentation the free side's code is not realized by the skeleton class.
    49. `K .pairSystemNoEarlyOutcome`: Node `[179]`, serial arm: the exact negation of `pairSystemEarlyOutcome`.
    50. `K .pairSerialDemandSystem`: Node `[179]`, alternative (v): the graph-realized serial demand system.
    51. `K .pairIncrementCovered`: Node `[180]`: corrected arithmetic or a periodic-response route.
    52. `K .pairIncrementEarlyOutcome`: Node `[180]`, periodic-response sparse-exit or Type B route.

<a id="residual-187-type-b-sublinear"></a>

### Node [187] (Type B sublinear failure) (thm:main (vi), tex 369-378)

- **Configuration at G.** Failure of the Type B sublinear hypothesis package on the unified route-8 ledger.
- **Lean.** Generic residual `TypeBSublinearOutcome` (`Assembly/Residuals.lean`), return theorem `typeBSublinearReturn`: the 81 facts common to all paths. It is returned at one Lean site (`Assembly/RouteEight/Local.lean`, the negative arm of `typeBSublinearDichotomy` in `selectedRouteEightUnifiedResidual`), which 750 paths from the root reach with 750 distinct fact sets (after the two lane-entry closures of Closed from G's facts). Product form: `TypeBSublinearOutcome_product` (`Assembly/Residuals/TypeBSublinearOutcome.lean`), below; wired: the return site calls `typeBSublinearProductReturn` with its `Route8Arms` argument.
- **Facts carried (81).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .largeBudgetResidual`: Node `[53]`, no arm — node `[55]`, Residual C: the joint package still fits the skeleton budget, and the branch is the large-budget residual.
  38. `K .netDeficiencyCap`: Node `[56]`: exact cleared finite form of the large-budget net-deficiency cap.
  39. `K .route8Rate`: Node `[120]`: the private-carrier rate reading of the census alone, `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13` with the `o(|R|)` allowance, `rem:route8-carrier-margin`), read from the arm's density fact.
  40. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  41. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  42. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  43. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  44. `K .coldFailureCycle`: `lem:cold-corridor-first-failure` (F1): a first failure that closes an accepted cycle is excluded at G by target avoidance.
  45. `K .coldFailureCompression`: `lem:cold-corridor-first-failure` (F3): a first failure that is a compression of G is excluded by uncompressibility.
  46. `K .coldHandoffTransfer`: `lem:cold-corridor-first-failure` (F4): an (F4) first failure transfers the corridor to its declared handoff interface of G.
  47. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  48. `K .typeBAbsorbedCharge`: Node `[177]`: every selected half-edge outside the subcubic candidates has its pinned absorbed Type B support, charged to the surplus of its centre.
  49. `K .highCentreNormalForm`: Node `[67]`, the standing law: every high centre of the object has its neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` -- cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside `{h}` for a nonadjacent pair.
  50. `K .sameCenterOpenPortCompatibility`: Node `[69]`, `lem:same-center-open-port-compatibility`.
  51. `K .triangularShoulderCompletion`: `lem:triangular-shoulder-completion`: the four completion-incidence conclusions for every triangular port at a heavy centre.
  52. `K .triangularPortReturn`: `lem:triangular-port-return`: deleting a triangular port edge leaves a simple return through a shoulder; its restored cycle is forbidden, and the shoulder tail contains a noncentral completion incidence.
  53. `K .route8BasinBurden`: Node `[112]`: the selected route-`8` residual carries the basin-burden lower side of `lem:typeA-route8-burden`.
  54. `K .route8CarrierCore`: Node `[114]`: canonical minimal carrier-core facts for every declared reading of the selected route-`8` residual.
  55. `K .typeBBridgeMass`: Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts for certificate residuals, overlap obstructions, and grouped decorated envelope residuals.
  56. `K .typeBBridgeSublinear`: `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been extracted into the Type A ledger, the remaining Type B bridge residual mass is paid by the assigned high-centre surplus.
  57. `K .route8UnifiedNegative`: Node `[123]`, `def:typeA-unified-negative`: the canonical collection of exactly the zero-surplus negative supports which produce no decorated Type B handoff, together with its cleared total deficit.
  58. `K .typeAExclusion`: Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the minimal counterexample: every negative zero-surplus canonical piece of a maximal packing's remainder carries an exit-`(4)` witness for a routed load, an admissible silent-core residual profile, or a produced decorated Type B handoff.
  59. `K .typeBBridgeReduction`: `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap` (`def:typeB-bridge-statements`), in the contrapositive the branch carries: every negative positive-surplus canonical piece of a maximal packing's remainder carries the B2 disjoint ledger with strictly negative remaining scaled core charge — every ...
  60. `K .route8PiecesClassified`: `thm:branch-kill`'s all-pieces classification: every negative piece of the canonical decomposition is silent-first when it has no ambient surplus, and is a Type B bridge component when it has positive surplus.
  61. `K .route8ExtractedEntryCensus`: `def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the extracted route-8 cores of the Type B bridge pieces (node `[123]`): the exact per-entry census of `lem:typeB-bridge-with-route8-core`'s collection `𝒜_X`.
  62. `K .typeBSublinearResidual`: The exact negation of the sublinear hypotheses, retained as the tested residual state (the manuscript's Part IX bridge-residual continuation).
  63. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  64. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  65. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  66. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  67. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  68. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  69. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  70. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  71. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  72. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  73. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  74. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  75. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  76. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  77. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  78. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  79. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  80. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  81. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Product of arm blocks (user ruling).** The 750 paths hold 750 distinct fact sets. Each is exactly the 71 generic facts above together with the keys of one block choice in each factor below. The chosen blocks are pairwise key-disjoint, and every combination occurs on exactly one path, so the product is full: 750 = 15 (lane entry: 3 prefix × 4 entropy + `[161]` prefix × 3 low entropy) × 50 (continuation), with 50 = 44 (Type A lane) + 6 (Type B high-surplus lane). Closed from G's facts: the 120 former `Route8DeficitBlock_holds` paths at `[124]` and the 12 absorbed-lane arms at `[173]` (1360 → 1000), then the `[146]` prefix (200 paths) and `[161]` × high entropy (50 paths) (1000 → 750). The check was made path by path against the elaborated ledgers (on the 1360-path product; the 750 are that product with the closed choices removed).
  - Lean: `TypeBSublinearOutcome_product := TypeBSublinearOutcome ∧ Route8LaneEntry ∧ NetChargeContinuation` (`Assembly/Residuals/TypeBSublinearOutcome.lean`), with `.toGeneric` and return theorem `typeBSublinearProductReturn`. The blocks are the shared route-8 blocks of `Assembly/Residuals/Route8Blocks.lean`, the same ones `Route8QuotientOutcome` uses; each has a `.ret` theorem with one `get` per key.
  - `NetChargeContinuation = TypeALane ∨ TypeBHighSurplusLane` (the absorbed lane is closed at `[173]`, see "Closed from G's facts").
  - `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry ∧ TypeAArm`, where `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour ∧ Route8DeficitBlock_fails) ∨ TypeAArmBlock_dischargedRetest`.
  - `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`.
  - `BChain = BChainEntryBlock ∧ BChainFanCertificate` (6 fan/certificate arms: the heavy-centre fan with the residual, B2-choice and overlap-obstruction certificates; the degree-four fan with the residual, degree-four-closed and degree-four-overlap certificates).
  - Total facts per path: 71 + the chosen blocks, from 101 to 140.
- **Arm blocks (each with its arms, the number of paths it is on, and its keys).**
  - **Prefix factor (4 live blocks; `Route8LanePrefix` is the three that take every entropy arm, `Route8LanePrefixBlock_unrealizedDenseBelow` takes only `EntropyArmLow`).**
    - `Route8LanePrefixBlock_realizedColdBelow` ([158] window package realized; [146] θ < 1/78); on 200 paths; 2 keys:
      - `K .coldRoute8Below`: Node `[146]`, yes: the canonical packing lies below the route-8 private-carrier threshold.
      - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of ...
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` ([158] window package realized; [146] θ ≥ 1/78; [153] bounded cold mass under the density cap); on 200 paths; 6 keys:
      - `K .coldMassBounded`: Node `[153]`, complementary arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
      - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
      - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in the object's own dyadic scale.
      - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of ...
      - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
      - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
    - `Route8LanePrefixBlock_unrealizedDenseBelow` ([158] window package unrealized; [160] first test: dense deficiency below); on 150 paths; 2 keys:
      - `K .denseDeficiencyBelow`: On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison holds at the fixed maximal packing — the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance, i.e.
      - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow`: closed at `[146]` (`θ < 1/78` forces `τ(θ) < 1/4`; see Closed from G's facts).
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` ([158] unrealized; [160] dense deficiency at or above; [146] θ ≥ 1/78; [153] bounded cold mass under the density cap); on 200 paths; 7 keys:
      - `K .coldMassBounded`: Node `[153]`, complementary arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
      - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
      - `K .denseDeficiencyAtOrAbove`: Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
      - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in the object's own dyadic scale.
      - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
      - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
      - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - **Entropy factor `EntropyArm` (4 blocks).**
    - `EntropyArmBlock_high` ([50] remainder entropy high; [53] entropy cap); on 150 paths; 3 keys:
      - `K .entropyCapBound`: Node `[54]`: the independently realized window/remainder code fits in the labelled skeleton class.
      - `K .entropyPackageDemand`: Node `[52]`: the window package and the remainder accounting, joined.
      - `K .remainderEntropyHigh`: Node `[50]`, yes arm — node `[51]`, the high-entropy remainder branch: `η(R) ≥ (1/d)·log₂ n`, i.e.
    - `EntropyArmBlock_lowNonrepetitive` ([50] remainder entropy low; local-type coordinate non-repetitive); on 200 paths; 2 keys:
      - `K .localTypeCoordinateNonrepetitive`: `prop:two-budget` (c): the same literal coordinate is not structurally repetitive.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
    - `EntropyArmBlock_lowRepetitiveWedgeFree` ([50] remainder entropy low; local-type coordinate repetitive; root-wedge split wedge-free); on 200 paths; 4 keys:
      - `K .dominantRootedType`: `lem:dominant-type`: the repetitive coordinate has a single rooted radius-two type outside only the registered finite `o(n)` allowance.
      - `K .dominantRootedTypeWedgeFree`: The wedge-free subarm after `lem:dominant-type`; the manuscript makes no translate-rank claim and passes this arm to the large-budget analysis.
      - `K .localTypeCoordinateRepetitive`: `prop:two-budget` (b): on the low-entropy residual, the radius-two rooted-type coordinate lies below the exact finite relabelling threshold.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
    - `EntropyArmBlock_lowRepetitiveWedge` ([50] remainder entropy low; local-type coordinate repetitive; root-wedge split wedge type); on 200 paths; 5 keys:
      - `K .dominantRootedType`: `lem:dominant-type`: the repetitive coordinate has a single rooted radius-two type outside only the registered finite `o(n)` allowance.
      - `K .dominantRootedWedgeType`: The literal incoming wedge subarm of `lem:translates-independent`: the preceding executor proved the dominant rooted type and the decision found an internal root wedge in that same type.
      - `K .independentObstructionTranslates`: Nodes `[51]`--`[52]`, `lem:translates-independent`: a dominant rooted radius-`r` type with an internal root wedge admits a maximal `2r`-separated family of translates.
      - `K .localTypeCoordinateRepetitive`: `prop:two-budget` (b): on the low-entropy residual, the radius-two rooted-type coordinate lies below the exact finite relabelling threshold.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
  - **Type A lane `TypeALane` (44 = 2 × 22; 22 = 3 × 6 + 3 × 1 + 1).**
    - `NetChargeLaneBlock_typeALowSurplus` ([59] net charge negative; [62] Type A; [88] saturated receiver); on 660 paths; 11 keys:
      - `K .negativeSupport`: Node `[61]`: `prop:negative-net-charge`.
      - `K .netChargeCap`: Node `[60]`: the large-budget remainder has negative total net charge once the paper's explicit sufficiently-large predicate holds.
      - `K .netChargeNegative`: Node `[59]`, no arm: `N₀(R) < 0` for that same selected packing.
      - `K .typeABoundedSupport`: Node `[87]`: the selected Type A support is induced-`P_windowOrder`-free; every two of its vertices have an internal path of length at most `windowOrder - 2`, and the subcubic breadth-first bound gives `1 + threshold * (2^(windowOrder - 2) - 1)` vertices.
      - `K .typeAExitFourFiniteDescent`: `lem:typeA-exit4-finite-descent` / `lem:typeA-saturated-handoff`: the finite exit-`(4)` descent principle read at the exact current saturated receiver/peeling state; consumed by node `[123]`'s pressure descent.
      - `K .typeALowSurplus`: Node `[62]`, no arm — node `[63]`, Type A: the selected negative support carries no assigned high-degree surplus.
      - `K .typeAPortReturn`: Nodes `[89]`, `[93]`, `[94]`, `[109]`, `lem:typeA-port-return`: every completion port of the selected object carries at least one anchored return.
      - `K .typeAReceiverRouting`: Node `[88]`: the routing and threshold algebra of a Type A support.
      - `K .typeASaturatedExitEntry`: **The shared entry of nodes `[101]`--`[107]`**, and the hypothesis of `lem:typeA-exit4-residual-routing`: *"let `w` be a saturated Type A receiver with a peeling set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads at `w` realize one of exits (1)--(8)"*.
      - `K .typeASaturatedReceiver`: Node `[89]`, yes arm — the entry of node `[93]`: some receiver of a Type A support has reached its saturation threshold, `L(w) ≥ s·q(w)`.
      - `K .typeASupport`: Node `[86]`: the Type A support `X₀`, `s·def⁺(X₀) < |V(X₀)|`.
    - `TypeAEntryBlock_visible` ([93] visible entry; [95]/[97]/[99] exits (1)--(3) free); on 330 paths; 4 keys:
      - `K .typeAExitOneFree`: Node `[95]`, no arm — the entry of node `[97]`: no anchored return through any completion port of any saturated receiver of any Type A support has accepted length, so exit `(1)` is not the exit this branch realizes and the saturated exit list continues at exit `(2)`.
      - `K .typeAExitThreeFree`: Node `[99]`, no arm — the entry of node `[101]`: every shared window of the packing satisfies its legal-label relation at every outside connector, so exit `(3)` is not the exit this branch realizes and the saturated exit list continues at exit `(4)`.
      - `K .typeAExitTwoFree`: Node `[97]`, no arm — the entry of node `[99]`: at every saturated receiver of every Type A support, no two receiver-entry returns through one of its completion ports are internally vertex-disjoint with accepted total length, so exit `(2)` is not the exit this branch realizes and the saturated exit list continues ...
      - `K .typeAVisibleEntry`: Node `[93]`, yes arm — the entry of the saturated exit chain at node `[95]`: some completion port of a saturated receiver of the Type A support carries `s` visible receiver-entry returns, in the sense of `def:typeA-visible-load`.
    - `TypeAEntryBlock_noVisible` ([93] no visible entry); on 330 paths; 2 keys:
      - `K .typeANoVisibleEntry`: Node `[93]`, no arm: no saturated receiver of `X₀` has an overloaded completion port.
      - `K .typeAVisibleFirstExcess`: Node `[93]`, no arm — node `[94]`, `lem:typeA-silent-excess-count`: no saturated receiver of the Type A support has a completion port carrying `s` visible receiver-entry returns, so the visible-first excess basins of `def:typeA-excess-basin` are silent and carry the whole excess, `S_sil^exc(X) ≥ s·D_A(X)`.
    - `TypeAArmBlock_decorated` ([103]/[105] exits (5), (6) free; [107] exit (7) handoff, decorated to the Type B chain); on 540 paths; 6 keys:
      - `K .typeAExitFiveFree`: Node `[103]`, no arm: the exact selected saturated-handoff residual after no exit `(4)` carries no target-complete proper-support compression, so the branch may continue to exit `(6)`.
      - `K .typeAExitSevenEnvelope`: Node `[108]`: the canonical exit-`(7)` separation and envelope of `X₀` at the terminal state.
      - `K .typeAExitSevenHandoff`: Node `[108]`, on node `[107]`'s yes arm — exit `(7)` of `def:typeA-saturated-exits`: *"a high-degree decorated handoff fan envelope is produced"*, at the visible saturated port node `[93]` delivered.
      - `K .typeAExitSixFree`: Node `[105]`, no arm: that same selected residual has no exit-`(6)` delocalization, so it can continue to exit `(7)`.
      - `K .typeASaturatedHandoffExitFourFree`: `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current saturated receiver/peeling state; this is the predecessor of exit `(5)`.
      - `K .typeBDecoratedAssignedSupport`: Node `[65]` on the decorated lane: the exact exit-`(7)` envelope, its Type-B centres and assigned first-neighbour supports, and every clause of `lem:decorated-fan-admissibility`, all published on the same residual for the common Type B continuation.
    - `TypeAArmBlock_route8Residual` ([103]/[105] exits (5), (6) free; [107] exit (7) free: route-8 residual profile); on 90 paths; 5 keys:
      - `K .route8ResidualProfile`: Node `[110]`, exit `(8)`: the selected route-8 residual satisfies the silent-core residual profile.
      - `K .typeAExitFiveFree`: Node `[103]`, no arm: the exact selected saturated-handoff residual after no exit `(4)` carries no target-complete proper-support compression, so the branch may continue to exit `(6)`.
      - `K .typeAExitSevenFree`: Node `[107]`, no arm — the entry of node `[109]`: no high-degree decorated handoff fan envelope is produced at any visible port of any saturated receiver of any Type A support, so exit `(7)` is not the exit this branch realizes and the saturated exit list continues at exit `(8)`, the route-8 residual of ...
      - `K .typeAExitSixFree`: Node `[105]`, no arm: that same selected residual has no exit-`(6)` delocalization, so it can continue to exit `(7)`.
      - `K .typeASaturatedHandoffExitFourFree`: `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current saturated receiver/peeling state; this is the predecessor of exit `(5)`.
    - `TypeAArmBlock_dischargedRetest` ([101] exit (4) peeled; [102] recompute-L4 retest discharges the receiver); on 30 paths; 4 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAExitFourReceiverDischarged`: Node `[102]`, no-loop arm: after the exit-`(4)` peel, the selected receiver is no longer saturated at the peeled residual, so its remaining receiver charge is nonnegative by `lem:typeA-exit4-peeling-charge`.
      - `K .typeAPeeledUnsaturatedDischarge`: Node `[91]` after peeling: `|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|`.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `TypeAExitFourBlock_absent` ([101] exit (4) absent); on 210 paths; 1 keys:
      - `K .typeAExitFourAbsent`: Node `[101]`, no arm: the entry state of the exit-chain receiver of `X₀` has no exit `(4)`.
    - `TypeAExitFourBlock_peeledVisible` ([101] exit (4) peeled; [89] peeled visible entry); on 210 paths; 7 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAPeeledExitOneFree`: Node `[95]` after peeling, no arm.
      - `K .typeAPeeledExitThreeFree`: Node `[99]` after peeling, no arm.
      - `K .typeAPeeledExitTwoFree`: Node `[97]` after peeling, no arm.
      - `K .typeAPeeledSaturatedReceiver`: Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated at its terminal peeling set.
      - `K .typeAPeeledVisibleEntry`: Node `[93]` after peeling, yes arm: the terminal state has an overloaded port.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `TypeAExitFourBlock_peeledNoVisible` ([101] exit (4) peeled; [89] no peeled visible entry); on 210 paths; 5 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAPeeledNoVisibleEntry`: Node `[93]` after peeling, no arm: the terminal state has no overloaded port.
      - `K .typeAPeeledSaturatedReceiver`: Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated at its terminal peeling set.
      - `K .typeAPeeledSilentExcess`: Node `[94]` after peeling: the residual excess `E₄(w)` is nonempty and silent.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `Route8DeficitBlock_fails` ([113] large-budget deficit fails); on 90 paths; 1 keys:
      - `K .route8LargeBudgetDeficitFails`: Node `[113]`, no arm.
  - **Type B high-surplus lane `TypeBHighSurplusLane` (6).**
    - `NetChargeLaneBlock_typeBHighSurplus` ([59] net charge negative; [62] Type B); on 90 paths; 5 keys:
      - `K .negativeSupport`: Node `[61]`: `prop:negative-net-charge`.
      - `K .netChargeCap`: Node `[60]`: the large-budget remainder has negative total net charge once the paper's explicit sufficiently-large predicate holds.
      - `K .netChargeNegative`: Node `[59]`, no arm: `N₀(R) < 0` for that same selected packing.
      - `K .typeBAssignedSupport`: Node `[65]` at the `[64]` entry: the ordinary Type B assigned support.
      - `K .typeBHighSurplus`: Node `[62]`, yes arm — node `[64]`, Type B: the selected negative support carries assigned high-degree surplus.
  - **B-chain `BChain` (6 = 2 × 3).**
    - `BChainEntryBlock` (Type B chain entry, common to every B-chain arm); on 630 paths; 7 keys:
      - `K .compatiblePairFanClosure`: `lem:compatible-pair-fan-closure`: compatible open ports recorded by one assigned profile are distinct fan-closed ports.
      - `K .compatiblePairTypeBRouting`: `cor:compatible-pair-typeB-routing`: a recorded compatible open pair gives the positive local Type-B deficit.
      - `K .fanCertificateCap`: Node `[70]`: the certificate-marked fan-degree cap.
      - `K .fanClosedPortTypeBRouting`: `prop:fan-closed-port-typeB-routing`: two or more fan-closed ports give the positive local Type-B deficit bound.
      - `K .typeBExclusionResidual`: Node `[76]`/`[85]`: Type B cannot carry the linear deficit outside route `8`; the B2-paid support keeps its deficit in its remaining core, and a bridge-residual support is charged to its assigned surplus.
      - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
      - `K .typeBRoute8Entry`: Node `[77]`: the Type B entry into route `8`; a negative Type B support hands a negative remaining core to route `8` or is a bridge residual charged to its surplus.
    - `BChainFanBlock_heavyCentre` ([68] heavy centre); on 315 paths; 6 keys:
      - `K .triangularCrossShoulder`: `lem:triangular-cross-shoulder`: two cross edges between distinct triangular shoulder pairs force a high shoulder; after that branch is routed away, the surviving cross edges have cardinality at most one.
      - `K .triangularFanCore`: Node `[79]`, `def:triangular-fan-core`: the shoulder sets, induced core vertex set, and completion-incidence classifications of every nonempty triangular-port family at a heavy centre.
      - `K .triangularFirstLanding`: `lem:triangular-first-landing`: every completion incidence in a triangular fan core is uniquely central, cross-triangular, or outside.
      - `K .triangularPortTypeBRouting`: `prop:triangular-port-typeB-routing`: a degree-`k` heavy triangular family of exactly `k - 2` assigned ports gives the stronger positive local Type-B deficit bound `(5k - 19) / 4`.
      - `K .typeBFanHeavyCentre`: Node `[68]`, yes arm, on either literal `[65]` input: some assigned centre of the canonical support, or an actual centre of an indexed `[177]` handoff datum, is *heavy* — degree above the high-centre degree `δ + 1` (`d_G(h) > 4` at the manuscript's baseline).
      - `K .typeBFanLocalDichotomy`: Node `[69]` at the `[64]` entry: `cor:heavy-center-local-dichotomy` at every heavy fan centre of the ordinary Type B support — a fan-compatible open pair, or at least `d_G(h) − 2` triangular ports, hence three.
    - `BChainFanBlock_degreeFour` ([68] degree four); on 315 paths; 2 keys:
      - `K .typeBFanDegreeFourCentres`: Node `[68]`, no arm, on either literal `[65]` input — the entry of node `[78]`: every assigned centre of the canonical support, or a retained witness for every indexed `[177]` datum, has degree exactly `δ + 1` (`d_G(h) = 4` at the manuscript's baseline).
      - `K .typeBFanDegreeFourProfile`: Nodes `[78]`--`[79]` at the `[64]` entry: the degree-four fan profile of the ordinary Type B support.
    - `BChainCertificateBlock_residual` ([71]/[80] certificate labelling: residual); on 210 paths; 2 keys:
      - `K .fanCertificateResidual`: Node `[71]`/`[80]`, no arm: some assigned centre of the Type B support carries no fan-certificate labelling (G's canonical labelling is absent).
      - `K .fanCertificateResidualMass`: Nodes `[75]`/`[84]` on the certificate-residual arm: the support-level bound `lem:typeB-bridge-deficit-bound` at the fan-certificate residual support.
    - `BChainCertificateBlock_b2Choice` ([71]/[80] marked; [72] B2 disjoint); on 105 paths; 6 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBB2Choice`: Node `[72]`, yes arm: the local B1 ledger is complete and B2 holds at the Type B support: its certificate-marked assigned centres have a pairwise-disjoint choice of candidate entries on the assigned fan envelopes of the support.
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBDisjointLedger`: Node `[74]`, B2(a)--(d): the Type B support is B2-paid; its canonical B2 ledger exists with its exact augmented-ledger refinement, the inherited Type A hygiene of every remaining component, and the grouped exit-`(7)` handoff coverage used by B2(d).
      - `K .typeBExcluded`: Node `[74]`, `prop:typeB-bridge-reduction`: the remaining core of the Type B support's canonical B2 ledger carries the whole deficit.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
    - `BChainCertificateBlock_overlapObstruction` ([71]/[80] marked; [72] B2 overlap obstruction); on 105 paths; 6 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBGlobalLocalBridge`: Node `[73]`/`[83]`: the canonical minimal obstruction together with all five global-to-local reflection clauses.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
      - `K .typeBOverlapObstruction`: Node `[72]`, no arm — the entry of `[73]`: B2's disjoint-carrier clause fails at the certificate-marked Type B support, which by `lem:typeB-bridge-to-overlap` carries G's canonical minimal Type B overlap obstruction of `def:typeB-overlap-obstruction`.
      - `K .typeBOverlapObstructionMass`: Nodes `[75]`/`[84]` on the B2-failure arm: the support-level bound `lem:typeB-bridge-deficit-bound` at the reflected obstructed support.
    - `BChainCertificateBlock_degreeFourClosed` ([71]/[80] marked; [81] degree-four ledger closed); on 105 paths; 5 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBDegreeFourClosed`: Node `[82]`: certificate-closed (`c ≤ 1`, `lem:typeB-exclusion` Step 1) or B2-paid with its remaining core carrying the whole deficit, at the degree-four Type B support.
      - `K .typeBDegreeFourLedger`: Node `[81]`, yes: `c ≤ 1` at every assigned centre, or `c ≥ 2` with the B2 disjoint choice, at the degree-four Type B support.
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
    - `BChainCertificateBlock_degreeFourOverlap` ([71]/[80] marked; [81] degree-four overlap); on 105 paths; 6 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBDegreeFourOverlap`: Node `[81]`, no → `[83]`: some assigned centre has `c ≥ 2` and B2 fails; minimal Type B overlap obstruction.
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBGlobalLocalBridge`: Node `[73]`/`[83]`: the canonical minimal obstruction together with all five global-to-local reflection clauses.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
      - `K .typeBOverlapObstructionMass`: Nodes `[75]`/`[84]` on the B2-failure arm: the support-level bound `lem:typeB-bridge-deficit-bound` at the reflected obstructed support.

<a id="residual-187-route-8-quotient"></a>

### Node [187] ([348], route-8 quotient failure) (thm:main (vi), tex 369-378, 388-390)

- **Configuration at G.** Failure of route-8 quotient freeness of the unified census.
- **The paper step it carries.** `thm:main` (tex 369-372, 388-390) returns the failure of route-8 quotient freeness at `[187]`; the proof of `lem:typeA-unified-carriers` (tex 15360-15364) instead dismisses alternative (b) as exit (5), which needs a smaller connected realization of G's quotient that the paper does not supply (see "Paper findings", [348]).
- **Lean.** `Route8QuotientOutcome` (`Assembly/Residuals.lean`, the generic residual: the 83 keys common to every path); return theorem `route8QuotientReturn`, called once, at `Assembly/RouteEight/Local.lean` (`selectedRouteEightUnifiedResidual`, arm `[348]`). The 750 paths from `selectedLedgerBoundary` carry 750 distinct fact sets (probe of the elaborated `known` at every call site, R09, 2026-09-27; B-chain count corrected at integration; 250 of the 1000 paths removed by the two lane-entry closures of Closed from G's facts), and form an exact product of arm blocks: `Route8QuotientOutcome_product := Route8QuotientOutcome ∧ Route8LaneEntry ∧ NetChargeContinuation` (`Assembly/Residuals/Route8QuotientOutcome.lean`; `.toGeneric`; return theorem `route8QuotientProductReturn`, parameterised by the arm blocks, each built by its block's `.ret` with one `get` per key). The blocks are shared (`Assembly/Residuals/Route8Blocks.lean`). Every path is the 73 common keys plus exactly one block per factor, and every one of the `15 × 50 = 750` combinations occurs (`Route8LaneEntry = (Route8LanePrefix ∧ EntropyArm) ∨ (Route8LanePrefixBlock_unrealizedDenseBelow ∧ EntropyArmLow)`, `15 = 3·4 + 3`). Totals: 85 to 142 facts. Wired: the return site calls `route8QuotientProductReturn` with its `Route8Arms` argument.
- **Facts carried (83).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .largeBudgetResidual`: Node `[53]`, no arm — node `[55]`, Residual C: the joint package still fits the skeleton budget, and the branch is the large-budget residual.
  38. `K .netDeficiencyCap`: Node `[56]`: exact cleared finite form of the large-budget net-deficiency cap.
  39. `K .route8Rate`: Node `[120]`: the private-carrier rate reading of the census alone, `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13` with the `o(|R|)` allowance, `rem:route8-carrier-margin`), read from the arm's density fact.
  40. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  41. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  42. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  43. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  44. `K .coldFailureCycle`: `lem:cold-corridor-first-failure` (F1): a first failure that closes an accepted cycle is excluded at G by target avoidance.
  45. `K .coldFailureCompression`: `lem:cold-corridor-first-failure` (F3): a first failure that is a compression of G is excluded by uncompressibility.
  46. `K .coldHandoffTransfer`: `lem:cold-corridor-first-failure` (F4): an (F4) first failure transfers the corridor to its declared handoff interface of G.
  47. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  48. `K .typeBAbsorbedCharge`: Node `[177]`: every selected half-edge outside the subcubic candidates has its pinned absorbed Type B support, charged to the surplus of its centre.
  49. `K .highCentreNormalForm`: Node `[67]`, the standing law: every high centre of the object has its neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` -- cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside `{h}` for a nonadjacent pair.
  50. `K .sameCenterOpenPortCompatibility`: Node `[69]`, `lem:same-center-open-port-compatibility`.
  51. `K .triangularShoulderCompletion`: `lem:triangular-shoulder-completion`: the four completion-incidence conclusions for every triangular port at a heavy centre.
  52. `K .triangularPortReturn`: `lem:triangular-port-return`: deleting a triangular port edge leaves a simple return through a shoulder; its restored cycle is forbidden, and the shoulder tail contains a noncentral completion incidence.
  53. `K .route8BasinBurden`: Node `[112]`: the selected route-`8` residual carries the basin-burden lower side of `lem:typeA-route8-burden`.
  54. `K .route8CarrierCore`: Node `[114]`: canonical minimal carrier-core facts for every declared reading of the selected route-`8` residual.
  55. `K .typeBBridgeMass`: Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts for certificate residuals, overlap obstructions, and grouped decorated envelope residuals.
  56. `K .typeBBridgeSublinear`: `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been extracted into the Type A ledger, the remaining Type B bridge residual mass is paid by the assigned high-centre surplus.
  57. `K .route8UnifiedNegative`: Node `[123]`, `def:typeA-unified-negative`: the canonical collection of exactly the zero-surplus negative supports which produce no decorated Type B handoff, together with its cleared total deficit.
  58. `K .typeAExclusion`: Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the minimal counterexample: every negative zero-surplus canonical piece of a maximal packing's remainder carries an exit-`(4)` witness for a routed load, an admissible silent-core residual profile, or a produced decorated Type B handoff.
  59. `K .typeBBridgeReduction`: `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap` (`def:typeB-bridge-statements`), in the contrapositive the branch carries: every negative positive-surplus canonical piece of a maximal packing's remainder carries the B2 disjoint ledger with strictly negative remaining scaled core charge — every ...
  60. `K .route8PiecesClassified`: `thm:branch-kill`'s all-pieces classification: every negative piece of the canonical decomposition is silent-first when it has no ambient surplus, and is a Type B bridge component when it has positive surplus.
  61. `K .route8ExtractedEntryCensus`: `def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the extracted route-8 cores of the Type B bridge pieces (node `[123]`): the exact per-entry census of `lem:typeB-bridge-with-route8-core`'s collection `𝒜_X`.
  62. `K .typeBSublinearLedger`: `prop:typeB-bridge-sublinear`'s hypotheses, tested: the flat off-centre pair at every negative positive-surplus canonical piece and the grouped fan-assignment data at the negative zero-surplus handoff pieces.
  63. `K .route8UnifiedDeficit`: Node `[123]`, `lem:typeA-unified-deficit`: the unified collection carries the whole large-budget deficit — `|R| ≤ s·D̃_A + s·|∂R| + 2F·s·T(n)`.
  64. `K .route8QuotientResidual`: The exact negation: some unified entry realizes alternative (b).
  65. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  66. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  67. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  68. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  69. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  70. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  71. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  72. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  73. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  74. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  75. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  76. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  77. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  78. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  79. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  80. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  81. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  82. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  83. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Product of arm blocks (keys beyond the 83 common facts).**
  Structure: `Route8LaneEntry (15 = 3 prefix × 4 entropy + [161] × 3 low entropy; the `[146]` prefix and `[161]` × high entropy are closed, see "Closed from G's facts") × NetChargeContinuation`; `NetChargeContinuation = TypeALane ∨ TypeBHighSurplusLane` (50 = 2·22 + 6; the absorbed lane is closed at `[173]` and the deficit-holds choice at `[124]`, see "Closed from G's facts"); `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry (2) ∧ TypeAArm (22)`; `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour (3) ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour (3) ∧ Route8DeficitBlock_fails) ∨ TypeAArmBlock_dischargedRetest`; `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`; `BChain = BChainEntryBlock ∧ BChainFanCertificate (6)`, `BChainFanCertificate = (BChainFanBlock_heavyCentre ∧ (residual ∨ b2Choice ∨ overlapObstruction)) ∨ (BChainFanBlock_degreeFour ∧ (residual ∨ degreeFourClosed ∨ degreeFourOverlap))`.
  - Prefix factor (one of 4; `Route8LanePrefix` is the first three, `Route8LanePrefixBlock_unrealizedDenseBelow` enters only with `EntropyArmLow`):
    - `Route8LanePrefixBlock_realizedColdBelow` (2): window package realized; cold route-8 rate below (`nearCubicRealized` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` (6): window package realized; cold route-8 rate at or above, density cap (`nearCubicRealized` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .densityCap`
      - `K .windowPackageRealized`
      - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
      - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow`: closed at `[146]` (`θ < 1/78` forces `τ(θ) < 1/4`; see Closed from G's facts).
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` (7): window package unrealized; dense deficiency at or above; cold route-8 rate at or above, density cap (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .denseDeficiencyAtOrAbove`
      - `K .densityCap`
      - `K .windowPackageUnrealized`
      - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
      - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
    - `Route8LanePrefixBlock_unrealizedDenseBelow` (2): window package unrealized; dense deficiency below (`nearCubicUnrealized` → `nearCubicLargeBudgetDenseRate`)
      - `K .denseDeficiencyBelow`
      - `K .windowPackageUnrealized`
  - Entropy factor `EntropyArm` (one of 4):
    - `EntropyArmBlock_high` (3): remainder entropy high
      - `K .entropyCapBound`
      - `K .entropyPackageDemand`
      - `K .remainderEntropyHigh`
    - `EntropyArmBlock_lowNonrepetitive` (2): remainder entropy low; local type coordinate non-repetitive
      - `K .localTypeCoordinateNonrepetitive`
      - `K .remainderEntropyLow`
    - `EntropyArmBlock_lowRepetitiveWedgeFree` (4): remainder entropy low; local type coordinate repetitive; dominant rooted type wedge-free
      - `K .dominantRootedType`
      - `K .dominantRootedTypeWedgeFree`
      - `K .localTypeCoordinateRepetitive`
      - `K .remainderEntropyLow`
    - `EntropyArmBlock_lowRepetitiveWedge` (5): remainder entropy low; local type coordinate repetitive; dominant rooted wedge type
      - `K .dominantRootedType`
      - `K .dominantRootedWedgeType`
      - `K .independentObstructionTranslates`
      - `K .localTypeCoordinateRepetitive`
      - `K .remainderEntropyLow`
  - Continuation lanes:
    - `NetChargeLaneBlock_typeALowSurplus` (11): Type A low-surplus lane
      - `K .negativeSupport`
      - `K .netChargeCap`
      - `K .netChargeNegative`
      - `K .typeABoundedSupport`
      - `K .typeAExitFourFiniteDescent`
      - `K .typeALowSurplus`
      - `K .typeAPortReturn`
      - `K .typeAReceiverRouting`
      - `K .typeASaturatedExitEntry`
      - `K .typeASaturatedReceiver`
      - `K .typeASupport`
    - `NetChargeLaneBlock_typeBHighSurplus` (5): Type B high-surplus lane
      - `K .negativeSupport`
      - `K .netChargeCap`
      - `K .netChargeNegative`
      - `K .typeBAssignedSupport`
      - `K .typeBHighSurplus`
  - Type A entry `TypeAEntry` (one of 2):
    - `TypeAEntryBlock_visible` (4): visible entry
      - `K .typeAExitOneFree`
      - `K .typeAExitThreeFree`
      - `K .typeAExitTwoFree`
      - `K .typeAVisibleEntry`
    - `TypeAEntryBlock_noVisible` (2): no visible entry
      - `K .typeANoVisibleEntry`
      - `K .typeAVisibleFirstExcess`
  - Type A continuation arm (one of 3 kinds):
    - `TypeAArmBlock_decorated` (6): decorated handoff, then `TypeAExitFour` and `BChain`
      - `K .typeAExitFiveFree`
      - `K .typeAExitSevenEnvelope`
      - `K .typeAExitSevenHandoff`
      - `K .typeAExitSixFree`
      - `K .typeASaturatedHandoffExitFourFree`
      - `K .typeBDecoratedAssignedSupport`
    - `TypeAArmBlock_route8Residual` (5): route-8 residual, then `TypeAExitFour` and `Route8DeficitBlock_fails`
      - `K .route8ResidualProfile`
      - `K .typeAExitFiveFree`
      - `K .typeAExitSevenFree`
      - `K .typeAExitSixFree`
      - `K .typeASaturatedHandoffExitFourFree`
    - `TypeAArmBlock_dischargedRetest` (4): exit-four discharged retest
      - `K .typeAExitFourPeeled`
      - `K .typeAExitFourReceiverDischarged`
      - `K .typeAPeeledUnsaturatedDischarge`
      - `K .typeASaturatedHandoffExitFour`
  - Type A exit four `TypeAExitFour` (one of 3):
    - `TypeAExitFourBlock_absent` (1): absent
      - `K .typeAExitFourAbsent`
    - `TypeAExitFourBlock_peeledVisible` (7): peeledVisible
      - `K .typeAExitFourPeeled`
      - `K .typeAPeeledExitOneFree`
      - `K .typeAPeeledExitThreeFree`
      - `K .typeAPeeledExitTwoFree`
      - `K .typeAPeeledSaturatedReceiver`
      - `K .typeAPeeledVisibleEntry`
      - `K .typeASaturatedHandoffExitFour`
    - `TypeAExitFourBlock_peeledNoVisible` (5): peeledNoVisible
      - `K .typeAExitFourPeeled`
      - `K .typeAPeeledNoVisibleEntry`
      - `K .typeAPeeledSaturatedReceiver`
      - `K .typeAPeeledSilentExcess`
      - `K .typeASaturatedHandoffExitFour`
  - Route-8 deficit (one block; the deficit-holds arm is closed at `[124]`, see Closed from G's facts):
    - `Route8DeficitBlock_fails` (1): deficit fails
      - `K .route8LargeBudgetDeficitFails`
  - B-chain `BChain`:
    - `BChainEntryBlock` (7): carried on every B-chain arm
      - `K .compatiblePairFanClosure`
      - `K .compatiblePairTypeBRouting`
      - `K .fanCertificateCap`
      - `K .fanClosedPortTypeBRouting`
      - `K .typeBExclusionResidual`
      - `K .typeBFanEntry`
      - `K .typeBRoute8Entry`
    - `BChainFanBlock_degreeFour` (2): fan arm (one of 2)
      - `K .typeBFanDegreeFourCentres`
      - `K .typeBFanDegreeFourProfile`
    - `BChainFanBlock_heavyCentre` (6): fan arm (one of 2)
      - `K .triangularCrossShoulder`
      - `K .triangularFanCore`
      - `K .triangularFirstLanding`
      - `K .triangularPortTypeBRouting`
      - `K .typeBFanHeavyCentre`
      - `K .typeBFanLocalDichotomy`
    - `BChainCertificateBlock_residual` (2): certificate arm (one of 5)
      - `K .fanCertificateResidual`
      - `K .fanCertificateResidualMass`
    - `BChainCertificateBlock_b2Choice` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBB2Choice`
      - `K .typeBDirectCycleFree`
      - `K .typeBDisjointLedger`
      - `K .typeBExcluded`
      - `K .typeBHybridEntry`
    - `BChainCertificateBlock_degreeFourClosed` (5): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDegreeFourClosed`
      - `K .typeBDegreeFourLedger`
      - `K .typeBDirectCycleFree`
      - `K .typeBHybridEntry`
    - `BChainCertificateBlock_degreeFourOverlap` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDegreeFourOverlap`
      - `K .typeBDirectCycleFree`
      - `K .typeBGlobalLocalBridge`
      - `K .typeBHybridEntry`
      - `K .typeBOverlapObstructionMass`
    - `BChainCertificateBlock_overlapObstruction` (6): certificate arm (one of 5)
      - `K .fanCertificateMarked`
      - `K .typeBDirectCycleFree`
      - `K .typeBGlobalLocalBridge`
      - `K .typeBHybridEntry`
      - `K .typeBOverlapObstruction`
      - `K .typeBOverlapObstructionMass`

<a id="residual-187-private-carrier-rate"></a>

### Node [187] (private-carrier rate failure) (thm:main (vi), tex 369-378)

- **Configuration at G.** Failure of the exact private-carrier rate at the entry of the route-8 continuation.
- **Lean.** Generic residual `Route8RateFailsOutcome` (`Assembly/Residuals.lean`), the facts common to all 11 paths (distinct ledger histories from the root; the dense-below high-entropy path is closed at `[53]`, see Closed from G's facts); return theorem `route8RateFailsReturn`.  The 12 paths hold 12 distinct fact sets, each its own subtype in `Assembly/Residuals/Route8RateFailsOutcome.lean` (`<Subtype> := Route8RateFailsOutcome ∧ extra facts`, projection `<Subtype>.toGeneric`, return theorem `route8RateFailsReturn_<label>`).  Wired: `nearCubicRouteEightEntry` takes `DensityCapArm ∧ EntropyArm` and returns `route8RateFailsSubtypesReturn_routeEightEntry` (8 subtypes); `nearCubicRateFailedExit` takes `EntropyArm` and returns `route8RateFailsSubtypesReturn_rateFailedExit` (4 subtypes). The upstream-arm facts of each subtype are read from the prefix and entropy blocks.
- **Common facts carried by the generic residual (62).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
  23. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  24. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  25. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  26. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  27. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  28. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  29. `K .coldMassBounded`: Node `[153]`, complementary arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
  30. `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in the object's own dyadic scale.
  31. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  32. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  33. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  34. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  35. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  36. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  37. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  38. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  39. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  40. `K .largeBudgetResidual`: Node `[53]`, no arm — node `[55]`, Residual C: the joint package still fits the skeleton budget, and the branch is the large-budget residual.
  41. `K .netDeficiencyCap`: Node `[56]`: exact cleared finite form of the large-budget net-deficiency cap.
  42. `K .route8RateFails`: The complement of the rate reading on an arm whose density fact does not decide it (`3/13 ≤ τ`): the manuscript's delicate density interval (row 2 of the cold-branch ledger), carried as its own branch.
  43. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  44. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  45. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  46. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  47. `K .bridgeless`: `lem:bridgeless` at G.  *Hoisted (entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`); `[20a]` item 20).*
  48. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  49. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  50. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  51. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  52. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  53. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  54. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  55. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  56. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  57. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  58. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  59. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  60. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  61. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  62. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes (11), one per distinct fact set.**
  - `Route8RateFailsOutcome_realized_highEntropy` ([158] yes (realized package); [50] high; [53] bound, Residual C [55]): 68 facts, the 62 common facts and
    - `K .windowPackageRealized`
    - `K .remainderEntropyHigh`
    - `K .entropyPackageDemand`
    - `K .entropyCapBound`
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_realized_lowNonrepetitive` ([158] yes (realized package); [50] low; local-type coordinate nonrepetitive (lem:dominant-type)): 67 facts, the 62 common facts and
    - `K .windowPackageRealized`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateNonrepetitive`
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_realized_lowWedgeFree` ([158] yes (realized package); [50] low; local-type coordinate repetitive; dominant rooted type wedge-free): 69 facts, the 62 common facts and
    - `K .windowPackageRealized`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedTypeWedgeFree`
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_realized_lowWedge` ([158] yes (realized package); [50] low; local-type coordinate repetitive; dominant rooted wedge type): 70 facts, the 62 common facts and
    - `K .windowPackageRealized`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedWedgeType`
    - `K .independentObstructionTranslates`
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseAtOrAbove_highEntropy` ([158] no (unrealized package); [160] first test no (τ(θ) ≥ 1/4); [50] high; [53] bound, Residual C [55]): 69 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyAtOrAbove`
    - `K .remainderEntropyHigh`
    - `K .entropyPackageDemand`
    - `K .entropyCapBound`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive` ([158] no (unrealized package); [160] first test no (τ(θ) ≥ 1/4); [50] low; local-type coordinate nonrepetitive (lem:dominant-type)): 68 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyAtOrAbove`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateNonrepetitive`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree` ([158] no (unrealized package); [160] first test no (τ(θ) ≥ 1/4); [50] low; local-type coordinate repetitive; dominant rooted type wedge-free): 70 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyAtOrAbove`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedTypeWedgeFree`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseAtOrAbove_lowWedge` ([158] no (unrealized package); [160] first test no (τ(θ) ≥ 1/4); [50] low; local-type coordinate repetitive; dominant rooted wedge type): 71 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyAtOrAbove`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedWedgeType`
    - `K .independentObstructionTranslates`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseBelow_highEntropy`: closed at `[53]` (the dense package overflows the skeleton budget, so the entropy cap is active; see Closed from G's facts).
  - `Route8RateFailsOutcome_denseBelow_lowNonrepetitive` ([158] no (unrealized package); [160] first test yes (τ(θ) < 1/4), private-carrier rate failed there; [50] low; local-type coordinate nonrepetitive (lem:dominant-type)): 68 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyBelow`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateNonrepetitive`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseBelow_lowWedgeFree` ([158] no (unrealized package); [160] first test yes (τ(θ) < 1/4), private-carrier rate failed there; [50] low; local-type coordinate repetitive; dominant rooted type wedge-free): 70 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyBelow`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedTypeWedgeFree`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Route8RateFailsOutcome_denseBelow_lowWedge` ([158] no (unrealized package); [160] first test yes (τ(θ) < 1/4), private-carrier rate failed there; [50] low; local-type coordinate repetitive; dominant rooted wedge type): 71 facts, the 62 common facts and
    - `K .windowPackageUnrealized`
    - `K .denseDeficiencyBelow`
    - `K .remainderEntropyLow`
    - `K .localTypeCoordinateRepetitive`
    - `K .dominantRootedType`
    - `K .dominantRootedWedgeType`
    - `K .independentObstructionTranslates`
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).

<a id="residual-187-cold-terminal"></a>

### Node [187] (local cold-terminal exclusion) (thm:main (vi), tex 369-378)

- **Configuration at G.** The local cold-terminal exclusion of thm:cold-branch-quantitative-closure without a global terminal contradiction.
- **Lean.** Generic residual `ColdBranchClosedOutcome` (`Assembly/Residuals.lean`, return theorem `coldBranchClosedReturn`): 76 facts, common to every path. The residual is reached by 4 paths (distinct ledger histories from the root), the 4 linear-cold-mass singletons of `Assembly/Residuals/ColdBranchClosedOutcome.lean`. Wired: the dense linear pass returns `coldBranchClosedLinearDenseReturn` on its `[160]` arm; the realized linear arm returns its two singletons. The 100 absorbed-germ paths (formerly the product `ColdBranchClosedOutcome_product`, 4 entropy × 5 window × 5 exit blocks through `selectedAbsorbedGermResidual`) are not entered: the `[173]` no-arm is closed at the node against `K .route8Rate` (see "Closed from G's facts", `[173]`/`[174]`); the product, its blocks and `Assembly/Absorbed/*` are removed.
- **Generic facts, carried on every path (76).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  38. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  39. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  40. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  41. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  42. `K .coldCutStatesDistinct`: Node `[153]`, distinct-states arm: G's pinned cut states along each retained cold corridor are pairwise distinct up to the first failure.
  43. `K .coldFailureCycle`: `lem:cold-corridor-first-failure` (F1): a first failure that closes an accepted cycle is excluded at G by target avoidance.
  44. `K .coldFailureDefectRoute`: `lem:cold-corridor-first-failure` (ii): an (F2) pair of prefixes of one of G's corridors is a target-defective quotient.
  45. `K .coldFailureCompression`: `lem:cold-corridor-first-failure` (F3): a first failure that is a compression of G is excluded by uncompressibility.
  46. `K .coldHandoffTransfer`: `lem:cold-corridor-first-failure` (F4): an (F4) first failure transfers the corridor to its declared handoff interface of G.
  47. `K .coldFailureRouting`: `lem:cold-corridor-first-failure`: the routing (F1)--(F5) of G's first failures, with (F2) excluded on the (★) arm.
  48. `K .coldExchangeBound`: `def:cold-corridor-first-failure`: the `M_cold = Q_cold + 30` exchange bound on the retained corridor of every selected half-edge of G that reaches its successor stub before `Q_cold + 1` states.
  49. `K .coldGermCandidates`: Node `[153]`: a positive current-residual bounded-germ family.
  50. `K .absorbedGermSplit`: Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy — every selected branch-excess half-edge's first-failure support is subcubic (a charged candidate germ) or meets a heavy centre whose neighbours all sit at the threshold (node `[10]`).
  51. `K .coldGermRouted`: `lem:cold-bounded-germ-trichotomy`: every bounded configuration of G's extracted family is routed (G1, G2 or G3).
  52. `K .coldGermSilent`: `lem:cold-bounded-germ-trichotomy` (G3): the silent configurations of G's extracted family.
  53. `K .coldGermDistinguished`: `lem:cold-bounded-germ-trichotomy` (G2): the hit-distinguished configurations of G's extracted family.
  54. `K .coldGermRealized`: `lem:cold-bounded-germ-trichotomy`: the realized configurations of G's extracted family (G1 is closed, so none is hit-realized).
  55. `K .coldSameInterfaceTable`: `lem:cold-same-interface-table`: the finite same-interface table of G's silent configurations.
  56. `K .coldBranchClosed`: `thm:cold-branch-quantitative-closure`, local part: the local cold-terminal exclusion at G (no global terminal contradiction).
  57. `K .absorbedGermFanData`: Node `[177]`, `lem:absorbed-germ-fan-data` (ii): every selected branch-excess half-edge outside node `[153]`'s exact subcubic candidate class meets a vertex of degree above the threshold, a heavy centre, and is decorated handoff fan data for Type B.
  58. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  59. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  60. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  61. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  62. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  63. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  64. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  65. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  66. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  67. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  68. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  69. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  70. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  71. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  72. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  73. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  74. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  75. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  76. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Linear-cold-mass singletons** (one path each, each `ColdBranchClosedOutcome ∧` its extra facts, with `.toGeneric`):
  - **`ColdBranchClosedOutcome_linearDenseAtOrAbove`** (85 facts: 66 generic + 9; return `coldBranchClosed_linearDenseAtOrAboveReturn`): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassAtOrAbove`: [158] unrealized, [160] tau at or above 1/4, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing.
    - `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
    - `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
    - `K .coldGermSomeDistinguishing`: Node `[154]`, second binary test on the no-G1 arm (G2): some configuration of the extracted active family is hit-distinguished.
    - `K .coldHeavyEntryTerminal`: Node `[162]`, test arm: a retained corridor of G first failing at a heavy centre before its terminal segment is still terminal.
    - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
    - `K .denseColdCorridorsTerminal`: Node `[162]`: every return corridor of the dense hot/cold pass is the terminal (F5) subcase because its selected shortest path lies in the induced-window-free normalized remainder.
    - `K .denseDeficiencyAtOrAbove`: Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
    - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
  - **`ColdBranchClosedOutcome_linearDenseRateFailed`** (86 facts: 66 generic + 10; return `coldBranchClosed_linearDenseRateFailedReturn`): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassRateFailed`: [158] unrealized, [160] tau below 1/4 and route-8 rate failing, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing.
    - `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
    - `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
    - `K .coldGermSomeDistinguishing`: Node `[154]`, second binary test on the no-G1 arm (G2): some configuration of the extracted active family is hit-distinguished.
    - `K .coldHeavyEntryTerminal`: Node `[162]`, test arm: a retained corridor of G first failing at a heavy centre before its terminal segment is still terminal.
    - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
    - `K .denseColdCorridorsTerminal`: Node `[162]`: every return corridor of the dense hot/cold pass is the terminal (F5) subcase because its selected shortest path lies in the induced-window-free normalized remainder.
    - `K .denseDeficiencyBelow`: On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison holds at the fixed maximal packing — the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance, i.e. the inequality node `[56]` supplies to `[57]`--`[62]`.
    - `K .route8RateFails`: The complement of the rate reading on an arm whose density fact does not decide it (`3/13 ≤ τ`): the manuscript's delicate density interval (row 2 of the cold-branch ledger), carried as its own branch.
    - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
  - **`ColdBranchClosedOutcome_linearRealizedDistinguished`** (84 facts: 66 generic + 8; return `coldBranchClosed_linearRealizedDistinguishedReturn`): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / some distinguishing.
    - `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
    - `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
    - `K .coldGermSomeDistinguishing`: Node `[154]`, second binary test on the no-G1 arm (G2): some configuration of the extracted active family is hit-distinguished.
    - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
    - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of independently target-testable coordinates, i.e. its full package code is realized canonically by the labelled skeletons of the current object's class `𝒢_{n,m}`.
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - **`ColdBranchClosedOutcome_linearRealizedSilent`** (84 facts: 66 generic + 8; return `coldBranchClosed_linearRealizedSilentReturn`): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / none distinguishing.
    - `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
    - `K .coldGermNoneDistinguishing`: Node `[154]`, the exact complement of `coldGermSomeDistinguishing`: every active configuration is silent (G3 or the equal-length table).
    - `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
    - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
    - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of independently target-testable coordinates, i.e. its full package code is realized canonically by the labelled skeletons of the current object's class `𝒢_{n,m}`.
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).

<a id="residual-153"></a>

### Node [153] (lem:cold-corridor-first-failure (ii), tex 7265-7270)

- **Configuration at G.** G's first equal-state pair on a retained cold corridor, with its separating path context and profile separation; at G's canonical witness `coldRepeatWitness? = some ⟨occurrence, ε, left, right⟩` (`ColdRepeatedStateSpecAt`): the retained corridor `C_ε` of G in its outside component of `G − X_cold`; `left < right` with equal pinned states and no two equal states before `right` (the first equal-state pair); no (F1)--(F5) event before `right` and the (F2) clause at `right`; the separating path context `ColdEqualStates.prefixContext right` (accepted cycle through `piece J_right`, none through `retainedPiece J_right J_left`); the boundary-degree profiles of the two pieces differ; the glue vertices `head left`, `head right` have equal boundary-degree entries.
- **Lean.** Generic residual `Node153ResidualOutcome` (`Assembly/Residuals.lean`), return theorem `node153Return`: 61 facts, common to every path. The residual is reached by 3 paths (distinct ledger histories from the root), the three linear arms of `[153]`, with 3 distinct fact sets; each is its own open node, a subtype `Node153ResidualOutcome_<label>` (`Assembly/Residuals/Node153ResidualOutcome.lean`) := the generic residual ∧ every extra fact of that path's ledger, with projection `.toGeneric`, return theorem `node153Return_<label>` (one `get` per fact), and their disjunction `Node153ResidualSubtypes`. Wired: the return site `nearCubicColdOccurrence` takes `Node153Arm` (one of the three linear blocks `Node153LinearBlock_*`) and returns `node153SubtypesReturn`, which calls each subtype's return theorem. The 20 absorbed-lane subtypes (`[173]` exact collision fails, returned from `selectedAbsorbedGermPrerequisites`) are not entered: the `[173]` no-arm is closed at the node against `K .route8Rate` (see "Closed from G's facts", `[173]`/`[174]`).
- **Facts carried (61).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  38. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  39. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  40. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  41. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  42. `K .coldRepeatedStateResidual`: Node `[153]`, returned residual: G's first equal-state pair on a retained cold corridor, with its separating context and profile separation.
  43. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  44. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  45. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  46. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  47. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  48. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  49. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  50. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  51. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  52. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  53. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  54. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  55. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  56. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  57. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  58. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  59. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  60. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  61. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes (3).** Each carries the 61 common facts above plus the extra facts listed, in ledger order.
  1. **`Node153ResidualOutcome_denseAtOrAbove_linear`** ([158] unrealized, [160] τ ≥ 1/4; [146] no, [153] linear cold mass): 57 facts; path `nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicDenseLinear`. Extra facts (4):
     - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
     - `K .denseDeficiencyAtOrAbove`: Node `[160]`, first test no, the exact complement of `K .denseDeficiencyBelow`: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
     - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
     - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
  2. **`Node153ResidualOutcome_denseRateFails_linear`** ([158] unrealized, [160] τ < 1/4 and private-carrier rate fails; [146] no, [153] linear cold mass): 58 facts; path `nearCubicUnrealized → nearCubicDensePassRateFailed → nearCubicDenseLinear`. Extra facts (5):
     - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
     - `K .denseDeficiencyBelow`: On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison holds at the fixed maximal packing — the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance, i.e. the inequality node `[56]` supplies to `[57]`--`[62]`.
     - `K .route8RateFails`: The complement of the rate reading on an arm whose density fact does not decide it (`3/13 ≤ τ`): the manuscript's delicate density interval (row 2 of the cold-branch ledger), carried as its own branch.
     - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
     - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
  3. **`Node153ResidualOutcome_realized_linear`** ([158] realized; [146] no, [153] linear cold mass): 58 facts; path `nearCubicRealized`. Extra facts (5):
     - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of independently target-testable coordinates, i.e. its full package code is realized canonically by the labelled skeletons of the current object's class `𝒢_{n,m}`.
     - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
     - `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
     - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
     - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).

<a id="residual-162"></a>

### Node [162] (lem:dense-cold-pass, tex 7692-7694)

- **Configuration at G.** A retained cold corridor of G whose first failure is a heavy centre strictly before its terminal segment and which reads more than Q_cold states; at G's canonical witness `coldHeavyEntryWitness? = some ⟨occurrence, ε, first, centre⟩` (`ColdDenseHeavyEntrySpecAt`): `head first = centre` with `δ < d_G(centre)`; `first` is an (F4) first failure with no earlier event; the pinned states up to `first` are pairwise distinct, so `first < Q_cold`; `first < |C_ε|`; `Q_cold ≤ |C_ε|` and `C_ε` is not terminal.
- **Lean.** `Node162ResidualOutcome` (`Assembly/Residuals.lean`); return theorem `node162Return`; reached by 2 paths (distinct ledger histories from the root).
- **Facts carried (65).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
  21. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  22. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  23. `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
  24. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  25. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  26. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  27. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  28. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  29. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  30. `K .coldMassLinear`: Node `[153]`, exact form of "for all sufficiently large `n`": the cold mass exceeds the two branch-excess slacks, so the extracted germ family is positive (`lem:cold-germ-extraction`).
  31. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  32. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  33. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  34. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  35. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  36. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  37. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  38. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  39. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  40. `K .netChargeLocalization`: Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.
  41. `K .bridgeless`: `lem:bridgeless`: the selected minimal counterexample has no bridge — every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`.
  42. `K .coldReturnCorridors`: `def:cold-corridor-first-failure`, the corridor construction: every boundary stub of every outside component of the ambient-cubic cold windows has its cold return corridor.
  43. `K .coldCorridorState`: Node `[153]`, `def:cold-corridor-first-failure`: the pinned cold corridor states (`coldCutStatePresentation`) of every retained return corridor of G, with the canonical second representative of every exchange germ.
  44. `K .coldFirstFailureOccurrence`: `lem:cold-corridor-first-failure`: every retained cold return corridor of G has a first failure, an (F1)--(F5) event at its first failing segment.
  45. `K .coldCutStatesDistinct`: Node `[153]`, distinct-states arm: G's pinned cut states along each retained cold corridor are pairwise distinct up to the first failure.
  46. `K .coldDenseHeavyEntryResidual`: Node `[162]`, returned residual: a non-terminal retained corridor of G first failing at a heavy centre before its terminal segment.
  47. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  48. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  49. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  50. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  51. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  52. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  53. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  54. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  55. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  56. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  57. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  58. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  59. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  60. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  61. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  62. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  63. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  64. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  65. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Distinct fact sets: 2** (2 paths, one per set).  Both paths reach the
  return in `nearCubicDenseLinear` (`Assembly/NearCubic/DensePass.lean`) from
  the no-arm of `[158]` (`nearCubicUnrealized`); their ledgers differ only by
  the arm of `[160]` (`lem:dense-deficiency-routing`).  Each set is its own
  subtype of the generic residual, in
  `Assembly/Residuals/Node162ResidualOutcome.lean`, with `.toGeneric` and a
  return theorem reading one `get` per key.
- **Subtype `Node162ResidualOutcome_tauAtOrAbove`** (`[160]` first test fails,
  `τ(θ) ≥ 1/4`; caller `nearCubicDensePassAtOrAbove`; return theorem
  `node162Return_tauAtOrAbove`).  Extra facts:
  - `K .denseDeficiencyAtOrAbove`
  Total: 66 facts.
- **Subtype `Node162ResidualOutcome_tauBelowRateFails`** (`[160]` first test
  holds, `τ(θ) < 1/4`, and the private-carrier rate `τ(θ) < 3/13` fails;
  caller `nearCubicDensePassRateFailed`; return theorem
  `node162Return_tauBelowRateFails`).  Extra facts:
  - `K .denseDeficiencyBelow`
  - `K .route8RateFails`
  Total: 67 facts.
- **Wired.** `nearCubicDenseLinear` takes the `[160]` arm (`DenseTauArm`),
  built by its two callers, and returns `node162SubtypesReturn`; the boundary
  carries the two subtypes.

<a id="residual-54"></a>

### Node [54] (prop:entropy-high-theta, tex 9921)

- **Configuration at G.** The configuration at G where the joint realization inequality RS(R0)*2^(rate*s*p13)*2^F <= B fails; at G's `P₀ = canonicalWindowPacking` and `R₀ = R(P₀)` (`AllColdEntropyResidualStatement`): `¬ WindowFamilyRealized P₀`; the remainder glue `RS(R₀)·room ≤ B` with `room = C(C(n,2) − C(|R₀|,2), m − e(G[R₀]))`; `F ≤ c_Ω·r_Ω(R₀)`; `room < 2^{rate·s·p₁₃}·2^F`; `[53]` active, `B < 2^{rate·s·p₁₃}·RS(R₀)·2^F`; and `¬ RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`.
- **Lean.** Generic residual `Node54ResidualOutcome` (`Assembly/Residuals.lean`), return theorem `node54Return`: the facts common to all paths. Reached by 5 paths (distinct ledger histories from the root; the `unrealizedTauHighColdBelow` path is closed at `[146]`, see Closed from G's facts), whose ledgers hold 5 distinct fact sets; each is its own open node, a subtype of the generic residual, in `Assembly/Residuals/Node54ResidualOutcome.lean` (`Node54ResidualOutcome_<label>`, `.toGeneric`, return theorem `node54Return_<label>`). Wired: `nearCubicLargeBudgetColdRate` / `DensityCap` take `ColdRateArm` / `DensityCapArm` and return `node54SubtypesReturn_coldRate` / `_densityCap`; `DenseRate` and `RateFailed`, each reached from one arm, carry that arm's `FactKeys.Has` and call `node54Return_unrealizedBothRates` / `node54Return_unrealizedRateFailsBounded`.
- **Generic residual: facts common to every path (60).**
  1. `K .selection`: Nodes `[1]`--`[4]`: the selected object avoids the target and every strictly smaller baseline object does not.
  2. `K .cubicBaseline`: The presentation laws of G's registered presentation, published once at the entry (`PresentationLawsStatement`): the cubic baseline identities, the Type B presentation facts (with the dyadic target law), the sparse-surplus presentation identities, and the spine laws at G.
  3. `K .returnAvoidance`: Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted accepted set at every oriented edge.
  4. `K .noProperBaseline`: Node `[8]`: no proper subgraph satisfies the baseline.
  5. `K .slackIndependent`: Node `[10]`: vertices strictly above the threshold are pairwise nonadjacent.
  6. `K .tightEndpoint`: Node `[9]`: every oriented edge has an endpoint exactly at the threshold.
  7. `K .cycleRankConstraint`: `lem:cycle-rank`: for the selected graph, `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.
  8. `K .degreeProfileFibres`: Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's declared coordinates never identifies two realizations in different boundary-degree fibres.
  9. `K .targetCompleteContextUniversality`: Node `[12]`, `lem:context-universality`: identifications of G's admissible quotients are target-complete, and an identification valid only at G's own outside context is target-defective.
  10. `K .replacementExclusion`: Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller boundary-signature-preserving replacement with one-way obstruction inclusion.
  11. `K .uncompressible`: Node `[14]`: no proper atom admits a nontrivial target-complete compression (`cor:uncompressible`).
  12. `K .windowPresent`: Node `[15]`, no arm: the object contains an induced window of the registered order (`cor:p13-exists`).
  13. `K .maximalPacking`: Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family of induced windows, and the family is nonempty.
  14. `K .localAlgebra`: Node `[18]`: `lem:labels`'s exact legal-label census at the registered window order.
  15. `K .surplusAtOrBelow`: Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite form.
  16. `K .sparseSurplusSurvivor`: Node `[125]`, `def:named-surplus-exits`: the selected object survives the five sparse surplus exits.
  17. `K .barrierEnumeration`: Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration read from the registered table.
  18. `K .windowPackageSeparated`: Nodes `[21]`--`[22]`: `lem:p13-window-package`.
  19. `K .skeletonDominates`: `lem:skeleton-dominates` at the current residual's exact order and edge count: the fixed-edge labelled skeleton class has exactly the registered skeleton budget, and every canonical state map realizes at most that many states.
  20. `K .hotColdPartition`: Node `[22]`: the canonical hot/cold partition of the maximal packing.
  21. `K .barrierCap`: Node `[22]`, cap arm: the packing's entropy demand fits inside the labelled skeleton budget, which is itself stable under a variable edge count.
  22. `K .coldHotEntropyCap`: Node `[148]`, no: the live-hot coordinates fit in that allowance.
  23. `K .coldMass`: Node `[150]`: the exact cleared cold-mass inequality.
  24. `K .coldAmbientCubic`: Node `[151]`: the non-ambient-cubic cold-window loss.
  25. `K .coldStubExcess`: Node `[152]`: the selected cold-skeleton branch-excess inequality.
  26. `K .coldAmbientCubicStubExcess`: Node `[152]`, `lem:cold-window-stub-excess`: every ambient-baseline member of G's canonical cold family has exactly the presentation-derived external-stub count.
  27. `K .coldSelectedBranchExcess`: Node `[152]`, `def:cold-skeleton-excess`: the restricted `9C` interior mass of G's canonical cold family, each selected half-edge charged once at its cold-window endpoint.
  28. `K .remainderNormalized`: Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no window and no subgraph meeting the baseline (`sec:remainder`).
  29. `K .boundaryDemand`: Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by its boundary incidences (`lem:surplus-aware-window-stub`).
  30. `K .stubSupply`: Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the object's own surplus and the registered near-cubic threshold spent against it.
  31. `K .wedgeSupply`: Node `[30]`, the lemma proper: every region of the remainder meets the baseline out of its own internal wedge supply and twice its own positive deficiency (`lem:wedge-lower`).
  32. `K .curvatureTargetRank`: Node `[31]`, `def:curvature-target-rank` at the remainder of every maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily.
  33. `K .exactResponseProfile`: Node `[31]`, `def:exact-response-profile` at the remainder of every maximal packing: the declared raw curvature coordinates are exact, so their labelled family has exactly `W₂(R)` entries.
  34. `K .targetRankCircuit`: `lem:target-rank-circuit` at the remainder of every maximal packing: every raw test outside a maximal surviving family carries a proper finite target-dependence, and absence of proper dependences is full survival.
  35. `K .curvatureFullRank`: Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible quotient system.
  36. `K .forcedCurvatureCost`: Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.
  37. `K .remainderEntropyHigh`: Node `[50]`, yes arm — node `[51]`, the high-entropy remainder branch: `η(R) ≥ (1/d)·log₂ n`, i.e.
  38. `K .entropyPackageDemand`: Node `[52]`: the window package and the remainder accounting, joined.
  39. `K .entropyCapActive`: Node `[53]`, yes arm — the terminal `[54]`: the remaining non-curvature budget is strictly smaller than the forced curvature cost, so the joint package overflows the labelled skeleton budget (`eq:entropy-cap`, `prop:entropy-high-theta`).
  40. `K .allColdEntropyResidual`: Node `[54]`, returned residual: the configuration at G where the joint realization inequality fails.
  41. `K .minDegreeBaseline`: Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`), published once at the entry by `minDegreeBaselineRow` from the selected object's own baseline proof (on the ledger directly after `K .cubicBaseline`; listed last here).
  42. `K .packingOrderBound`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`).  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 33).*
  43. `K .noSuppressionChordViolation`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 29).*
  44. `K .specWitnessStructure`: **Every target-defect witness of G has the `[20a]` structure** (not only the canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`; the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`; `2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a minimum connected set containing `A ∪ B`.  *Hoisted (entry prefix, after `[4]` (`entrySelectionFactsRow`); `[20a]` item 95).*
  45. `K .bridgeless`: `lem:bridgeless` at G.  *Hoisted (entry prefix, after the presentation laws `K .cubicBaseline` (`bridgelessRow`); `[20a]` item 20).*
  46. `K .remainderDeficiencyBelowCut`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder).  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 37).*
  47. `K .windowCutCapacity`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`.  *Hoisted (entry prefix, after `[1]`--`[3]` (`sparseExitPackingRow`); `[20a]` item 38).*
  48. `K .primitiveCarrierCount`: **`|𝔘_sp(G)| = 4n + 2σ`.**  *Hoisted (entry prefix, after `[1]`--`[3]` (`primitiveCarrierCountRow`); `[20a]` item 84).*
  49. `K .singleBoundaryShape`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex).  *Hoisted (entry prefix, after `[8]` (`singleBoundaryShapeRow`); `[20a]` item 45).*
  50. `K .surplusDartIdentity`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`).  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 31).*
  51. `K .highDegreeCountBound`: **High-degree count**: `|H| ≤ σ`.  *Hoisted (entry prefix, after `[9]`/`[10]` (`degreeCountRow`); `[20a]` item 32).*
  52. `K .admissibleQuotientsLabelInjective`: **Every admissible quotient of G is label-injective** on its family.  *Hoisted (entry prefix, after `[13]` (`sparseExitQuotientsRow`); `[20a]` item 44).*
  53. `K .neighbourhoodPairCount` (idx 6900): **Neighbourhood pairs**: at every vertex `h`, `G[N(h)]` is a matching (no accepted quadrilateral), `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  54. `K .starCycleConstraint` (idx 6901): **Star constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`, `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`).  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  55. `K .meetingCycleConstraint` (idx 6902): **Meeting constraint**: for every vertex `h`, distinct neighbours `y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, they meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`.  *Entry prefix, after the presentation laws (`cycleNeighbourhoodRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  56. `K .highDegreePairSum` (idx 6903): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)` (tex 2797-2802), `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and `σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`.  *Entry prefix, after `[1]`--`[3]`'s baseline (`highDegreePairSumRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  57. `K .vertexDeletionComponents` (idx 6904): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  58. `K .cyclesThroughVertex` (idx 6905): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`.  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  59. `K .cutVertexBlockPaths` (idx 6906): **Block paths at the cut vertices**: for every `h` with `G − h` disconnected and every neighbour `a`, the block `{a, b}`; every `a → b` path `r` of `G − h` has `|r| + 2 ≠ 2^k`; every return of `ha` is `a ⋯ b h`; an `a → b` path avoiding `ha`, `hb` avoids `h` (`|p| ≡ 3 mod 4` when `|p| + 1 = 2^j`); a path to another block avoiding both `h`-edges splits at `h` with `|r₁| + |r₂| + 2 = |p|` (`|r₁| + |r₂| ≡ 1 mod 4`, opposite parities, when `|p| + 1 = 2^j`).  *Entry prefix, after `[8]` and `lem:bridgeless` (`cutVertexCyclesRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
  60. `K .cycleDoubleCount` (idx 6907): **Double count at the high vertices** (independent by `[10]`, tex 2107): `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with `L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`.  *Entry prefix, after `[9]`/`[10]` (`cycleDoubleCountRow`); cycle counting, Lean improvement (not routed by the paper; see [Cycle counting at G](#cycle-counting)).*
- **Subtypes (5 distinct fact sets).** Each is the generic residual plus the extra facts listed.
  - `Node54ResidualOutcome_realizedColdBelow` ([158] realized; [146] `θ < 1/78` (`[147]`)); return `node54Return_realizedColdBelow`; 63 facts in total. Extra facts:
    - `K .windowPackageRealized`: Node `[158]`, yes arm: the fixed maximal packing's full package code is realized canonically by the labelled skeletons of G's class (`2^{b_P} ≤ |𝒢_{n,m}|`).
    - `K .coldRoute8Below`: Node `[146]`, yes arm (`θ < 1/78`): the canonical packing is below the cold route-8 threshold.
    - `K .route8Rate`: Node `[120]`: the private-carrier rate reading of the census, `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13`), read from the arm's density fact.
  - `Node54ResidualOutcome_realizedBounded` ([158] realized; [146] `θ ≥ 1/78`; [153] bounded (`[24]`)); return `node54Return_realizedBounded`; 66 facts in total. Extra facts:
    - `K .windowPackageRealized`: Node `[158]`, yes arm: the fixed maximal packing's full package code is realized canonically by the labelled skeletons of G's class (`2^{b_P} ≤ |𝒢_{n,m}|`).
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no arm: the canonical packing is not below the cold route-8 threshold.
    - `K .coldMassBounded`: Node `[153]`, bounded arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
    - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in G's own dyadic scale.
    - `K .realizedDensityOrder`: Node `[146]` no on the realized-package arm `[158]` yes, made exact (Lean improvement, not routed by the paper): the realized package's entropy count `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n))` (`lem:p13-window-package`, `lem:skeleton-dominates`) against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)` (`A = 234`, `D = 109`), combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.realizedDensityOrder_of_realized`).
    - `K .realizedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·26192·C_sp + 1)²) = 2^235` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`realizedDensityOrder_false_of_large`).
  - `Node54ResidualOutcome_unrealizedTauHighColdBelow`: closed at `[146]` (`θ < 1/78` forces `τ(θ) < 1/4`; see Closed from G's facts).
  - `Node54ResidualOutcome_unrealizedTauHighBounded` ([158] unrealized; [160] `τ(θ) ≥ 1/4`; [146] `θ ≥ 1/78`; [153] bounded (`[24]`)); return `node54Return_unrealizedTauHighBounded`; 67 facts in total. Extra facts:
    - `K .windowPackageUnrealized`: Node `[158]`, no arm (`[159]`): the fixed maximal packing's full package code is not realized canonically by the labelled skeletons of G's class.
    - `K .denseDeficiencyAtOrAbove`: Node `[160]`, first test no: `τ(θ) ≥ 1/4`.
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no arm: the canonical packing is not below the cold route-8 threshold.
    - `K .coldMassBounded`: Node `[153]`, bounded arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
    - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in G's own dyadic scale.
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Node54ResidualOutcome_unrealizedRateFailsBounded` ([158] unrealized; [160] `τ(θ) < 1/4`, rate fails; [146] `θ ≥ 1/78`; [153] bounded (`[24]`)); return `node54Return_unrealizedRateFailsBounded`; 68 facts in total. Extra facts:
    - `K .windowPackageUnrealized`: Node `[158]`, no arm (`[159]`): the fixed maximal packing's full package code is not realized canonically by the labelled skeletons of G's class.
    - `K .denseDeficiencyBelow`: Node `[160]`, first test yes: `τ(θ) < 1/4`, the dense net-deficiency cap.
    - `K .route8RateFails`: Node `[160]`, second test no: the private-carrier rate fails (`3/13 ≤ τ`), retained as its own branch.
    - `K .coldRoute8AtOrAbove`: Node `[146]`, no arm: the canonical packing is not below the cold route-8 threshold.
    - `K .coldMassBounded`: Node `[153]`, bounded arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
    - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in G's own dyadic scale.
    - `K .boundedDensityOrder`: Node `[24]` on `[146]` no, made exact (Lean improvement, not routed by the paper): `[24]`'s density cap `2·rate·log₂n·p₁₃ ≤ (log₂n+1)(δn + T(n)) + densitySlack·rate·log₂n·T(n)` against the `[146]`-no lower bound `δn ≤ A·p₁₃ + D·T(n)`, combined at G (`Graph.DensityOrderBound`; `Contracts.Spine.boundedDensityOrder_of_densityCap`).
    - `K .boundedOrderSmall`: the exact size test on G's order, no arm: `n < N₀ = max(2^235, (2·M·C_sp + 1)²)` with `M = 26192 + 55224·(1 + 4·B_cold)` (`¬ Graph.SufficientlyLargeForDensityOrder`); its yes arm `N₀ ≤ n` is closed (`boundedDensityOrder_false_of_large`).
  - `Node54ResidualOutcome_unrealizedBothRates` ([158] unrealized; [160] both rates hold (`[161]`)); return `node54Return_unrealizedBothRates`; 63 facts in total. Extra facts:
    - `K .windowPackageUnrealized`: Node `[158]`, no arm (`[159]`): the fixed maximal packing's full package code is not realized canonically by the labelled skeletons of G's class.
    - `K .denseDeficiencyBelow`: Node `[160]`, first test yes: `τ(θ) < 1/4`, the dense net-deficiency cap.
    - `K .route8Rate`: Node `[120]`: the private-carrier rate reading of the census, `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13`), read from the arm's density fact.

## User-approved repairs

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

### [177] the counted core of the absorbed fan data, `lem:absorbed-germ-fan-data` (ii) (tex 7926-7952)

- **Status (closure of `[173]`'s no-arm).** The absorbed-configuration
  residual `[174]` is closed at `[173]` against `K .route8Rate` (see "Closed
  from G's facts", `[173]`/`[174]`), and `Assembly/Absorbed/*` is removed; the
  absorbed-lane wiring described here is no longer run.  The graph-level
  statements and contracts are kept.

- **Paper claim** (tex 7926-7932, proof 7945-7952): if the first-failure
  support `J` of `ε` contains a vertex `z` of degree `≥ 4`, "the corridor enters
  `z` through one of its incidences and leaves through another ... the two
  corridor incidences at `z` are distinct, so the segments of the corridor on
  either side of `z` are two connector tails separated at `z`, which is the
  decorated handoff configuration of `lem:typeA-high-degree-handoff`".  That
  configuration (tex 11110-11131, `def:decorated-fan-envelope` 10898-10925,
  `lem:decorated-fan-admissibility` 11150-11158) is an envelope `(Y, {z})` over a
  connected `P₁₃`-free remainder core `Y ⊆ R` with `z ∉ Y` ("the only new
  vertices counted outside `Y` are the decorations"), whose arms are the
  connector tails from the first neighbours of `z` "to their first-entry data
  in" `Y`.  The paper never names `Y` for a cold corridor; in the Type A lemma
  `Y` is the Type A support `X` the tails return to.
- **Faithful Lean statement (restated 2026-09-27, fix2-SC).**  `[177]`
  (`AbsorbedHandoffAt`, `Statements/TypeB.lean`) now publishes exactly that
  configuration at `ε`'s first heavy centre `z` of G's retained corridor: an
  admissible `DecoratedHandoff.Envelope` with decorations `{z}`, assigned first
  neighbours the two corridor incidences at `z`
  (`Corridor.entryNeighbour` / `exitNeighbour`, proved distinct), arms the two
  corridor segments at `z` cut at their first entry into the core
  (`Corridor.entryTail` / `exitTail`, `DecoratedHandoff.firstEntryArm`), a
  connected core `Y ⊆ R(P₀)` with `z ∉ Y`, and simple full handoff paths
  (`z ∉ A_{z,a}`).  Everything is proved from G's facts
  (`Contracts.TypeB.absorbedGermDecoratedAssignedSupport`, via the generic
  `DecoratedHandoff.envelopeOfTails`) except the existence of `Y`, which is the
  hook `Contracts.Spine.coldAbsorbedRemainderCore`: a connected `Y ⊆ R(P₀)`,
  `z ∉ Y`, met by both corridor segments at `z`.  The Type B support of the
  absorbed lane is `(Y, {z})`, chosen canonically (`canonicalAbsorbedHandoff`).
- **The former Lean statement was not the paper's.**  Until 2026-09-27 the
  hook was `coldAbsorbedPrefix_subset_remainder` ("the prefix `J` through its
  trace end lies in `R`"), and the envelope took `Y := J` with `z ∈ Y` and
  `z ∈ H` (counted twice, in `def⁺(Y)`/`|V(Y)|` and in `ω(H)`), assigned every
  neighbour of `z`, and let arms `[a, z]` return to `z`, so the handoff path
  `z a z` was not simple.  The library `Envelope` admits this (no `h ∉ core`
  clause, and landing at `h` is allowed); `[177]`'s statement now adds
  `z ∉ Y` and simplicity explicitly.  "The paper's core is `J`" was not in the
  tex.
- **Why it fails.**  A cold corridor has no Type A support.  Its two segments
  at `z` run to the corridor's two boundary stubs, whose window endpoints lie in
  ambient-cubic cold windows of `P₀`, outside `R`.
- **Completeness check** (tex 6862-6874, 8636-8674, 10063-10110, 10898-10937,
  11110-11158, 7164-7183, 7329-7345, 7883-7958): the paper's remainder objects
  are on the ledger -- `R`, `[27]`, `[22]`, the canonical pieces of `R`
  (`canonicalPieces`, `NetCharge.lean:53`), the Type A supports and exit-(7)
  envelopes `[108]`, `[10]` `.slackIndependent`, the absorbed split and fan
  data `[175]`, the subcubic reach `.coldHandoffTransfer`.  None of them is tied
  to a cold corridor, and no construction of the paper yields a connected core
  in `R` avoiding `z` that both segments enter.  Even corridor containment in
  `R` would not suffice (`z` may separate the segments' parts of `R`).
- **Construction attempt at G (fix2-177, 2026-09-27).**  The canonical
  candidate is: follow each corridor segment at `z` to its first vertex of
  `R(P₀)`, and let `Y` be the component of `G[R(P₀) \ {z}]` containing those
  entries.  Requirement by requirement at G's objects:
  - *`Y ⊆ R`, `Y` connected, `z ∉ Y`*: by construction, provided the entries
    exist.
  - *Simple paths, admissibility*: already proved from G's facts in
    `absorbedGermDecoratedAssignedSupport` (`entryTail_nodup`/`exitTail_nodup`,
    `vertexAt_not_mem_*Tail`, `entryNeighbour_ne_exitNeighbour`, fan-safety from
    `avoids`, admissibility from `[14]`/`[25]`--`[27]`).
  - *Each segment reaches `R`*: **fails in general.**  The corridor lives in
    `G − X_cold` (C2 ruling), so its inside vertices may lie in hot or
    non-ambient-cubic cold windows of `P₀`, and both segments end at a stub
    endpoint in `X_cold ⊆ ⋃P₀`.  A segment whose inside vertices all lie in
    windows meets no vertex of `R`.
  - *Both entries in one component of `G[R \ {z}]`*: fails in general (the two
    sides may be joined only through `z` and windows).
  - *`z ∈ R`?*  Not needed: `H ⊆ V_{≥4}(G)` and the hook only needs `z ∉ Y`;
    a heavy `z` inside a hot / non-ambient-cubic window is allowed by both the
    paper and the Lean.
- **The heavy entry foot, proved at G** (`Contracts.Spine.coldAbsorbedRemainderCore_heavyEntryFoot`,
  `Graph/Contracts/Spine/ColdSubcubicCharge.lean`; vocabulary-free input
  `Corridor.entryTail_zero_not_meets`, `Graph/ColdCorridorTails.lean`).  For
  every eligible selected half-edge `ε` of G whose foot `ε.2` has degree above
  the baseline: `ε ∉ coldRoutedCandidates` (the foot lies in every prefix
  support), `firstIndex = 0` satisfies every hypothesis of the hook (within the
  trace prefix, heavy head, no earlier index), and the hook's conclusion is
  **false** there: `entryTail 0 = [ε.1]` with `ε.1 ∈ X_cold ⊆ ⋃P₀`, so it meets
  no subset of `R(P₀)`.  Hence, at G, the hook is equivalent on this
  configuration to "no selected half-edge of G has a heavy foot".
- **The paper claims `i = 0` (checked 2026-09-27).**  The tex has no separate
  treatment of a heavy foot.  `def:cold-corridor-first-failure` defines the
  first failure as "the first initial segment ... at which ... (F4) the corridor
  first enters a declared Type B handoff envelope" (tex 7213, 7222), with
  segment `0` an initial segment; `lem:cold-germ-extraction` removes "Type B,
  and route-8 handoff incidences" wholesale and says "If a candidate support
  contains a vertex of degree at least `4`, then the corresponding corridor
  first enters the high-degree handoff ledger" (tex 7318, 7330-7331); and
  `lem:absorbed-germ-fan-data` (ii) covers every `J` that "contains a vertex
  `z` of degree at least `4`" with "the corridor enters `z` through one of its
  incidences and leaves through another ... the segments of the corridor on
  either side of `z` are two connector tails separated at `z`, which is the
  decorated handoff configuration of `lem:typeA-high-degree-handoff`"
  (tex 7926-7930, 7949-7951).  At `i = 0` the entering incidence is `ε`
  itself, and no other core, envelope, or `σ(G)` charge is given for it
  (the only `σ(G)` charge is node `[153]`'s bounded-arm loss, which (ii) says
  is "charged to the Type B ledger", tex 7937-7939).  So the hook is not an
  overstatement at `i = 0`: it is the paper's claim, restated faithfully.
- **`i ≥ 1` is not rescued.**  Removing `i = 0` would not remove the failure of
  "each arm reaches `R`": for `i ≥ 1` the entry side is inside vertices
  `0..i−1` of `K ⊆ G − X_cold`, and the exit side inside vertices `i+1..` of
  `K`, each ending at a stub endpoint in `X_cold`.  Under the C2 ruling these
  inside vertices may all lie in hot or non-ambient-cubic windows of `P₀`
  (maximality of `P₀` even pushes corridor vertices into windows), and no
  ledger fact at `[177]` places one of them in `R`.
- **Three routes on "some selected `ε` of G has a heavy foot `z`"**, run at
  G's objects: the configuration is `z ∈ V_{≥4}(G)` adjacent to an interior
  vertex `x` of an ambient-cubic cold window `P ∈ P₀ \ P_hot`, via a selected
  interior stub.  (1) Structure: `[10]` (independence of `V_{≥4}`) and
  `lem:deletion-critical` need `d_G(x) = 3`, which ambient-cubicity supplies;
  `coldWindowStubStructure` says `x` has exactly one external stub, which is
  `xz`; `P₀` maximality, bridgelessness, minimum degree and target avoidance
  constrain neither `d_G(z)` nor the stub's other endpoint; the (F4) registry
  fires at segment `0` (that is the absorbed case itself, not a contradiction).
  (2) Overload: such `ε` are at most `Σ_{z ∈ V_{≥4}} d_G(z) ≤ (δ+1)σ(G)` (the
  registry's exact count), which is within every bound on the ledger at
  `[177]`; one occurrence overloads nothing.  (3) Compressibility: the
  configuration is a single edge `xz`; it yields no smaller support with the
  same response, so neither `K .uncompressible` nor `K .selection` is
  contradicted.  All three fail with the configuration in hand.
- **Completeness inventory** (root → `[177]`): `R` and `P₀`
  (`remainderSupport`, `canonicalWindowPacking`), `P_hot`/`P_cold`
  (`canonicalHotWindows`/`canonicalColdWindows`), `X_cold`
  (`coldCorridorWindows`), `[10]` (`.slackIndependent`), `[14]`, `[22]`,
  `[25]`--`[27]` (remainder normalization), ambient cubicity
  (`K .coldAmbientCubic`), the stub structure (`coldWindowStubStructure`), the
  cold corridor, its states and first failures (`K .coldCorridorState`,
  `K .coldFirstFailureOccurrence`, `K .coldFailureRouting`), the (F4) registry
  (`ColdDeclaredHandoffSupport`), `[153]`'s candidates, the absorbed split and
  fan data `[175]` (`K .absorbedGermFanData`, including `neighboursCubic`), the
  canonical pieces of `R` and the Type A supports / exit-(7) envelopes `[108]`.
  The paper's remaining objects on the path (`def:cold-skeleton-excess`,
  `def:cold-bounded-germ`, `lem:cold-corridor-first-failure`) are represented
  by those keys.  None constrains the degree of a selected stub's foot or ties
  a remainder component to a cold corridor.
- **Outcome.**  `Y` is not constructible from G's facts at `[177]`: on the
  heavy-entry-foot configuration it provably does not exist (Lean above), and
  that configuration is not refuted by any of the three routes.  It is not a
  PAPER-ERROR because the configuration is not shown to occur in G; it stays
  an OPEN CONSTRUCTION whose exact content is now "G has no selected half-edge
  with a heavy foot" (for `i = 0`) together with the hot-window case for
  `i > 0`.
- **Status (2026-09-27): closed by user-approved repair.**  The hook
  `coldAbsorbedRemainderCore` and its `sorry` are deleted.  Node `[177]` now
  decides the existence of `Y` at G's canonical absorbed half-edge; the no arm
  is charged by the exact (F4) count (see "User-approved repairs", "[177]
  extension of the (F4) exact-count repair").  The obstruction analysis above
  is kept as the reason for the repair.
- **The Type B support of the absorbed lane, `(Y_X, H_X)` (integration of
  fix2-TB and fix2-SC, 2026-09-27).**  The envelope's decorations stay `{z}`;
  the Type B support the lane publishes (`canonicalTypeBAbsorbedSupportAt`,
  `Statements/CanonicalTypeB.lean`) is `(Y, {z} ∪ centres(Y))`, where
  `centres(Y)` are the high vertices of `Y`
  (`Graph.TypeBRefinedSupport.centres`).  The tex:
  - `def:typeB-assigned-ledger` (tex 12909): "write `H_X` for the high-degree
    fan centers whose surplus units are assigned to `X` by
    `def:canonical-decomp` … A high-degree vertex that appears only as boundary
    context for another support is not an element of that support's set
    `H_X`";
  - `def:canonical-decomp` (tex 10063): "All surplus units of
    `h ∈ V_{≥4}(G) ∩ V(R)` are assigned to the unique piece containing `h`. …
    When an assigned surplus unit is represented by an actual high-degree fan
    vertex in the local Type B analysis, the corresponding fan envelope records
    that vertex as decoration data";
  - `def:typeB-residual-mass` (tex 14682) puts `H_X = H_𝔠` (the decorations
    only) for "grouped decorated Type B envelope supports produced from Type A
    exit-(7) handoffs".
  The [177] support is a cold-corridor absorbed support, not an exit-(7)
  grouped envelope, so the general definition applies: `H_X` holds the
  decoration `z` and every high vertex of the counted core `Y ⊆ R`.  With it,
  `centres(Y_X) ⊆ H_X` holds by definition on this lane
  (`TypeBAbsorbedLane.centres_subset`), so the B2 ledger (`typeBB2LedgerAt`),
  the bridge-deficit bound and the per-`ε` charge `K .typeBAbsorbedCharge`
  (idx 2800, `typeBAbsorbedCharge`) are proved as before, with no new predicate
  and no new `sorry`.  Since fix2-177 the charge is stated at every selected
  half-edge whose canonical absorbed handoff `(z, Y)` is defined, and the
  `[177]` yes row enters `[65]` with `(Y, {z} ∪ centres(Y))` read from it; the
  half-edges without a counted core take the `[177]` no arm (the (F4) charge).  fix2-TB's former "`centres(J) ⊆ {z}`" proof applied to
  its prefix core `J ∋ z` and is superseded by the `(z, Y)` envelope.

### [177] extension of the (F4) exact-count repair: absorbed half-edges without a counted core (user-approved, 2026-09-27)

- **Status (closure of `[173]`'s no-arm).** The absorbed-configuration
  residual `[174]` is closed at `[173]` against `K .route8Rate` (see "Closed
  from G's facts", `[173]`/`[174]`), and `Assembly/Absorbed/*` is removed; the
  absorbed-lane wiring described here is no longer run.  The graph-level
  statements and contracts are kept.

- **Paper.** `lem:absorbed-germ-fan-data` (ii) (tex 7926-7952) routes every
  absorbed half-edge `ε` (first-failure support meeting `V_{≥4}(G)`) through
  the decorated handoff of `lem:typeA-high-degree-handoff` at its heavy centre
  `z`, which needs a counted remainder core `Y ⊆ R(P₀)`, `z ∉ Y`, entered by
  both corridor segments at `z`.  The paper never constructs `Y` for a cold
  corridor, and at G it can fail to exist: the heavy entry foot (`i = 0`,
  `Contracts.Spine.coldAbsorbedRemainderCore_heavyEntryFoot`) and segments whose
  vertices all lie in windows of `P₀` (open construction [177], below).
- **Ruling.** When `Y` exists, keep the paper's Type B handoff.  When it does
  not, charge `ε` by the exact (F4) count
  `#{ε ∉ candidates} ≤ corridorLoss ≤ (δ+1)·B_cold·σ(G)` published at `[219]`
  (`K .coldGermCandidates`), not through Type B.
- **Lean (live).**
  - `Statements/TypeB.lean`: `AbsorbedRemainderCoreAt` (the core `Y` at the
    heavy centre).  `Statements/TypeBLanes.lean`: `AbsorbedHandoffCoreStatement`
    / `AbsorbedHandoffCoreAbsentStatement` (node `[177]`'s decision at G's
    canonical absorbed half-edge: its canonical absorbed handoff is defined or
    not) and `AbsorbedF4ChargeStatement` (no arm).
  - Keys (idx 3100-3102): `K .absorbedHandoffCore`, `K .absorbedHandoffCoreAbsent`
    (decision `absorbedHandoffCoreDichotomy`, reading `K .typeBAbsorbedHalfEdge`,
    split at the one pinned `ε`), `K .absorbedF4Charge` (row
    `absorbedF4ChargeRow`).
  - Contracts (`Contracts/TypeB/Entry.lean`):
    `absorbedHandoffAt_of_remainderCore` (given `Y`, the admissible envelope
    `AbsorbedHandoffAt (z, Y)` from G's facts), `absorbedFirstIndex_unique`,
    `canonicalAbsorbedHandoff_isSome_iff_core` (the decision is exactly "a core
    `Y` exists at `z`"), `absorbedHandoffCore_split`, `typeBAbsorbedLane_of_core`,
    `typeBFanEntry_of_absorbedCore` (yes arm, `[177]` → `[65]`, support
    `(Y, {z})`), `absorbedF4Charge` (no arm).
  - Assembly (`Assembly/Absorbed/Residual.lean`): at both `[175]` yes sites,
    `[177]` yes runs the Type B entry and charge tail; `[177]` no publishes
    `K .absorbedF4Charge` and ends at the local cold exclusion
    `K .coldBranchClosed` (`[187]`), as the `[175]` no arm does.
- **Why the (F4) bound absorbs these half-edges, with no double count.**  The
  cold argument's inequalities never used the Type B charge: node `[153]`'s
  witness (`ColdGermFamilyWitness`) partitions the selected occurrences exactly
  as `#selected = #candidates + corridorLoss` (every non-candidate, in
  particular every absorbed `ε`, is one corridor-loss unit, counted once), and
  the linear arm (`coldGermFamilyPositive`: `corridorLoss < #selected`) and the
  bounded arm (`densityCapLinear_of_coldMassBounded`) use only
  `corridorLoss ≤ (δ+1)·B_cold·σ(G)`.  `AbsorbedF4ChargeStatement` records at
  G that `ε ∈ univ \ candidates`, that `#(univ \ candidates) = corridorLoss`
  of the canonical extraction `coldGermExtraction?`, and the bound.  No extra
  term arises, and on the no arm `ε` is not also sent to Type B.
- **Merge note.**  The split is on `canonicalAbsorbedHandoff ε` only; the
  absorbed support built from it on the yes arm (`canonicalTypeBAbsorbedSupportAt`,
  now `(Y, {z})`) can be widened to `H := {z} ∪ centres(Y)` without touching
  the split.

### [162]→[164] dense-pass wiring (user-approved, 2026-09-27)

[162]→[164] dense-pass wiring (user-approved). The tex (Part XII, tex 1327–1340)
routes '[53] active' on the dense pass to [164]. The Lean instead closes those
arms (`nearCubicLargeBudgetRateFailed`, `nearCubicLargeBudgetColdRate`,
`nearCubicLargeBudgetDensityCap`) with the exact [54] decision (its joint arm
closes, its other arm returns the [54] residual). Reason: [164]'s proof uses
the K=0 / hot-only reading, which the approved exact [50]/[53] supersedes.

- **Where recorded.** The current `[54]` residual entry
  ([#residual-54](#residual-54), "Returned residuals") lists the facts carried
  at the `[53]`-active sites of these arms (tex 7843-7850).
