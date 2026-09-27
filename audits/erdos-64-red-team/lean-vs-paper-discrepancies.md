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

## [118] → [123] → [124]: now paper-exact

*fix2-TR.*  The two-support entry `[118]` (the yes arm of `[117]`) enters the
descent decision `[123]` (tex 1134, edge `(residual)--(pressure)`): the
`[117]`-yes ledger continues through `selectedTypeBRoute8Continuation`, the
unified ledger on which `[123]` is asked; its yes arm closes at `[124]`
(`K .route8UnifiedTrueTwoCarrierEntry` against `K .route8UnifiedTwoCarrierExit`),
its no arm reaches `[181]`, `[183]`--`[186]`
(`Assembly/RouteEight/Residual.lean`, `selectedRouteEightCollection`).  The
earlier direct closure of `[118]` at `[124]` is no longer used.

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
  The positive arm continues to `[114]`--`[122]`, `[118]` → `[123]`; the
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

Rows run on the paths that lacked them (fix4): `[149]`--`[152]`
(`nearCubicColdStubFacts`) on the `[147]` arms and on `[161]` (with `[22]`'s
cap, `liveHotBarrierCapRow`); `[25]`--`[34]`, `[48]` and `[58]`'s localization
on the linear arms of `[153]`, with `[175]`'s split and `[177]`'s fan data on
their extracted family; the cold corridors, states, first failures, (F1)/(F3)
readings and (F4) transfer on every net-charge lane; `[58]`'s localization on
the absorbed lane; `[67]`/`[69]`'s normal form and landing lemmas, `[177]`'s
absorbed charge, `[112]`'s burden and `[114]`'s cores on every lane into
`[123]`; `[131]`'s dependence prefix, cubic budget, skeleton room and `[21]`'s
domination on the blocked side of the pair chain; `[135]`'s envelope on its
free side.

| Residual (abbrev) | Node | Paths | Facts |
|---|---|---:|---:|
| `Node20aOutcome` | [20a] | 1 | 18 |
| `NearCubicTargetDefectOutcome` | [187] (near-cubic target defect) | 1 | 18 |
| `Node144aOutcome` (6 subtypes) | [144a] | 6 | 44 common; subtypes 47, 48, 48, 49, 49, 50 |
| `BlockedBarrierOverlapOutcome` | [172a] | 2 | 71 |
| `PairConditionalFactorizationOutcome` | [182] | 6 | 33 |
| `Route8JointBalanceOutcome` | [186] | 2080 | 79 |
| `PairTypeBOutcome` | [187] ([179]/[180] Type B entry) | 4 | 42 |
| `TypeBSublinearOutcome` | [187] (Type B sublinear failure) | 2080 | 62 |
| `Route8QuotientOutcome` | [187] ([348], route-8 quotient failure) | 2080 | 64 |
| `Route8RateFailsOutcome` | [187] (private-carrier rate failure) | 12 | 42 |
| `ColdBranchClosedOutcome` | [187] (local cold-terminal exclusion) | 104 | 57 |
| `Node153ResidualOutcome` | [153] | 23 | 42 |
| `Node162ResidualOutcome` | [162] | 2 | 46 |
| `Node54ResidualOutcome` | [54] | 6 | 40 |

<a id="open-constructions"></a>
<a id="residual-20a"></a>

### Node [20a] (thm:main (i), tex 339-346)

- **Configuration at G.** The strict-surplus named sparse exit of [20]: the attempted-quotient target defect and its registered structure, on the strict arm of [19].
- **Lean.** `Node20aOutcome` (`Assembly/Residuals.lean`); return theorem `node20aReturn`; reached by 1 path (distinct ledger histories from the root).
- **Facts carried (18).**
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
  17. `K .sparseTargetDefectResidual`: Node `[125]`, the sole nonterminal named-exit payload: the concrete rank-reducing attempted quotient and identified realizations whose response is separated by an outside context.
  18. `K .sparseTargetDefectStructure`: Node `[20]`: the same identified target-defect pair with its bound outside context and proved target-free negative constituents.

<a id="residual-187-near-cubic-target-defect"></a>

### Node [187] (near-cubic target defect) (thm:main (vi), tex 369-378)

- **Configuration at G.** The sparse target-defect exit of [20] on the at-or-below-surplus arm of [19].
- **Lean.** `NearCubicTargetDefectOutcome` (`Assembly/Residuals.lean`); return theorem `nearCubicTargetDefectReturn`; reached by 1 path (distinct ledger histories from the root).
- **Distinct fact sets.** One: the single return site (`selectedNearCubicBranch`, exit arm of `sparseSurplusSurvivorDichotomy`, then `selectedSparseTargetDefectExit`) carries exactly the 18 keys below, so the generic residual is the only node and has no subtypes.
- **Facts carried (18).**
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
  17. `K .sparseTargetDefectResidual`: Node `[125]`, the sole nonterminal named-exit payload: the concrete rank-reducing attempted quotient and identified realizations whose response is separated by an outside context.
  18. `K .sparseTargetDefectStructure`: Node `[20]`: the same identified target-defect pair with its bound outside context and proved target-free negative constituents.

<a id="residual-144a"></a>

### Node [144a] (thm:main (ii), tex 347-353)

- **Configuration at G.** The same-token Type B handoff of [144] on the strict-surplus survivor, or (the paper error at [144]) the unresolved same-label pattern pair.
- **The paper step it carries.** `lem:same-token-bottleneck-routing` (tex 5585-5620) routes the two equal-label pattern edges of G's canonical routing to a same-token Type B handoff; where no handoff is produced (`K .typeBHandoffFails`), the unresolved same-label pattern pair (`K .sameTokenPatternUnresolved`: readings profile-separated, neither a sparse exit nor target-complete) and the explicit replacement candidates of tex 5594 (`K .sameTokenReadingsNotReplacement`) are carried instead.
- **Lean.** Generic residual `Node144aOutcome` (`Assembly/Residuals.lean`), the 44 facts common to every path, return theorem `node144aReturn`; reached by 6 paths (distinct ledger histories from the root), with 6 distinct fact sets, each a subtype `Node144aOutcome_<label>` (`Assembly/Residuals/Node144aOutcome.lean`) of the generic residual (`.toGeneric`), returned by `node144a<Label>Return`. The six subtypes replace the generic disjunct of `SelectedLedgerBoundaryResult` and `StrictSurplusBoundaryResult`.
- **Generic residual: facts on every path (44).**
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
- **Subtypes.** Label = class arm of `[139]`/`[141]` times arm of `[144]`'s handoff decision.
  - *`Node144aOutcome_windowHandoff`* ([139] yes (token in 𝔗_W, audit [140]); [144] handoff): 47 facts, the 44 common facts and:
    - `K .windowClassOverload`: Node `[139]`, yes arm: the overloading token of node `[137]` lies in `𝔗_W`, so the branch enters the window-incidence audit `[140]`.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_windowFails`* ([139] yes (token in 𝔗_W, audit [140]); [144] handoff fails): 48 facts, the 44 common facts and:
    - `K .windowClassOverload`: Node `[139]`, yes arm: the overloading token of node `[137]` lies in `𝔗_W`, so the branch enters the window-incidence audit `[140]`.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.
  - *`Node144aOutcome_remainderHandoff`* ([139] no, [141] yes (token in 𝔗_R, audit [142]); [144] handoff): 48 facts, the 44 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassOverload`: Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch enters the remainder-surplus audit `[142]`.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_remainderFails`* ([139] no, [141] yes (token in 𝔗_R, audit [142]); [144] handoff fails): 49 facts, the 44 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassOverload`: Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch enters the remainder-surplus audit `[142]`.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.
  - *`Node144aOutcome_primitiveHandoff`* ([139] no, [141] no (primitive token, audit [143]); [144] handoff): 49 facts, the 44 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassAbsent`: Node `[141]`, no arm: the selected overloading token lies in `𝔗_prim`, so that same witness enters `[143]`.
    - `K .primitiveClassOverload`: Node `[143]` entry: the overloading token is primitive.
    - `K .typeBHandoff`: Node `[144]`, the survivor specialization of the preceding fact: the sparse-exit arm is impossible, so the same current object is entered directly in the Type B fan ledger.
    - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
  - *`Node144aOutcome_primitiveFails`* ([139] no, [141] no (primitive token, audit [143]); [144] handoff fails): 50 facts, the 44 common facts and:
    - `K .windowClassAbsent`: Node `[139]`, no arm: the selected overloading token does not lie in `𝔗_W`, so that same witness falls through to node `[141]`.
    - `K .remainderClassAbsent`: Node `[141]`, no arm: the selected overloading token lies in `𝔗_prim`, so that same witness enters `[143]`.
    - `K .primitiveClassOverload`: Node `[143]` entry: the overloading token is primitive.
    - `K .typeBHandoffFails`: Node `[144]`, the exact complement of the same-token handoff.
    - `K .sameTokenPatternUnresolved`: Node `[144a]`, the residual of the paper error at `[144]`: the unresolved same-label pattern pair.
    - `K .sameTokenReadingsNotReplacement`: Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative.

<a id="residual-172a"></a>

### Node [172a] (thm:main (iii), tex 354-358)

- **Configuration at G.** The first failed conditional graph-count inequality of lem:scale-additivity on the dense-packing branch, with its minimal same-scale barrier overlap.
- **Lean.** Generic residual `BlockedBarrierOverlapOutcome` (`Assembly/Residuals.lean`), the facts common to both paths; return theorem `blockedBarrierOverlapReturn`; reached by 2 paths (distinct ledger histories from the root), with 2 distinct fact sets, each its own subtype in `Assembly/Residuals/BlockedBarrierOverlapOutcome.lean` (below).
- **Common facts (71).**
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
- **Subtypes** (one per distinct fact set; the two paths differ only by the arm of the `[160]` rate split through which the dense-packing residual enters the dense hot/cold pass `[162]`; each subtype implies the generic residual by `.toGeneric`).
  - `BlockedBarrierOverlapOutcome_DeficiencyAtOrAbove`, `[160]` first test no (`τ(θ) ≥ 1/4`); return theorem `blockedBarrierOverlapReturn_DeficiencyAtOrAbove`. Extra facts:
    72. `K .denseDeficiencyAtOrAbove`: Node `[160]`, first test, no arm: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
    - Total: 72 facts.
  - `BlockedBarrierOverlapOutcome_DeficiencyBelowRateFails`, `[160]` first test yes (`τ(θ) < 1/4`), second test no (private-carrier rate fails); return theorem `blockedBarrierOverlapReturn_DeficiencyBelowRateFails`. Extra facts:
    72. `K .denseDeficiencyBelow`: Node `[160]`, first test, yes arm: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison, the `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance.
    73. `K .route8RateFails`: Node `[160]`, second test, no arm: the complement of the private-carrier rate reading (`3/13 ≤ τ`), the manuscript's delicate density interval, carried as its own branch.
    - Total: 73 facts.

<a id="residual-182"></a>

### Node [182] (thm:main (iv), tex 359-363)

- **Configuration at G.** The first failed coverage implication of [178], [179] or [180] on the strict-surplus pair-code chain.
- **Lean.** `PairConditionalFactorizationOutcome` (`Assembly/Residuals.lean`); return theorem `pairConditionalFactorizationReturn`; reached by 6 paths (distinct ledger histories from the root) with 6 distinct fact sets, one subtype each in `Assembly/Residuals/PairConditionalFactorizationOutcome.lean`.
- **Generic residual: facts common to all six paths (33).**
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
- **Subtypes, one per distinct fact set (6).**  Each is `PairConditionalFactorizationOutcome ∧` its extra facts, with `.toGeneric` and a return theorem `pairConditionalFactorizationReturn_<label>` (one `get` per fact).  The side is the entry into the pair-code chain: free = `[130]` blocker-free arm and `[131]` free-pair count fails; blocked = `[130]` blocked arm with no (d)/(e) blocker, `[132]` no sparse exit, `[134]`--`[136]` token ledger and `[137]` blocked-side count fails.  The arm is the first failed implication: `[178]` factorization, `[179]` realizability, `[180]` increment coverage.
  - `PairConditionalFactorizationOutcome_freeFactorizationFails` (37 facts): the 33 above, plus
    - `K .independentPairFamily`
    - `K .freePairCountFails`
    - `K .freePairCodeUnrealized`
    - `K .pairFactorizationFails`
  - `PairConditionalFactorizationOutcome_freeRealizabilityFails` (40 facts): the 33 above, plus
    - `K .independentPairFamily`
    - `K .freePairCountFails`
    - `K .freePairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairRealizabilityFails`
  - `PairConditionalFactorizationOutcome_freeIncrementFails` (43 facts): the 33 above, plus
    - `K .independentPairFamily`
    - `K .freePairCountFails`
    - `K .freePairCodeUnrealized`
    - `K .pairConditionalFactorization`
    - `K .pairFailureOverlap`
    - `K .pairDemandReturns`
    - `K .pairSystemRealizability`
    - `K .pairSystemNoEarlyOutcome`
    - `K .pairSerialDemandSystem`
    - `K .pairIncrementFails`
  - `PairConditionalFactorizationOutcome_blockedFactorizationFails` (45 facts): the 33 above, plus
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
  - `PairConditionalFactorizationOutcome_blockedRealizabilityFails` (48 facts): the 33 above, plus
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
  - `PairConditionalFactorizationOutcome_blockedIncrementFails` (51 facts): the 33 above, plus
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
- **Lean.** `Route8JointBalanceOutcome` (`Assembly/Residuals.lean`, the generic residual: the 79 keys common to every path); return theorem `route8JointBalanceReturn`, called once, at `Assembly/RouteEight/Local.lean` (`selectedRouteEightUnifiedResidual`, the quotient-free arm after `[123]`, `[181]`, `[183]`--`[185]`). The 2080 paths from `selectedLedgerBoundary` carry 2080 distinct fact sets (probe of the elaborated `known` at every call site, R06, 2026-09-27), and form an exact product of arm blocks: `Route8JointBalanceOutcome_product := Route8JointBalanceOutcome ∧ Route8LanePrefix ∧ EntropyArm ∧ NetChargeContinuation` (`Assembly/Residuals/Route8JointBalanceOutcome.lean`; `.toGeneric`; return theorem `route8JointBalanceProductReturn`, parameterised by the arm blocks, each built by its block's `.ret` with one `get` per key). The factors are those of `Route8QuotientOutcome` (same composition, same incoming ledgers); the blocks are shared (`Assembly/Residuals/Route8Blocks.lean`). Every path is the 79 common keys plus exactly one block per factor, and every one of the `5 × 4 × 104 = 2080` combinations occurs. Totals: 99 to 136 facts. Not yet wired: the return site still calls `route8JointBalanceReturn`.
- **Facts carried (79).**
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
- **Product of arm blocks (keys beyond the 79 common facts).**
  Structure: `5 prefix × 4 entropy × NetChargeContinuation`; `NetChargeContinuation = TypeALane ∨ AbsorbedLane ∨ TypeBHighSurplusLane` (104 = 2·37 + 20 + 10); `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry (2) ∧ TypeAArm (37)`; `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour (3) ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour (3) ∧ Route8Deficit (2)) ∨ TypeAArmBlock_dischargedRetest`; `AbsorbedLane = NetChargeLaneBlock_absorbedGerm ∧ AbsorbedGerm (2) ∧ BChain`; `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`; `BChain = BChainEntryBlock ∧ BChainFan (2) ∧ BChainCertificate (5)`.
  - Prefix factor `Route8LanePrefix` (one of 5):
    - `Route8LanePrefixBlock_realizedColdBelow` (2): window package realized; cold route-8 rate below (`nearCubicRealized` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` (4): window package realized; cold route-8 rate at or above, density cap (`nearCubicRealized` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .densityCap`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow` (3): window package unrealized; dense deficiency at or above; cold route-8 rate below (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .denseDeficiencyAtOrAbove`
      - `K .windowPackageUnrealized`
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` (5): window package unrealized; dense deficiency at or above; cold route-8 rate at or above, density cap (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .denseDeficiencyAtOrAbove`
      - `K .densityCap`
      - `K .windowPackageUnrealized`
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
    - `NetChargeLaneBlock_absorbedGerm` (11): absorbed-germ lane
      - `K .absorbedConfigurationResidual`
      - `K .absorbedGermFanData`
      - `K .absorbedGermSplit`
      - `K .absorbedHandoffCore`
      - `K .coldCutStatesDistinct`
      - `K .coldExchangeBound`
      - `K .coldFailureDefectRoute`
      - `K .coldFailureRouting`
      - `K .coldGermCandidates`
      - `K .exactCollisionFails`
      - `K .typeBAbsorbedHalfEdge`
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
    - `TypeAArmBlock_route8Residual` (5): route-8 residual, then `TypeAExitFour` and `Route8Deficit`
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
  - Route-8 deficit `Route8Deficit` (one of 2):
    - `Route8DeficitBlock_holds` (5): deficit holds
      - `K .route8CarrierCutParity`
      - `K .route8LargeBudgetDeficit`
      - `K .route8NoSmallCoreEntry`
      - `K .route8TrueResidual`
      - `K .route8TwoCarrierEntry`
    - `Route8DeficitBlock_fails` (1): deficit fails
      - `K .route8LargeBudgetDeficitFails`
  - Absorbed cold germ `AbsorbedGerm` (one of 2):
    - `AbsorbedGermBlock_positive` (14): positive germ
      - `K .coldAbsorbedNeutralConfiguration`
      - `K .coldBranchClosed`
      - `K .coldCanonicalNeutralConfiguration`
      - `K .coldCanonicalReplacementSwap`
      - `K .coldCanonicalReplacementTrivial`
      - `K .coldGermDistinguished`
      - `K .coldGermFamilyPositive`
      - `K .coldGermNoneDistinguishing`
      - `K .coldGermNoneRealizing`
      - `K .coldGermRealized`
      - `K .coldGermRouted`
      - `K .coldGermSilent`
      - `K .coldPositiveGerm`
      - `K .coldSameInterfaceTable`
    - `AbsorbedGermBlock_none` (1): no positive germ
      - `K .coldNoPositiveGerm`
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
- **Generic residual: common facts (37), then its own arm as a disjunction.**
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
  - *Arm `system`* (one disjunct): `K .pairSystemEarlyOutcome`.
  - *Arm `increment`* (one disjunct): `K .pairSystemNoEarlyOutcome`, `K .pairSerialDemandSystem`, `K .pairIncrementCovered`, `K .pairIncrementEarlyOutcome`.
- **Subtypes** (`PairTypeBOutcome_<label> := PairTypeBOutcome ∧ <extra facts>`; each has `.toGeneric`):
  - **`PairTypeBOutcome_independentSystem`** ([130] independent (blocker-free) arm; [131] free-pair count fails; [179] early outcome); return theorem `pairTypeBIndependentSystemReturn`; 41 facts (37 common + 4 extra):
    38. `K .independentPairFamily`: Node `[130]`, blocker-free arm: the exact negation of `dependentPairFamily` at G's canonical activation (`Π_blk = ∅`).
    39. `K .freePairCountFails`: Node `[131]`, count fails: the exact negation of `freePairEntropySandwich`.
    40. `K .freePairCodeUnrealized`: Node `[131]`, complementary arm: the free-pair code is not realized by the skeleton class.
    41. `K .pairSystemEarlyOutcome`: Node `[179]`, alternatives (i)--(iv), retained for their literal route; (iv) is the first-separator handoff of the obstruction's own overlap support at `P₀`.
  - **`PairTypeBOutcome_independentIncrement`** ([130] independent (blocker-free) arm; [131] free-pair count fails; [179] serial arm; [180] covered increment; [180] early outcome); return theorem `pairTypeBIndependentIncrementReturn`; 44 facts (37 common + 7 extra):
    38. `K .independentPairFamily`: Node `[130]`, blocker-free arm: the exact negation of `dependentPairFamily` at G's canonical activation (`Π_blk = ∅`).
    39. `K .freePairCountFails`: Node `[131]`, count fails: the exact negation of `freePairEntropySandwich`.
    40. `K .freePairCodeUnrealized`: Node `[131]`, complementary arm: the free-pair code is not realized by the skeleton class.
    41. `K .pairSystemNoEarlyOutcome`: Node `[179]`, serial arm: the exact negation of `pairSystemEarlyOutcome`.
    42. `K .pairSerialDemandSystem`: Node `[179]`, alternative (v): the graph-realized serial demand system.
    43. `K .pairIncrementCovered`: Node `[180]`: corrected arithmetic or a periodic-response route.
    44. `K .pairIncrementEarlyOutcome`: Node `[180]`, periodic-response sparse-exit or Type B route.
  - **`PairTypeBOutcome_dependentSystem`** ([130] dependent arm (no blocker (d), no blocker (e)); [132] blocker arm; [137] blocked-side count fails; [179] early outcome); return theorem `pairTypeBDependentSystemReturn`; 49 facts (37 common + 12 extra):
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
  - **`PairTypeBOutcome_dependentIncrement`** ([130] dependent arm (no blocker (d), no blocker (e)); [132] blocker arm; [137] blocked-side count fails; [179] serial arm; [180] covered increment; [180] early outcome); return theorem `pairTypeBDependentIncrementReturn`; 52 facts (37 common + 15 extra):
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
- **Lean.** Generic residual `TypeBSublinearOutcome` (`Assembly/Residuals.lean`), return theorem `typeBSublinearReturn`: the 62 facts common to all paths. It is returned at one Lean site (`Assembly/RouteEight/Local.lean`, the negative arm of `typeBSublinearDichotomy` in `selectedRouteEightUnifiedResidual`), which 2080 paths from the root reach with 2080 distinct fact sets. Product form: `TypeBSublinearOutcome_product` (`Assembly/Residuals/TypeBSublinearOutcome.lean`), below.
- **Facts carried (62).**
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
- **Product of arm blocks (user ruling).** The 2080 paths hold 2080 distinct fact sets. Each is exactly the 62 generic facts above together with the keys of one block choice in each factor below. The chosen blocks are pairwise key-disjoint, and every combination occurs on exactly one path, so the product is full: 2080 = 5 (prefix) × 4 (entropy) × 104 (continuation), with 104 = 74 (Type A lane) + 20 (absorbed lane) + 10 (Type B high-surplus lane). The check was made path by path against the elaborated ledgers.
  - Lean: `TypeBSublinearOutcome_product := TypeBSublinearOutcome ∧ Route8LanePrefix ∧ EntropyArm ∧ NetChargeContinuation` (`Assembly/Residuals/TypeBSublinearOutcome.lean`), with `.toGeneric` and return theorem `typeBSublinearProductReturn`. The blocks are the shared route-8 blocks of `Assembly/Residuals/Route8Blocks.lean`, the same ones `Route8QuotientOutcome` uses; each has a `.ret` theorem with one `get` per key.
  - `NetChargeContinuation = TypeALane ∨ AbsorbedLane ∨ TypeBHighSurplusLane`.
  - `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry ∧ TypeAArm`, where `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour ∧ Route8Deficit) ∨ TypeAArmBlock_dischargedRetest`.
  - `AbsorbedLane = NetChargeLaneBlock_absorbedGerm ∧ AbsorbedGerm ∧ BChain`.
  - `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`.
  - `BChain = BChainEntryBlock ∧ BChainFan ∧ BChainCertificate` (2 fan blocks × 5 certificate blocks).
  - Total facts per path: 62 + the chosen blocks, from 82 to 119.
- **Arm blocks (each with its arms, the number of paths it is on, and its keys).**
  - **Prefix factor `Route8LanePrefix` (5 blocks).**
    - `Route8LanePrefixBlock_realizedColdBelow` ([158] window package realized; [146] θ < 1/78); on 416 paths; 2 keys:
      - `K .coldRoute8Below`: Node `[146]`, yes: the canonical packing lies below the route-8 private-carrier threshold.
      - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of ...
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` ([158] window package realized; [146] θ ≥ 1/78; [153] bounded cold mass under the density cap); on 416 paths; 4 keys:
      - `K .coldMassBounded`: Node `[153]`, complementary arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
      - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
      - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in the object's own dyadic scale.
      - `K .windowPackageRealized`: Node `[21]`, `lem:p13-window-package` with `def:target-rank` and the realization sentence used in `lem:p13-window-package` and `prop:p13-density`, "all target-complete window states are realized by labelled near-cubic skeletons": the canonical multi-scale package of the fixed maximal packing is a family of ...
    - `Route8LanePrefixBlock_unrealizedDenseBelow` ([158] window package unrealized; [160] first test: dense deficiency below); on 416 paths; 2 keys:
      - `K .denseDeficiencyBelow`: On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact large-budget net-deficiency comparison holds at the fixed maximal packing — the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n` allowance, i.e.
      - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow` ([158] unrealized; [160] dense deficiency at or above; [146] θ < 1/78); on 416 paths; 3 keys:
      - `K .coldRoute8Below`: Node `[146]`, yes: the canonical packing lies below the route-8 private-carrier threshold.
      - `K .denseDeficiencyAtOrAbove`: Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
      - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` ([158] unrealized; [160] dense deficiency at or above; [146] θ ≥ 1/78; [153] bounded cold mass under the density cap); on 416 paths; 5 keys:
      - `K .coldMassBounded`: Node `[153]`, complementary arm: the cold mass is within the two branch-excess slacks; the spine continues to `[24]`'s density cap.
      - `K .coldRoute8AtOrAbove`: Node `[146]`, no: the same canonical packing is not below that threshold.
      - `K .denseDeficiencyAtOrAbove`: Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact allowance, on which the net-charge collision does not fire.
      - `K .densityCap`: Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing in the object's own dyadic scale.
      - `K .windowPackageUnrealized`: The complementary arm of the `[21]` realization decision: the fixed maximal packing's full package code is *not* realized canonically by the labelled skeletons of the current object's class — the residual on which the manuscript's `[21]` sentence fails, carried as a branch of its own.
  - **Entropy factor `EntropyArm` (4 blocks).**
    - `EntropyArmBlock_high` ([50] remainder entropy high; [53] entropy cap); on 520 paths; 3 keys:
      - `K .entropyCapBound`: Node `[54]`: the independently realized window/remainder code fits in the labelled skeleton class.
      - `K .entropyPackageDemand`: Node `[52]`: the window package and the remainder accounting, joined.
      - `K .remainderEntropyHigh`: Node `[50]`, yes arm — node `[51]`, the high-entropy remainder branch: `η(R) ≥ (1/d)·log₂ n`, i.e.
    - `EntropyArmBlock_lowNonrepetitive` ([50] remainder entropy low; local-type coordinate non-repetitive); on 520 paths; 2 keys:
      - `K .localTypeCoordinateNonrepetitive`: `prop:two-budget` (c): the same literal coordinate is not structurally repetitive.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
    - `EntropyArmBlock_lowRepetitiveWedgeFree` ([50] remainder entropy low; local-type coordinate repetitive; root-wedge split wedge-free); on 520 paths; 4 keys:
      - `K .dominantRootedType`: `lem:dominant-type`: the repetitive coordinate has a single rooted radius-two type outside only the registered finite `o(n)` allowance.
      - `K .dominantRootedTypeWedgeFree`: The wedge-free subarm after `lem:dominant-type`; the manuscript makes no translate-rank claim and passes this arm to the large-budget analysis.
      - `K .localTypeCoordinateRepetitive`: `prop:two-budget` (b): on the low-entropy residual, the radius-two rooted-type coordinate lies below the exact finite relabelling threshold.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
    - `EntropyArmBlock_lowRepetitiveWedge` ([50] remainder entropy low; local-type coordinate repetitive; root-wedge split wedge type); on 520 paths; 5 keys:
      - `K .dominantRootedType`: `lem:dominant-type`: the repetitive coordinate has a single rooted radius-two type outside only the registered finite `o(n)` allowance.
      - `K .dominantRootedWedgeType`: The literal incoming wedge subarm of `lem:translates-independent`: the preceding executor proved the dominant rooted type and the decision found an internal root wedge in that same type.
      - `K .independentObstructionTranslates`: Nodes `[51]`--`[52]`, `lem:translates-independent`: a dominant rooted radius-`r` type with an internal root wedge admits a maximal `2r`-separated family of translates.
      - `K .localTypeCoordinateRepetitive`: `prop:two-budget` (b): on the low-entropy residual, the radius-two rooted-type coordinate lies below the exact finite relabelling threshold.
      - `K .remainderEntropyLow`: Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch `prop:two-budget` (b) and (c) share.
  - **Absorbed lane `AbsorbedLane` (20 = 2 × 10).**
    - `NetChargeLaneBlock_absorbedGerm` ([59] net charge nonnegative; [57]/[173] exact collision fails; [177] counted core; [153] (★)); on 400 paths; 11 keys:
      - `K .absorbedConfigurationResidual`: Node `[174]`, `lem:exact-collision-test`, the consequence of the failed collision: the failure witness packing `P` of `[173]` satisfies `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`, `A = netChargeCoefficient`, the manuscript's `C ≥ (n − 73|𝒫_hot| − 4(σ_W − σ_R))/73` without subtraction: the residual carries ...
      - `K .absorbedGermFanData`: Node `[177]`, `lem:absorbed-germ-fan-data` (ii): every selected branch-excess half-edge outside node `[153]`'s exact subcubic candidate class meets a vertex of degree above the threshold, a heavy centre, and is decorated handoff fan data for Type B.
      - `K .absorbedGermSplit`: Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy — every selected branch-excess half-edge's first-failure support is subcubic (a charged candidate germ) or meets a heavy centre whose neighbours all sit at the threshold (node `[10]`).
      - `K .absorbedHandoffCore`: Node `[177]`, yes: a counted remainder core exists at the heavy centre of `G`'s canonical absorbed half-edge.
      - `K .coldCutStatesDistinct`: Node `[153]`, distinct-states arm: G's pinned cut states along each retained cold corridor are pairwise distinct up to the first failure.
      - `K .coldExchangeBound`: `def:cold-corridor-first-failure`: the `M_cold = Q_cold + 30` exchange bound on the retained corridor of every selected half-edge of G that reaches its successor stub before `Q_cold + 1` states.
      - `K .coldFailureDefectRoute`: `lem:cold-corridor-first-failure` (ii): an (F2) pair of prefixes of one of G's corridors is a target-defective quotient.
      - `K .coldFailureRouting`: `lem:cold-corridor-first-failure`: the routing (F1)--(F5) of G's first failures, with (F2) excluded on the (★) arm.
      - `K .coldGermCandidates`: Node `[153]`: a positive current-residual bounded-germ family.
      - `K .exactCollisionFails`: Node `[173]`, `lem:exact-collision-test`, no arm: node `[56]`'s collision, decided exactly on the current object, fails at some maximal packing — the absorbed-germ residual `[174]`.
      - `K .typeBAbsorbedHalfEdge`: Node `[175]`, yes, read at `[177]`: some selected corridor meets a high-degree vertex --- `G`'s canonical absorbed half-edge exists.
    - `AbsorbedGermBlock_none` ([175] no positive germ); on 200 paths; 1 keys:
      - `K .coldNoPositiveGerm`: Node `[175]`, no arm: every selected corridor meets a high-degree vertex.
    - `AbsorbedGermBlock_positive` ([175] positive germ; [154] G1/G2 tests; [163] neutral configuration); on 200 paths; 14 keys:
      - `K .coldAbsorbedNeutralConfiguration`: Node `[176]` on the absorbed-configuration residual (`lem:absorbed-germ-fan-data` (i)): on the G2-silent arm, the neutral equal-length configuration of G's silent extracted family, an (F5) configuration (terminal or repeated-state); the dense-residual terminality of node `[162]` is not assumed.
      - `K .coldBranchClosed`: `thm:cold-branch-quantitative-closure`, local part: the local cold-terminal exclusion at G (no global terminal contradiction).
      - `K .coldCanonicalNeutralConfiguration`: Node `[163]`, no-arm: no neutral zero-increment germ of the incoming extracted family has a graph-realized second strand; its `E` is therefore the canonical-replacement case of `[165]`--`[166]`.
      - `K .coldCanonicalReplacementSwap`: Node `[165]`: for every neutral configuration, replacing `Q` by a distinct canonical representative `E` gives a baseline, target-avoiding graph with the same vertex and edge counts, while `E` strictly precedes `Q` in the fixed canonical piece order.
      - `K .coldCanonicalReplacementTrivial`: Node `[166]`: refined minimality forces every neutral configuration's canonical replacement to be the corridor piece itself, `E = Q`.
      - `K .coldGermDistinguished`: `lem:cold-bounded-germ-trichotomy` (G2): the hit-distinguished configurations of G's extracted family.
      - `K .coldGermFamilyPositive`: Node `[153]`, linear arm: the literal disjoint family retained by `coldGermCandidates` is nonempty after both surplus losses are paid.
      - `K .coldGermNoneDistinguishing`: Node `[154]`, the exact complement of `coldGermSomeDistinguishing`: every active configuration is silent (G3 or the equal-length table).
      - `K .coldGermNoneRealizing`: Node `[154]`, the exact complement of `coldGermSomeRealizing`.
      - `K .coldGermRealized`: `lem:cold-bounded-germ-trichotomy`: the realized configurations of G's extracted family (G1 is closed, so none is hit-realized).
      - `K .coldGermRouted`: `lem:cold-bounded-germ-trichotomy`: every bounded configuration of G's extracted family is routed (G1, G2 or G3).
      - `K .coldGermSilent`: `lem:cold-bounded-germ-trichotomy` (G3): the silent configurations of G's extracted family.
      - `K .coldPositiveGerm`: 
      - `K .coldSameInterfaceTable`: `lem:cold-same-interface-table`: the finite same-interface table of G's silent configurations.
  - **Type A lane `TypeALane` (74 = 2 × 37; 37 = 3 × 10 + 3 × 2 + 1).**
    - `NetChargeLaneBlock_typeALowSurplus` ([59] net charge negative; [62] Type A; [88] saturated receiver); on 1480 paths; 11 keys:
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
    - `TypeAEntryBlock_visible` ([93] visible entry; [95]/[97]/[99] exits (1)--(3) free); on 740 paths; 4 keys:
      - `K .typeAExitOneFree`: Node `[95]`, no arm — the entry of node `[97]`: no anchored return through any completion port of any saturated receiver of any Type A support has accepted length, so exit `(1)` is not the exit this branch realizes and the saturated exit list continues at exit `(2)`.
      - `K .typeAExitThreeFree`: Node `[99]`, no arm — the entry of node `[101]`: every shared window of the packing satisfies its legal-label relation at every outside connector, so exit `(3)` is not the exit this branch realizes and the saturated exit list continues at exit `(4)`.
      - `K .typeAExitTwoFree`: Node `[97]`, no arm — the entry of node `[99]`: at every saturated receiver of every Type A support, no two receiver-entry returns through one of its completion ports are internally vertex-disjoint with accepted total length, so exit `(2)` is not the exit this branch realizes and the saturated exit list continues ...
      - `K .typeAVisibleEntry`: Node `[93]`, yes arm — the entry of the saturated exit chain at node `[95]`: some completion port of a saturated receiver of the Type A support carries `s` visible receiver-entry returns, in the sense of `def:typeA-visible-load`.
    - `TypeAEntryBlock_noVisible` ([93] no visible entry); on 740 paths; 2 keys:
      - `K .typeANoVisibleEntry`: Node `[93]`, no arm: no saturated receiver of `X₀` has an overloaded completion port.
      - `K .typeAVisibleFirstExcess`: Node `[93]`, no arm — node `[94]`, `lem:typeA-silent-excess-count`: no saturated receiver of the Type A support has a completion port carrying `s` visible receiver-entry returns, so the visible-first excess basins of `def:typeA-excess-basin` are silent and carry the whole excess, `S_sil^exc(X) ≥ s·D_A(X)`.
    - `TypeAArmBlock_decorated` ([103]/[105] exits (5), (6) free; [107] exit (7) handoff, decorated to the Type B chain); on 1200 paths; 6 keys:
      - `K .typeAExitFiveFree`: Node `[103]`, no arm: the exact selected saturated-handoff residual after no exit `(4)` carries no target-complete proper-support compression, so the branch may continue to exit `(6)`.
      - `K .typeAExitSevenEnvelope`: Node `[108]`: the canonical exit-`(7)` separation and envelope of `X₀` at the terminal state.
      - `K .typeAExitSevenHandoff`: Node `[108]`, on node `[107]`'s yes arm — exit `(7)` of `def:typeA-saturated-exits`: *"a high-degree decorated handoff fan envelope is produced"*, at the visible saturated port node `[93]` delivered.
      - `K .typeAExitSixFree`: Node `[105]`, no arm: that same selected residual has no exit-`(6)` delocalization, so it can continue to exit `(7)`.
      - `K .typeASaturatedHandoffExitFourFree`: `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current saturated receiver/peeling state; this is the predecessor of exit `(5)`.
      - `K .typeBDecoratedAssignedSupport`: Node `[65]` on the decorated lane: the exact exit-`(7)` envelope, its Type-B centres and assigned first-neighbour supports, and every clause of `lem:decorated-fan-admissibility`, all published on the same residual for the common Type B continuation.
    - `TypeAArmBlock_route8Residual` ([103]/[105] exits (5), (6) free; [107] exit (7) free: route-8 residual profile); on 240 paths; 5 keys:
      - `K .route8ResidualProfile`: Node `[110]`, exit `(8)`: the selected route-8 residual satisfies the silent-core residual profile.
      - `K .typeAExitFiveFree`: Node `[103]`, no arm: the exact selected saturated-handoff residual after no exit `(4)` carries no target-complete proper-support compression, so the branch may continue to exit `(6)`.
      - `K .typeAExitSevenFree`: Node `[107]`, no arm — the entry of node `[109]`: no high-degree decorated handoff fan envelope is produced at any visible port of any saturated receiver of any Type A support, so exit `(7)` is not the exit this branch realizes and the saturated exit list continues at exit `(8)`, the route-8 residual of ...
      - `K .typeAExitSixFree`: Node `[105]`, no arm: that same selected residual has no exit-`(6)` delocalization, so it can continue to exit `(7)`.
      - `K .typeASaturatedHandoffExitFourFree`: `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current saturated receiver/peeling state; this is the predecessor of exit `(5)`.
    - `TypeAArmBlock_dischargedRetest` ([101] exit (4) peeled; [102] recompute-L4 retest discharges the receiver); on 40 paths; 4 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAExitFourReceiverDischarged`: Node `[102]`, no-loop arm: after the exit-`(4)` peel, the selected receiver is no longer saturated at the peeled residual, so its remaining receiver charge is nonnegative by `lem:typeA-exit4-peeling-charge`.
      - `K .typeAPeeledUnsaturatedDischarge`: Node `[91]` after peeling: `|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|`.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `TypeAExitFourBlock_absent` ([101] exit (4) absent); on 480 paths; 1 keys:
      - `K .typeAExitFourAbsent`: Node `[101]`, no arm: the entry state of the exit-chain receiver of `X₀` has no exit `(4)`.
    - `TypeAExitFourBlock_peeledVisible` ([101] exit (4) peeled; [89] peeled visible entry); on 480 paths; 7 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAPeeledExitOneFree`: Node `[95]` after peeling, no arm.
      - `K .typeAPeeledExitThreeFree`: Node `[99]` after peeling, no arm.
      - `K .typeAPeeledExitTwoFree`: Node `[97]` after peeling, no arm.
      - `K .typeAPeeledSaturatedReceiver`: Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated at its terminal peeling set.
      - `K .typeAPeeledVisibleEntry`: Node `[93]` after peeling, yes arm: the terminal state has an overloaded port.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `TypeAExitFourBlock_peeledNoVisible` ([101] exit (4) peeled; [89] no peeled visible entry); on 480 paths; 5 keys:
      - `K .typeAExitFourPeeled`: Node `[102]`: the exit-`(4)` witness has been charged to the peeling ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load condition and dropping the residual load by one.
      - `K .typeAPeeledNoVisibleEntry`: Node `[93]` after peeling, no arm: the terminal state has no overloaded port.
      - `K .typeAPeeledSaturatedReceiver`: Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated at its terminal peeling set.
      - `K .typeAPeeledSilentExcess`: Node `[94]` after peeling: the residual excess `E₄(w)` is nonempty and silent.
      - `K .typeASaturatedHandoffExitFour`: `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current saturated receiver/peeling state.
    - `Route8DeficitBlock_holds` ([113] large-budget deficit; [115] small core; [117] two-support entry); on 120 paths; 5 keys:
      - `K .route8CarrierCutParity`: Node `[114]`, `lem:typeA-carrier-cut-parity`: every surviving target event which uses an edge internal to its selected trace basin and an edge leaving its ambient piece records at least two distinct incidences from the canonical essential carrier core.
      - `K .route8LargeBudgetDeficit`: Node `[113]`, yes arm.
      - `K .route8NoSmallCoreEntry`: Node `[115]`, no arm.
      - `K .route8TrueResidual`: Node `[114]`, `def:typeA-true-route8-residual`: every actual indexed entry of the selected route-`8` collection satisfies clauses (R1)--(R4).
      - `K .route8TwoCarrierEntry`: Node `[117]`, yes: some indexed route-8 entry of `𝒳_A` has at most `δ` private essential carriers (`prop:typeA-route8-carrier-reduction`).
    - `Route8DeficitBlock_fails` ([113] large-budget deficit fails); on 120 paths; 1 keys:
      - `K .route8LargeBudgetDeficitFails`: Node `[113]`, no arm.
  - **Type B high-surplus lane `TypeBHighSurplusLane` (10).**
    - `NetChargeLaneBlock_typeBHighSurplus` ([59] net charge negative; [62] Type B); on 200 paths; 5 keys:
      - `K .negativeSupport`: Node `[61]`: `prop:negative-net-charge`.
      - `K .netChargeCap`: Node `[60]`: the large-budget remainder has negative total net charge once the paper's explicit sufficiently-large predicate holds.
      - `K .netChargeNegative`: Node `[59]`, no arm: `N₀(R) < 0` for that same selected packing.
      - `K .typeBAssignedSupport`: Node `[65]` at the `[64]` entry: the ordinary Type B assigned support.
      - `K .typeBHighSurplus`: Node `[62]`, yes arm — node `[64]`, Type B: the selected negative support carries assigned high-degree surplus.
  - **B-chain `BChain` (10 = 2 × 5).**
    - `BChainEntryBlock` (Type B chain entry, common to every B-chain arm); on 1800 paths; 7 keys:
      - `K .compatiblePairFanClosure`: `lem:compatible-pair-fan-closure`: compatible open ports recorded by one assigned profile are distinct fan-closed ports.
      - `K .compatiblePairTypeBRouting`: `cor:compatible-pair-typeB-routing`: a recorded compatible open pair gives the positive local Type-B deficit.
      - `K .fanCertificateCap`: Node `[70]`: the certificate-marked fan-degree cap.
      - `K .fanClosedPortTypeBRouting`: `prop:fan-closed-port-typeB-routing`: two or more fan-closed ports give the positive local Type-B deficit bound.
      - `K .typeBExclusionResidual`: Node `[76]`/`[85]`: Type B cannot carry the linear deficit outside route `8`; the B2-paid support keeps its deficit in its remaining core, and a bridge-residual support is charged to its assigned surplus.
      - `K .typeBFanEntry`: Nodes `[65]`/`[66]`: the common Type B fan support entry (`def:typeB-assigned-ledger`): a canonical core with its assigned centres — the ordinary support's own high centres at `[65]`, or the decorations of the handoff envelope at the dashed input `[66]` — nonempty and all high.
      - `K .typeBRoute8Entry`: Node `[77]`: the Type B entry into route `8`; a negative Type B support hands a negative remaining core to route `8` or is a bridge residual charged to its surplus.
    - `BChainFanBlock_heavyCentre` ([68] heavy centre); on 900 paths; 6 keys:
      - `K .triangularCrossShoulder`: `lem:triangular-cross-shoulder`: two cross edges between distinct triangular shoulder pairs force a high shoulder; after that branch is routed away, the surviving cross edges have cardinality at most one.
      - `K .triangularFanCore`: Node `[79]`, `def:triangular-fan-core`: the shoulder sets, induced core vertex set, and completion-incidence classifications of every nonempty triangular-port family at a heavy centre.
      - `K .triangularFirstLanding`: `lem:triangular-first-landing`: every completion incidence in a triangular fan core is uniquely central, cross-triangular, or outside.
      - `K .triangularPortTypeBRouting`: `prop:triangular-port-typeB-routing`: a degree-`k` heavy triangular family of exactly `k - 2` assigned ports gives the stronger positive local Type-B deficit bound `(5k - 19) / 4`.
      - `K .typeBFanHeavyCentre`: Node `[68]`, yes arm, on either literal `[65]` input: some assigned centre of the canonical support, or an actual centre of an indexed `[177]` handoff datum, is *heavy* — degree above the high-centre degree `δ + 1` (`d_G(h) > 4` at the manuscript's baseline).
      - `K .typeBFanLocalDichotomy`: Node `[69]` at the `[64]` entry: `cor:heavy-center-local-dichotomy` at every heavy fan centre of the ordinary Type B support — a fan-compatible open pair, or at least `d_G(h) − 2` triangular ports, hence three.
    - `BChainFanBlock_degreeFour` ([68] degree four); on 900 paths; 2 keys:
      - `K .typeBFanDegreeFourCentres`: Node `[68]`, no arm, on either literal `[65]` input — the entry of node `[78]`: every assigned centre of the canonical support, or a retained witness for every indexed `[177]` datum, has degree exactly `δ + 1` (`d_G(h) = 4` at the manuscript's baseline).
      - `K .typeBFanDegreeFourProfile`: Nodes `[78]`--`[79]` at the `[64]` entry: the degree-four fan profile of the ordinary Type B support.
    - `BChainCertificateBlock_residual` ([71]/[80] certificate labelling: residual); on 360 paths; 2 keys:
      - `K .fanCertificateResidual`: Node `[71]`/`[80]`, no arm: some assigned centre of the Type B support carries no fan-certificate labelling (G's canonical labelling is absent).
      - `K .fanCertificateResidualMass`: Nodes `[75]`/`[84]` on the certificate-residual arm: the support-level bound `lem:typeB-bridge-deficit-bound` at the fan-certificate residual support.
    - `BChainCertificateBlock_b2Choice` ([71]/[80] marked; [72] B2 disjoint); on 360 paths; 6 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBB2Choice`: Node `[72]`, yes arm: the local B1 ledger is complete and B2 holds at the Type B support: its certificate-marked assigned centres have a pairwise-disjoint choice of candidate entries on the assigned fan envelopes of the support.
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBDisjointLedger`: Node `[74]`, B2(a)--(d): the Type B support is B2-paid; its canonical B2 ledger exists with its exact augmented-ledger refinement, the inherited Type A hygiene of every remaining component, and the grouped exit-`(7)` handoff coverage used by B2(d).
      - `K .typeBExcluded`: Node `[74]`, `prop:typeB-bridge-reduction`: the remaining core of the Type B support's canonical B2 ledger carries the whole deficit.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
    - `BChainCertificateBlock_overlapObstruction` ([71]/[80] marked; [72] B2 overlap obstruction); on 360 paths; 6 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBGlobalLocalBridge`: Node `[73]`/`[83]`: the canonical minimal obstruction together with all five global-to-local reflection clauses.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
      - `K .typeBOverlapObstruction`: Node `[72]`, no arm — the entry of `[73]`: B2's disjoint-carrier clause fails at the certificate-marked Type B support, which by `lem:typeB-bridge-to-overlap` carries G's canonical minimal Type B overlap obstruction of `def:typeB-overlap-obstruction`.
      - `K .typeBOverlapObstructionMass`: Nodes `[75]`/`[84]` on the B2-failure arm: the support-level bound `lem:typeB-bridge-deficit-bound` at the reflected obstructed support.
    - `BChainCertificateBlock_degreeFourClosed` ([71]/[80] marked; [81] degree-four ledger closed); on 360 paths; 5 keys:
      - `K .fanCertificateMarked`: Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support carries G's canonical fan-certificate labelling, under the label-packing cap (`def:marked-typeB-fan`).
      - `K .typeBDegreeFourClosed`: Node `[82]`: certificate-closed (`c ≤ 1`, `lem:typeB-exclusion` Step 1) or B2-paid with its remaining core carrying the whole deficit, at the degree-four Type B support.
      - `K .typeBDegreeFourLedger`: Node `[81]`, yes: `c ≤ 1` at every assigned centre, or `c ≥ 2` with the B2 disjoint choice, at the degree-four Type B support.
      - `K .typeBDirectCycleFree`: Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned centre of the marked Type B support is direct-cycle-free at `P₀` (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`); a direct configuration would be a cycle of accepted length.
      - `K .typeBHybridEntry`: Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.
    - `BChainCertificateBlock_degreeFourOverlap` ([71]/[80] marked; [81] degree-four overlap); on 360 paths; 6 keys:
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
- **Lean.** `Route8QuotientOutcome` (`Assembly/Residuals.lean`, the generic residual: the 64 keys common to every path); return theorem `route8QuotientReturn`, called once, at `Assembly/RouteEight/Local.lean` (`selectedRouteEightUnifiedResidual`, arm `[348]`). The 2080 paths from `selectedLedgerBoundary` carry 2080 distinct fact sets (probe of the elaborated `known` at every call site, R09, 2026-09-27), and form an exact product of arm blocks: `Route8QuotientOutcome_product := Route8QuotientOutcome ∧ Route8LanePrefix ∧ EntropyArm ∧ NetChargeContinuation` (`Assembly/Residuals/Route8QuotientOutcome.lean`; `.toGeneric`; return theorem `route8QuotientProductReturn`, parameterised by the arm blocks, each built by its block's `.ret` with one `get` per key). The blocks are shared (`Assembly/Residuals/Route8Blocks.lean`). Every path is the 64 common keys plus exactly one block per factor, and every one of the `5 × 4 × 104 = 2080` combinations occurs. Totals: 84 to 121 facts. Not yet wired: the return site still calls `route8QuotientReturn`.
- **Facts carried (64).**
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
- **Product of arm blocks (keys beyond the 64 common facts).**
  Structure: `5 prefix × 4 entropy × NetChargeContinuation`; `NetChargeContinuation = TypeALane ∨ AbsorbedLane ∨ TypeBHighSurplusLane` (104 = 2·37 + 20 + 10); `TypeALane = NetChargeLaneBlock_typeALowSurplus ∧ TypeAEntry (2) ∧ TypeAArm (37)`; `TypeAArm = (TypeAArmBlock_decorated ∧ TypeAExitFour (3) ∧ BChain) ∨ (TypeAArmBlock_route8Residual ∧ TypeAExitFour (3) ∧ Route8Deficit (2)) ∨ TypeAArmBlock_dischargedRetest`; `AbsorbedLane = NetChargeLaneBlock_absorbedGerm ∧ AbsorbedGerm (2) ∧ BChain`; `TypeBHighSurplusLane = NetChargeLaneBlock_typeBHighSurplus ∧ BChain`; `BChain = BChainEntryBlock ∧ BChainFan (2) ∧ BChainCertificate (5)`.
  - Prefix factor `Route8LanePrefix` (one of 5):
    - `Route8LanePrefixBlock_realizedColdBelow` (2): window package realized; cold route-8 rate below (`nearCubicRealized` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_realizedColdAtOrAbove` (4): window package realized; cold route-8 rate at or above, density cap (`nearCubicRealized` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .densityCap`
      - `K .windowPackageRealized`
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow` (3): window package unrealized; dense deficiency at or above; cold route-8 rate below (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetColdRate`)
      - `K .coldRoute8Below`
      - `K .denseDeficiencyAtOrAbove`
      - `K .windowPackageUnrealized`
    - `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` (5): window package unrealized; dense deficiency at or above; cold route-8 rate at or above, density cap (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`)
      - `K .coldMassBounded`
      - `K .coldRoute8AtOrAbove`
      - `K .denseDeficiencyAtOrAbove`
      - `K .densityCap`
      - `K .windowPackageUnrealized`
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
    - `NetChargeLaneBlock_absorbedGerm` (11): absorbed-germ lane
      - `K .absorbedConfigurationResidual`
      - `K .absorbedGermFanData`
      - `K .absorbedGermSplit`
      - `K .absorbedHandoffCore`
      - `K .coldCutStatesDistinct`
      - `K .coldExchangeBound`
      - `K .coldFailureDefectRoute`
      - `K .coldFailureRouting`
      - `K .coldGermCandidates`
      - `K .exactCollisionFails`
      - `K .typeBAbsorbedHalfEdge`
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
    - `TypeAArmBlock_route8Residual` (5): route-8 residual, then `TypeAExitFour` and `Route8Deficit`
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
  - Route-8 deficit `Route8Deficit` (one of 2):
    - `Route8DeficitBlock_holds` (5): deficit holds
      - `K .route8CarrierCutParity`
      - `K .route8LargeBudgetDeficit`
      - `K .route8NoSmallCoreEntry`
      - `K .route8TrueResidual`
      - `K .route8TwoCarrierEntry`
    - `Route8DeficitBlock_fails` (1): deficit fails
      - `K .route8LargeBudgetDeficitFails`
  - Absorbed cold germ `AbsorbedGerm` (one of 2):
    - `AbsorbedGermBlock_positive` (14): positive germ
      - `K .coldAbsorbedNeutralConfiguration`
      - `K .coldBranchClosed`
      - `K .coldCanonicalNeutralConfiguration`
      - `K .coldCanonicalReplacementSwap`
      - `K .coldCanonicalReplacementTrivial`
      - `K .coldGermDistinguished`
      - `K .coldGermFamilyPositive`
      - `K .coldGermNoneDistinguishing`
      - `K .coldGermNoneRealizing`
      - `K .coldGermRealized`
      - `K .coldGermRouted`
      - `K .coldGermSilent`
      - `K .coldPositiveGerm`
      - `K .coldSameInterfaceTable`
    - `AbsorbedGermBlock_none` (1): no positive germ
      - `K .coldNoPositiveGerm`
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
- **Lean.** `Route8RateFailsOutcome` (`Assembly/Residuals.lean`); return theorem `route8RateFailsReturn`; reached by 12 paths (distinct ledger histories from the root).
- **Facts carried (42).**
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
- **On some paths only, not carried (14).** Gated by an arm of:
  - [50] low arm, local-type coordinate (lem:dominant-type): `dominantRootedType`, `localTypeCoordinateNonrepetitive`, `localTypeCoordinateRepetitive`.
  - [50] remainder entropy: `entropyPackageDemand`, `remainderEntropyHigh`, `remainderEntropyLow`.
  - [160] first test (tau < 1/4): `denseDeficiencyAtOrAbove`, `denseDeficiencyBelow`.
  - [50] low arm, root-wedge split (lem:dominant-type): `dominantRootedTypeWedgeFree`, `dominantRootedWedgeType`.
  - [158] window package realized: `windowPackageRealized`, `windowPackageUnrealized`.
  - [53] entropy cap: `entropyCapBound`.
  - [50] low arm, root-wedge split (lem:dominant-type); [50] low arm, local-type coordinate (lem:dominant-type): `independentObstructionTranslates`.

<a id="residual-187-cold-terminal"></a>

### Node [187] (local cold-terminal exclusion) (thm:main (vi), tex 369-378)

- **Configuration at G.** The local cold-terminal exclusion of thm:cold-branch-quantitative-closure without a global terminal contradiction.
- **Lean.** `ColdBranchClosedOutcome` (`Assembly/Residuals.lean`); return theorem `coldBranchClosedReturn`; reached by 104 paths (distinct ledger histories from the root).
- **Facts carried (57).**
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
- **On some paths only, not carried (42).** Gated by an arm of:
  - [163] on the absorbed residual; [163] neutral configuration: `coldCanonicalNeutralConfiguration`, `coldCanonicalReplacementSwap`, `coldCanonicalReplacementTrivial`.
  - [153] linear / bounded cold mass: `coldMassBounded`, `coldMassLinear`, `densityCap`.
  - [50] low arm, local-type coordinate (lem:dominant-type): `dominantRootedType`, `localTypeCoordinateNonrepetitive`, `localTypeCoordinateRepetitive`.
  - [50] remainder entropy: `entropyPackageDemand`, `remainderEntropyHigh`, `remainderEntropyLow`.
  - [57]/[173] exact collision: `absorbedConfigurationResidual`, `exactCollisionFails`.
  - [177] counted core: `absorbedF4Charge`, `absorbedHandoffCoreAbsent`.
  - [154] G2 test: `coldGermNoneDistinguishing`, `coldGermSomeDistinguishing`.
  - [162] heavy entry: `coldHeavyEntryTerminal`, `denseColdCorridorsTerminal`.
  - [175] positive germ: `coldNoPositiveGerm`, `coldPositiveGerm`.
  - [146] theta < 1/78: `coldRoute8AtOrAbove`, `coldRoute8Below`.
  - [160] first test (tau < 1/4): `denseDeficiencyAtOrAbove`, `denseDeficiencyBelow`.
  - [50] low arm, root-wedge split (lem:dominant-type): `dominantRootedTypeWedgeFree`, `dominantRootedWedgeType`.
  - [160] second test / route-8 entry rate: `route8Rate`, `route8RateFails`.
  - [175] read at [177]: `typeBAbsorbedHalfEdge`, `typeBAbsorbedHalfEdgeAbsent`.
  - [158] window package realized: `windowPackageRealized`, `windowPackageUnrealized`.
  - [175] positive germ; [154] G2 test; [153] linear / bounded cold mass: `coldAbsorbedNeutralConfiguration`.
  - [175] positive germ; [153] linear / bounded cold mass: `coldGermFamilyPositive`.
  - [154] G1 test: `coldGermNoneRealizing`.
  - [175] positive germ; [175] read at [177]: `coldSelectedFamilyEmpty`.
  - [53] entropy cap: `entropyCapBound`.
  - [50] low arm, root-wedge split (lem:dominant-type); [50] low arm, local-type coordinate (lem:dominant-type): `independentObstructionTranslates`.
  - [53] entropy cap; [50] remainder entropy: `largeBudgetResidual`.
  - [153] linear / bounded cold mass; [146] theta < 1/78; [160] first test (tau < 1/4); [53] entropy cap; [50] remainder entropy: `netDeficiencyCap`.

<a id="residual-153"></a>

### Node [153] (lem:cold-corridor-first-failure (ii), tex 7265-7270)

- **Configuration at G.** G's first equal-state pair on a retained cold corridor, with its separating path context and profile separation; at G's canonical witness `coldRepeatWitness? = some ⟨occurrence, ε, left, right⟩` (`ColdRepeatedStateSpecAt`): the retained corridor `C_ε` of G in its outside component of `G − X_cold`; `left < right` with equal pinned states and no two equal states before `right` (the first equal-state pair); no (F1)--(F5) event before `right` and the (F2) clause at `right`; the separating path context `ColdEqualStates.prefixContext right` (accepted cycle through `piece J_right`, none through `retainedPiece J_right J_left`); the boundary-degree profiles of the two pieces differ; the glue vertices `head left`, `head right` have equal boundary-degree entries.
- **Lean.** `Node153ResidualOutcome` (`Assembly/Residuals.lean`); return theorem `node153Return`; reached by 23 paths (distinct ledger histories from the root).
- **Facts carried (42).**
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
- **On some paths only, not carried (25).** Gated by an arm of:
  - [153] linear / bounded cold mass: `coldMassBounded`, `coldMassLinear`, `densityCap`.
  - [50] low arm, local-type coordinate (lem:dominant-type): `dominantRootedType`, `localTypeCoordinateNonrepetitive`, `localTypeCoordinateRepetitive`.
  - [50] remainder entropy: `entropyPackageDemand`, `remainderEntropyHigh`, `remainderEntropyLow`.
  - [57]/[173] exact collision: `absorbedConfigurationResidual`, `exactCollisionFails`.
  - [146] theta < 1/78: `coldRoute8AtOrAbove`, `coldRoute8Below`.
  - [160] first test (tau < 1/4): `denseDeficiencyAtOrAbove`, `denseDeficiencyBelow`.
  - [50] low arm, root-wedge split (lem:dominant-type): `dominantRootedTypeWedgeFree`, `dominantRootedWedgeType`.
  - [160] second test / route-8 entry rate: `route8Rate`, `route8RateFails`.
  - [158] window package realized: `windowPackageRealized`, `windowPackageUnrealized`.
  - [53] entropy cap: `entropyCapBound`.
  - [50] low arm, root-wedge split (lem:dominant-type); [50] low arm, local-type coordinate (lem:dominant-type): `independentObstructionTranslates`.
  - [53] entropy cap; [50] remainder entropy: `largeBudgetResidual`.
  - [153] linear / bounded cold mass; [146] theta < 1/78; [160] first test (tau < 1/4); [53] entropy cap; [50] remainder entropy: `netDeficiencyCap`.

<a id="residual-162"></a>

### Node [162] (lem:dense-cold-pass, tex 7692-7694)

- **Configuration at G.** A retained cold corridor of G whose first failure is a heavy centre strictly before its terminal segment and which reads more than Q_cold states; at G's canonical witness `coldHeavyEntryWitness? = some ⟨occurrence, ε, first, centre⟩` (`ColdDenseHeavyEntrySpecAt`): `head first = centre` with `δ < d_G(centre)`; `first` is an (F4) first failure with no earlier event; the pinned states up to `first` are pairwise distinct, so `first < Q_cold`; `first < |C_ε|`; `Q_cold ≤ |C_ε|` and `C_ε` is not terminal.
- **Lean.** `Node162ResidualOutcome` (`Assembly/Residuals.lean`); return theorem `node162Return`; reached by 2 paths (distinct ledger histories from the root).
- **Facts carried (46).**
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
- **On some paths only, not carried (3).** Gated by an arm of:
  - [160] first test (tau < 1/4): `denseDeficiencyAtOrAbove`, `denseDeficiencyBelow`.
  - [160] second test / route-8 entry rate: `route8RateFails`.

<a id="residual-54"></a>

### Node [54] (prop:entropy-high-theta, tex 9921)

- **Configuration at G.** The configuration at G where the joint realization inequality RS(R0)*2^(rate*s*p13)*2^F <= B fails; at G's `P₀ = canonicalWindowPacking` and `R₀ = R(P₀)` (`AllColdEntropyResidualStatement`): `¬ WindowFamilyRealized P₀`; the remainder glue `RS(R₀)·room ≤ B` with `room = C(C(n,2) − C(|R₀|,2), m − e(G[R₀]))`; `F ≤ c_Ω·r_Ω(R₀)`; `room < 2^{rate·s·p₁₃}·2^F`; `[53]` active, `B < 2^{rate·s·p₁₃}·RS(R₀)·2^F`; and `¬ RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`.
- **Lean.** `Node54ResidualOutcome` (`Assembly/Residuals.lean`); return theorem `node54Return`; reached by 6 paths (distinct ledger histories from the root).
- **Facts carried (40).**
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
- **On some paths only, not carried (10).** Gated by an arm of:
  - [153] linear / bounded cold mass: `coldMassBounded`, `densityCap`.
  - [146] theta < 1/78: `coldRoute8AtOrAbove`, `coldRoute8Below`.
  - [160] first test (tau < 1/4): `denseDeficiencyAtOrAbove`, `denseDeficiencyBelow`.
  - [160] second test / route-8 entry rate: `route8Rate`, `route8RateFails`.
  - [158] window package realized: `windowPackageRealized`, `windowPackageUnrealized`.

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
