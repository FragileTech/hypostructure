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
  publishes.  `[54]` (`entropyCapBoundRow.runAndCloseIncompatible`) reads
  `[21]`, `[48]`, `[51]`, `[52]`; on the arm where the window package of `P₀` is
  not retained its bound is the `OPEN-CONSTRUCTION [54] tex:9921` hook (see Paper
  errors).
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
  `¬ WindowFamilyRealized P₀` holds and the hook arm is the only one reached.
- **Note on the `[158]`-no arms.**  There `B < 2^{b_P}`; with `bits ≤
  (rate+1)·L − 1`, the high arm's `RS ≥ n^p` (`n ≥ 23p`, from `[161]` or
  `coldRoute8Below`) gives `B < 2^{rate·L·p}·RS ≤ demand·2^F`: `[53]` is
  always active there, and `[54]` asserts that a superset of the package the
  paper found unrealized at `[159]` is realized.  This is the terminal's own
  contradiction at a nonexistent G (every terminal hook contradicts its branch's
  ledger); it is not a refutation from the hook's hypotheses, but it shows that
  on those arms the paper's `[54]` step is circular.
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
  valuation.  Both were generically true: the round-2 audit
  (`audit2-F4/ProfileDReduces.lean`) manufactured the free determination for
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
present: every entry formerly filed here was re-checked at G (round 2, fix2)
and is now under "Paper findings (no sorry)", "Open constructions", or closed
by a user-approved repair, or returned as an explicitly constructed residual
(fix3).  The anchor `#paper-errors` is kept for the Lean
references written before the split.

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
- **User-approved construction attempt (fix2-TR steps 2 and 2b).**  Evidence:
  `audits/erdos-64-red-team/fix2-TR/Step2Evidence348.lean` (compiles; axioms
  propext, Classical.choice, Quot.sound).  At an entry `ξ = (X, w, u, B_u)` of
  G's unified set with (b), with `S := B_u`, `Y_G :=` the outside of `B_u` in G,
  and the explicit smaller representative `R :=` the interior fold
  `identifyInternal keep remove` of `B_u` (a realization of the quotient, fold
  map as label-fixing placement, when no kept declared support contains
  `keep`/`remove`):
  - Clauses of `CompressibleSupport G S` (`InterfaceReplacement.lean:415`):
    connected, proper, boundary degree profile, baseline `δ(R ⊕ Y) ≥ 3`,
    strictly smaller all hold (`fold_clauses`,
    `foldRealization_baseline_and_smaller`).  The response clause is the only
    open one, and at `Y_G` it is equivalent to `¬ Target(R ⊕ Y_G)`, i.e. to
    the closure itself (minimality forces `Target(R ⊕ Y_G)`,
    `response_clause_fails_at_G_context`).  So the question is whether G's
    facts force `R` to respond like `B_u` at `Y_G`.
  - What (b) gives at `Y_G`: `Y_G` is profile-compatible
    (`profileCompatible_G_context`), so (b) yields
    `¬ declaredAlgebra R Y_G` (`b_at_G_context`).
  - **Conditional closure** (`closes_of_visibility`): (b) + a fold pair off
    the kept declared supports with no common neighbour + `Visibility` ⇒ `False`
    against G's minimality.  **Missing implication, as a formula about G**:
    `Visibility(R) := Target(R ⊕ Y_G) → declaredAlgebra R Y_G` -- every
    accepted cycle of `R ⊕ Y_G` passes through a label of `∂B_u` lying on the
    event walk of a core-retained crossing declared coordinate of `ξ` -- plus
    the existence of the fold pair.
  - **Inventory (completeness check)** of what the paper constructs on G on the
    path to tex 15362 that could turn declared-algebra equivalence into
    response equality at `Y_G`:

    | paper object / fact | tex | Lean key / object | at `[348]` | gives `Visibility`? |
    |---|---|---|---|---|
    | `lem:degree-profile-fibres` [11] | 6088 | `K .degreeProfileFibres` (2300), `Statements/Spine.lean:2606` | on ledger (entry prefix) | no: separates fibres only; the fold with no common label stays in `B_u`'s fibre |
    | `lem:context-universality` [12] | 6106 | `K .targetCompleteContextUniversality` (2301), `Statements/Spine.lean:2635` | on ledger | no: part 1 needs a full-target, all-context identification of an admissible rank quotient (not supplied by (b)); "consequently" concludes target-DEFECT from a separating context, never equality at `Y_G` |
    | `def:admissible-rank-quotient` | 6026-6035 | `Graph.CurvatureQuotient` | definitional | no: requires target-completeness against all `T`-contexts; tex 6031-6035: a correlation with no smaller representative "is not an admissible rank reduction" |
    | `lem:replacement`, `cor:uncompressible` [13]/[14] | 6116, 6142 | `K .replacementExclusion` (223), `K .uncompressible` (5) | on ledger | no: refute a representative that is already full-target complete |
    | declared family `R_u(B_u)`, declared algebra | 10733-10743 | `traceCoordinates`, `declaredAlgebra` (`Route8Residual.lean`) | definitional | no: completeness is stated for declared `u`-supported events only |
    | (b) response quotient, realization, compatible context | 10744-10775 | `ResponseQuotient`, `QuotientRealization`, `ProfileCompatible`, `TraceResponseQuotient` | tested at `[347]`/`[348]` | gives `¬ declaredAlgebra R Y_G` only |
    | trace-completeness / basin selection | 10718-10731 | `TraceComplete`, `select?` | definitional | no (about the trace path) |
    | target-complete-minimality of route-8 basins | 10760-10790 | `TargetCompleteMinimal`, census `K .route8UnifiedEntryCensus` (340) | after `[348]` (free arm only) | no: its (b)-clause is the negation of what is tested |
    | exit (5) smaller representative | 10773-10775, 10824-10826, 11677-11682 | `TraceTargetCompleteCompression` | never constructed by the paper (always "when realized by a smaller ... piece") | -- |
    | `\tilde{\mathcal X}`, `\tilde\Xi`, deficit | 15236, 15301, 15260 | `K .route8UnifiedNegative` (336), `route8UnifiedEntries`, `K .route8UnifiedDeficit` (339) | on ledger | no (counting facts) |
    | Type A exclusion | 11890-11919 | `K .typeAExclusion` (343) | on ledger | no: keeps (b) as an open alternative |
    | selection, minimality, baseline | [4] | `K .selection` (0), `K .cubicBaseline` | on ledger | used: gives `Target(R ⊕ Y_G)` |

    Nothing the paper constructs is missing from G's ledger at `[348]`; the
    paper never supplies `Visibility` nor the fold pair.  So the Step-1 routing
    is kept: `[348]` is a returned outcome at `[187]`.
- **Scope of `[347]`.**  The former second conjunct of
  `Route8QuotientFreeStatement` (every negative no-handoff core of a deleted
  region, any `σ`, every receiver, `excessBasinReduced` loads) went beyond
  tex 15360-15364 and had no reader; it is removed.  The extracted cores carry
  their own quotient-free clause in `route8ExtractedCores`.
- **Realization class (fix2-TR).**  A response quotient keeps, identifies or
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

## Returned residuals (explicitly constructed)

User ruling (2026-09-27): a paper step that is not established at G is not a
`sorry`.  The node is an exact decision at G's pinned objects; the arm where
the paper's claim holds continues with its proof, and the complementary arm
publishes the explicitly constructed configuration at G as a ledger fact, which
is returned as a top-level outcome of `SelectedLedgerBoundaryResult`
(`Assembly/Final.lean`), as `[144a]` and `[348]` already do.  Each returned
outcome carries the residual's own fact and `K .surplusAtOrBelow`, read from
G's one ExactLedger at the return point.  New keys: idx 3200-3205.
Each residual key has a Core `Incompatible` instance against its decision's
other arm, so a later row that proves the paper's claim on the residual arm
closes it with `closeIncompatible` without restating anything.  The live
library is `Graph/ColdEqualStates.lean` (vocabulary-free, rebuilt from the
quarantined `ColdF2Refutation` Part 4, not imported) and
`Graph/Statements/ColdResiduals.lean`.

### [153] `lem:cold-corridor-first-failure` (ii) (tex 7265-7270): G's first equal-state pair

- **Paper step replaced** (tex 7264-7270): "If it is (F2), the actual quotient
  is valid only for the current outside context and fails for another
  compatible context.  By `lem:context-universality`, this is not
  target-complete, so it is a target-defective quotient.  In the global branch
  ledger such defects are exactly the sparse exits; in the Type A location they
  are the exit-(4) peels, and both are excluded in `def:surviving-cold-branch`."
- **Decision** (`coldCutStatesDichotomy`, reads `K .coldFirstFailureOccurrence`):
  (★) `ColdCutStatesDistinctStatement` -- along G's retained corridor of every
  eligible `ε`, the pinned cut states (`coldCutStatePresentation`, identity
  index) of the segments up to the first failure are pairwise distinct.  At G
  this is equivalent to the paper's exclusion
  (`Contracts.Spine.coldFirstFailureDefectAt_iff`: (F2) at a segment iff an
  earlier segment has the same state, through the path context below).
- **(★) arm** (`K .coldCutStatesDistinct`): (F2) is excluded
  (`coldFailureDefect_excluded`, `coldFailureDefectRoutes_of_distinct`) and the
  routing `[68]` continues unchanged.
- **Returned residual** (`K .coldRepeatedStateResidual`, 3201,
  `ColdRepeatedStateResidualStatement`), at G's canonical witness
  `coldRepeatWitness? = some ⟨occurrence, ε, left, right⟩`
  (`ColdRepeatedStateSpecAt`):
  - `C_ε = coldOccurrenceCorridorAt …`, in its outside component of
    `G − X_cold` (`IsOutsideComponent`);
  - `left < right`, `state(left) = state(right)`, and no two equal states
    before `right`: the FIRST equal-state pair;
  - no (F1)--(F5) event at any segment before `right` (in particular no
    terminal and no (F4) event), and the (F2) clause holds at `right`: `right`
    is `ε`'s first failure;
  - the separating context `ColdEqualStates.prefixContext right`: a path of
    `2^(right+2) − right` edges with fresh interior glued at `head right` and
    the entry foot; `glue(piece J_right, P)` has an accepted cycle (length
    `2^(right+2)`), `glue(retainedPiece J_right J_left, P)` has none (in that
    reading `head right` is isolated, and G has no accepted cycle);
  - `d_∂(retainedPiece J_right J_left) ≠ d_∂(piece J_right)`
    (`ColdEqualStates.prefix_profile_ne`);
  - the excision data of the pair: glue vertices `head left`, `head right`
    with equal boundary-degree entries, i.e.
    `min(d_G(head left), D) = min(d_G(head right), D)` (through the `[30]` pin,
    `pinned_headBoundaryDegree`).
- **Returned at**: the dense pass (`nearCubicDenseLinear`), the realized arm of
  `[158]`, and the absorbed lane (`selectedAbsorbedGermPrerequisites` →
  `selectedNetChargeContinuation`); root outcome `Node153ResidualOutcome`.

#### Analysis before fix3 (formerly under "Open constructions": [153] (F2) exclusion, `lem:cold-corridor-first-failure` (ii) (tex 7265-7270))

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
- **Tag.** `sorry`, `OPEN-CONSTRUCTION [153] tex:7268`, in
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
- **Addendum (2026-09-27, fix2-SC): the corrected cut state, and the hook's
  exact content at G.**  `coldCutStatePresentation` is now the paper's
  `ρ^ex_{T(J)}(J)` retention (see "the cold chain at G's objects"): `T(J)` is
  the entry interface and the head interface (the successor window only once
  `J` reaches it), the head half-edge and the head-side offset move along the
  corridor, and each declared coordinate is read through its clause.  The hook
  is stated at this presentation (the `Sigma` pin is unchanged).
  - **Equivalence at G.**  Since G has no target cycle, the Lean (F2) holds at
    every pair `left < right` of G's corridor with equal states: a fresh path
    context of length `2^k − right` from the entry foot to `head right` closes a
    target cycle with `piece(J_right)`, and is pendant in
    `retainedPiece(J_right, J_left)` (whose head has no retained edge), where
    the only cycles are G's.  With (F1)/(F3) excluded by `[64]`/`[66]`, the hook
    at G is therefore equivalent to: **every retained corridor of G is terminal
    (reaches its successor stub within `Q_cold` states) or reaches a heavy
    centre ((F4), `ColdDeclaredHandoffSupport`) strictly before its first state
    repeat.**  The (F5) repeat subcase can never be a first failure.
  - **Completeness check** (the whole path to `[153]`'s (F2) routing, tex
    2754-2772, 4629-4652, 4783-4798, 5858-5950, 6106-6140, 6982-6997,
    7164-7275, 12095-12127): every object the paper constructs is on the ledger
    -- the sparse family and survivor `[125]` (`sparseDeclaredFamily`,
    `DeclaredSparseSurvivor`, `CanonicalSurplus.lean:174,232`), clause (b)
    `ResidualTargetDefect` (`NamedSurplusExits.lean:111`), the pair coordinates
    `r_π` and spine family, context universality `[12]`, the exit-(4) family
    `Q₄(w)` (`ExitFourFamily.lean`, closed list Q1-Q5), the corridor, cut state
    and first failures (`[30]`, `[404]`, `[422]`).  What is missing is exactly
    the paper's sentence "in the global branch ledger such defects are exactly
    the sparse exits; in the Type A location they are the exit-(4) peels"
    (tex 7268-7270): a map from an (F2) pair -- two prefixes of one corridor --
    to two coordinates of G's sparse family (tex 2769-2772 names only surplus
    demands, pairs and spine coordinates) or to a member of the closed list
    `Q₄(w)` (tex 12126-12127, "exit (4) occurs precisely when one of these
    listed canonical quotients is target-defective").  The paper constructs
    neither; the same unproved sentence recurs at G2 (tex 7391-7395) and at the
    table's distinguishing row (tex 7446-7450), where the Lean keeps the
    outcome instead of excluding it.  So the missing fact about G is the one
    displayed above (no state repeat before a terminal or heavy event), which no
    construction of the paper supplies.
  - **Not refutable.**  Refuting it needs a retained corridor of G whose first
    state repeat precedes every heavy centre; nothing on the ledger places G's
    heavy vertices or bounds corridor lengths from below.
  - **The pumping construction, carried out at G (user's construction,
    2026-09-27).**  Suppose G's states repeat at segments `i < j` before any
    terminal or heavy event.  Excise the corridor stretch strictly between
    `J_i` and `J_j` and glue `head i` to the continuation after `head j`: the
    replacement piece of `supp = J_j` is `retainedPiece(J_j, J_i)` (the corridor
    prefix `J_i` with the head moved), a proper boundaried piece of G.  Clause
    by clause against `CompressibleSupport` (`K .uncompressible`): it is
    strictly smaller (`j − i` fewer internal vertices), connected, on G's own
    support; but
    - **the boundary profile clause fails**: on `∂J_j` the entry foot keeps
      its corridor edge in `piece(J_j)` and has it only through `head i` in the
      replacement; at `i = 0` the foot loses it
      (`Quarantine/PaperRepairs/ColdF2Refutation.lean`,
      `prefix_zero_profile_ne`);
    - **the response clause fails, at G, always**: the context of a fresh path
      of length `2^k − j` from the foot to `head j` closes a target cycle with
      `piece(J_j)` and none with the replacement, whose cycles through the
      glued vertex are `j − i` shorter; G has no target cycle, so this context
      is compatible and separates the two pieces.  The retained cut state is a
      finite projection of `ρ^ex_{T(J)}(J)` (tex 7187-7197: "It is not the full
      labelled prefix"), so equal states do not give equal responses -- the
      paper itself records exactly this discrepancy as (F2) (tex 7192-7195).
    So the excision is not a compression and yields no contradiction with
    `[14]` or `[4]`; the concrete obstruction at G is the separating context
    above, at any equal-state pair.  The step stays open.
  - **Where the separating context attaches, and why equal states do not
    exclude it.**  The context is a path `P` of length `L = 2^k − j` (fresh
    internal vertices) glued at the entry foot `x = head 0` and at `head j`,
    i.e. at the two vertices of `T(J_j) ∩ ∂J_j` -- it attaches *through* the
    interface.  `CompressibleSupport`'s response clause ranges over every
    `OutsideContext` of the support's boundary `∂J_j` (`∀ outside, Target (glue
    E outside) ↔ Target (glue Q outside)`), so `P` is one of its contexts.
    With `Q = piece(J_j)`, `glue Q P` has the cycle `P + (x … head j)` of length
    `L + j = 2^k`; with the excised `E`, the foot-to-head path has length `j −
    (j−i) = i`, so the cycle has length `2^k − (j − i)`, not a power of two for
    `k` large, and `E` adds no other cycle through `P`.  Equal states do not
    exclude this because the paper's cut state is a *finite* projection of
    `ρ^ex_{T(J)}(J)` (tex 7187-7197): it keeps the boundary-degree profile,
    the two half-edges, the two offsets, and the declared coordinates whose
    support lies inside `T(J)`.  The foot-to-head distance is carried only by
    coordinates supported on the connector itself (D2 "connector lengths",
    "edge-rooted return data"), whose support is the prefix, not contained in
    `T(J)`, so it is not retained -- and it cannot be: the distances `0, …, Q`
    along one corridor are pairwise distinct, so a state that kept them could
    never repeat and `Q_cold` would not be a constant of the signature.  The
    paper says as much: the state "is not the full labelled prefix", and a
    same-state pair that differs in response "is recorded as (F2)"
    (tex 7192-7195).  Enriching the state to the full exterior response would
    change the paper's definition and remove the finiteness `[153]`/`[162]`
    rest on; and for a power-of-two target any excision that shortens the
    foot-to-head distance changes the response against such a path context, so
    no excision is ever response-preserving.  Route 3 therefore fails at every
    equal-state pair; routes 1 and 2 give nothing (no arm or bound is
    contradicted by a state repeat).
  - **Route 1 through the survivor: the cold prefixes as declared coordinates
    (2026-09-27).**  The survival clause of `def:named-surplus-exits`
    (tex 2769-2772) quantifies (b) over "any selected surplus demand, any
    selected pair of surplus demands, or any baseline spine coordinate used in
    the entropy sandwich of `def:baseline-spine-demand`"; `I_spine`
    (tex 4783-4798) is "the independent target coordinates already forced by
    the near-cubic spine before sparse surplus-pair coordinates are added" --
    window, remainder, obstruction and local-residual demands.  No clause
    declares cold corridor prefixes, and `sparseDeclaredFamily`
    (`Statements/CanonicalSurplus.lean`) follows it.  Adding them would not
    help: clause (b) (`ResidualTargetDefect`) reads the two coordinates on G's
    piece at `Z = select?(J_i ∪ J_j) = J_j` and needs equal boundary-degree
    profiles of `retainedPiece(J_j, J_i)` and `piece(J_j)`.  They differ: on
    `∂J_j` the head `head j` keeps its corridor edge in `piece(J_j)` and has
    none in the `J_i` reading (checked in Lean for `i = 0`:
    `Quarantine/PaperRepairs/ColdF2Refutation.lean`,
    `prefix_zero_profile_ne`, `not_residualTargetDefect_prefixPair_zero`).
    The cut state's "same boundary-degree profile" is G's degree at the foot
    and at the head, not the `d_∂` of the two readings, so an (F2) pair lands
    in blocker (d) (`ResidualProfileSeparation`), not in exit (b).  Reading (b)
    over all of G's boundaried pieces instead would fire on every corridor of
    length `≥ 2` (`edge_twoPath_sameFibre_targetDefect`) and empty the
    surviving branch.  So route 1 fails as well; the hook stays open, and so
    does `[162]`, whose length bound needs (F2) excluded.
- **Addendum (2026-09-27, fix2-F2): the hook at G, Lean-checked, and the
  remaining routes.**  `Quarantine/PaperRepairs/ColdF2Refutation.lean`, Part 4
  (standard axioms):
  - **The equivalence, proved.**  `EqualStates.coldFirstFailureDefectAt_iff`:
    on an object with no accepted cycle (G, `.targetAvoidance`) and a target
    accepting every `2^k`, `k ≥ 2` (`lengthOK_iff_powerOfTwo`), for every
    corridor, presentation and index, the Lean (F2) at `right` holds iff some
    `left < right` has the same state.  The separating context is the path of
    length `2^(right+2) − right` from `head right` to the foot.  In
    `retainedPiece J_right J_left`, `head right` is isolated, so every cycle of
    that gluing lifts to G.  `EqualStates.first_lt_stateBound`: pairwise
    distinct states up to `first` force `first < Q_cold`.  So the hook at G is
    exactly **(★) G's pinned cut states along each retained corridor are
    pairwise distinct up to its first failure** (a terminal or (F4) event).
    The (F5) repeat subcase is never a first failure.  The paper's existence
    proof ("two states are equal ... gives the repeat subcase of (F5)",
    tex 7259-7262) produces exactly the configuration its (ii) must exclude.
  - **The paper's map, read exactly.**  Tex 7265-7270 maps an (F2) pair to the
    identification `q_J(J_l) = q_J(J_r)` made by the cut-state map
    `q_J : ρ^ex_{T(J)}(J) → CutState`.  That identification is target-defective
    (`not_targetComplete_of_firstFailureDefect`, the only object the sentence
    constructs), and the sentence asserts that it is a sparse exit or an
    exit-(4) peel.  That assertion is type-incorrect at every pair:
    `EqualStates.prefix_profile_ne` / `not_residualTargetDefect_prefixPair`
    (all `left < right`, generalizing the `left = 0` case) show that the two
    readings are always a `d_∂` separation, while clause (b) and `Q₄(w)` are
    same-fibre defects of declared coordinates (no declared sparse or exit-(4)
    coordinate is supported on a corridor prefix).  So the missing object is
    not an unimplemented construction.  The closing object would be ¬(★)
    itself, and the paper maps that to nothing.
  - **Route 1 through profile structure** (explicit witness: G's retained
    corridor, `l < r ≤ first` with equal pinned states, the path context
    above).  `[11]` (`degreeProfileFibres`, 2300) and `[12]` constrain
    identifications made by a `CurvatureQuotient` (field `fibrewise`); the
    fix2-SP closure of blocker (d) (key 2902, `SparseEntropySandwich.lean`
    665-809) relies on the determination quotient carrying G's exact response
    (`SparsePairExactValuation`).  `q_J` is neither.  By tex 7192 it is a
    finite projection, and giving it an exact valuation makes `CutState`
    infinite, so `Q_cold` is no longer a signature constant.
    `def:admissible-rank-quotient` and rem. 6084 allow such non-admissible
    identifications to exist ("does not reduce `r_Ω`").  `[12]`'s second
    conjunct produces the defect and forbids nothing.  G1/G2 and
    `[604]`/`[605]` are downstream of the routing that consumes this hook
    (circular).  The (F4) registry is never met before the repeat under ¬(★).
    No contradiction.
  - **Route 2 (overload).**  `coldMassBounded`/`coldMassLinear` count windows;
    `corridorLoss ≤ (δ+1)·B_cold·σ(G)` and `#(F4) ≤ corridorLoss` are
    downstream of the routing and count (F4) and loss stubs, not repeats;
    `Q_cold` bounds distinct states per corridor, and one repeat per corridor
    overloads nothing; `[174]`/`[22]` and `|𝒫_hot| ≤ θ_win n` count windows,
    and a hot window can be crossed by every corridor of its component; the
    maximality of `P₀` forces window visits (the corridor is shortest in `K`,
    hence induced), not distinct states.  No contradiction.
  - **Verdict.**  Still an OPEN CONSTRUCTION, with the missing fact about G
    Lean-equivalent to the hook: (★).  It is not refutable (that needs a
    G-corridor with a repeat, which the ledger does not place) and not shown
    false.  Analysis: `f2-analysis.md` (group F2 scratchpad).

### [162] `lem:dense-cold-pass` (tex 7692-7694): a first failure at a heavy centre before the terminal segment

- **Paper step replaced** (tex 7692-7694): "Since the boundaried pieces of `R`
  are induced-`P₁₃`-free and subcubic, they have bounded diameter, so every
  return corridor is terminal in the sense of the (F5) terminal subcase".
- **Order.**  In the dense pass the first failures and `[153]`'s decision now
  run before `[162]` (`[162]` is consumed only at `[163]`).
- **Decision on the (★) arm** (`coldHeavyEntryDichotomy`, reads
  `K .coldCutStatesDistinct`): `ColdHeavyEntryTerminalStatement` -- every
  retained corridor of G whose first failure is an (F4) heavy centre strictly
  before its terminal segment is terminal.
- **Test arm** (`K .coldHeavyEntryTerminal`): `[162]` is proved
  (`denseColdCorridorsTerminal_of_distinct`): (F1) by target avoidance, (F3)
  by uncompressibility, (F2) and the repeat subcase of (F5) by (★), the
  terminal subcase of (F5) directly, an (F4) event at the terminal segment by
  `ColdEqualStates.first_lt_stateBound` (distinct states put it below
  `Q_cold`), and an (F4) event before the terminal segment by the test.  The
  paper's diameter premise is not used.
- **Returned residual** (`K .coldDenseHeavyEntryResidual`, 3203,
  `ColdDenseHeavyEntryResidualStatement`), at G's canonical witness
  `coldHeavyEntryWitness? = some ⟨occurrence, ε, first, centre⟩`
  (`ColdDenseHeavyEntrySpecAt`): `head first = centre`, `δ < d_G(centre)`;
  `first` is an (F4) first failure with no earlier event; the pinned states up
  to `first` are pairwise distinct, so `first < Q_cold`; `first < |C_ε|`;
  `Q_cold ≤ |C_ε|` and `C_ε` is not terminal.  Root outcome
  `Node162ResidualOutcome`.
- The former hook `denseColdCorridorsTerminal_of_state` is deleted.

#### Analysis before fix3 (formerly under "Open constructions": [162] terminality of the cold return corridors, `lem:dense-cold-pass` (tex 7692-7694))

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
- **Pumping (2026-09-27).**  A corridor longer than `Q_cold` must repeat a
  state (route 2 gives the repeat), but the excision at the repeat is not a
  compression at G: the path context glued at the foot and at the later head
  -- through `T(J)` -- separates the pieces, and the finite state forgets the
  foot-to-head distance (see `[153]`'s pumping entry).  So route 3 does not
  bound the length either.  The obstruction at G is a retained corridor that crosses
  hot or non-ambient-cubic cold windows for more than `Q_cold` segments; the
  ledger neither produces nor excludes one.
- **The exact gap (fix2-SC, 2026-09-27).**  The missing fact is "the corridor
  path of every eligible `ε` lies in `R(P₀)`", and it is exactly sufficient: the
  Lean inside path is shortest in `G[K]` (`inside_length_le`), hence shortest in
  `G[S]` for its own vertex set `S`; if `S ⊆ R`, `[27]` makes `G[S]` induced-`P₁₃`
  free, so `shortestPath_length_le_order_sub_two` bounds its length by `11` and
  `statesRead ≤ 12 < 13 ≤ Q_cold` (`windowOrder_le_stateBound`): terminal.  The
  paper's second premise, subcubicity of the pieces, is unsupported (R may
  contain degree-`≥ 4` vertices, which `lem:absorbed-germ-fan-data` (ii) itself
  uses) and unnecessary.
- **Completeness check** (tex 6862-6865, 6937-6997, 7046-7114, 7164-7298,
  7619-7698, 8636-8674, 10063-10090, 10374-10381): every object the paper
  builds on the path is on the ledger before `[162]` -- `P₀` and `R` (`[19]`,
  `.maximalPacking`), `[27]` `.remainderNormalized`, the hot/cold split `[22]`,
  `.surplusAtOrBelow`, `.coldAmbientCubic`, the selected half-edges and stub
  excess `[150]`--`[152]`, `lem:bridgeless`, the corridors and states `[30]`,
  the dense-residual tests `[158]`/`[160]`.  None of them places a corridor in
  `R`: `X_cold` keeps the hot and non-ambient-cubic cold windows in the outside
  graph, a selected stub's foot may lie in a hot window, and the paper only
  counts the non-ambient-cubic windows (`≤ σ(G)`).  The only diameter argument
  in the paper (tex 10374, `diam(X) ≤ 11`) is about Type A pieces `X ⊆ R`;
  tex 7692-7694 transfers it to corridors of `G − X_cold` without the
  containment.  Maximality of `P₀` only gives that every 13 consecutive corridor
  vertices meet a window of `P₀`.
- **Tag.** `sorry`, `OPEN-CONSTRUCTION [162] tex:7694`, in
  `Graph/Contracts/Spine/ColdMass.lean`.  Node `[162]` is no longer consumed on
  the absorbed branch (see "the cold chain at G's objects").
- **Relation to `[153]` (2026-09-27, fix2-F2).**  The `[153]` hook at G is
  (★) "pinned cut states pairwise distinct up to the first failure"
  (`ColdF2Refutation.EqualStates.coldFirstFailureDefectAt_iff`).  By
  `EqualStates.first_lt_stateBound`, (★) puts the first failure within
  `Q_cold` states.  So `[153]` together with "no (F4) event before the
  terminal segment" gives `[162]`'s conclusion.  Both hooks rest on one
  missing fact about G: its cold corridors are short.  Profile structure
  (`[11]`/`[12]`, key 2902) and overload (cold mass, corridor loss, hot/cold
  caps, maximality of `P₀`) give nothing for `[162]` either.  The gap stays
  "the corridor path of every eligible `ε` lies in `R(P₀)`".

### [54] `prop:entropy-high-theta` (tex 9929): the joint realization inequality fails

- **Paper step replaced** (tex 9929): "Then the window package of
  `lem:p13-window-package`, the remainder bits, and the forced-obstruction bits
  together strictly exceed the near-cubic skeleton budget.  These bits form one
  independently target-testable coordinate family, so the number of realized
  target-complete states would exceed the number of labelled skeletons,
  contradicting `lem:independent-target-entropy`, `lem:skeleton-dominates`."
- **Decision** (`entropyJointRealizationDichotomy`, on `[53]`'s active arm,
  reads `K .entropyCapActive`): `EntropyJointRealizationStatement` --
  `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` at G.
- **Joint arm** (`K .entropyJointRealization`): `entropyCapBoundRow` publishes
  `K .entropyCapBound` (`entropyCapBound_of_jointRealization`, through
  `jointRealization_iff_entropyCapBound`) and Core closes it against
  `K .entropyCapActive`.
- **Returned residual** (`K .allColdEntropyResidual`, 3205,
  `AllColdEntropyResidualStatement`), at G's `P₀ = canonicalWindowPacking` and
  `R₀ = R(P₀)`: `¬ WindowFamilyRealized P₀` (a retained package proves the
  inequality, `entropyCapBound_of_retained`); the remainder glue
  `RS(R₀)·room ≤ B`; `room = C(C(n,2) − C(|R₀|,2), m − e(G[R₀]))`
  (`remainderOuterRoom`, moved to the statements module); `F ≤ c_Ω·r_Ω(R₀)`;
  `room < 2^{rate·s·p₁₃}·2^F` (a fit proves the inequality,
  `entropyCapBound_of_outerRoom`); `[53]` active,
  `B < 2^{rate·s·p₁₃}·RS(R₀)·2^F`; and `¬ RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`.
  Returned at the four `[53]`-active sites of `NearCubic/Spine.lean`; root
  outcome `Node54ResidualOutcome`.  The former hook
  `entropyCapBound_unretained` is deleted.

#### Analysis before fix3 (formerly under "Open constructions": [54] on the all-cold arm of [22], `prop:entropy-high-theta` (tex 9919-9921))

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
- **Faithful Lean statement (until 2026-09-27; now `entropyCapBound_unretained`, see the addendum).** `Contracts.Spine.entropyCapBound_allCold`: at the
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
- **Tag.** `sorry`, `OPEN-CONSTRUCTION [54] tex:9921`, in
  `Graph/Contracts/Spine/RemainderEntropy.lean`.
- **Addendum (2026-09-27, fix2-SC): completeness check and the glue relation.**
  - The paper builds exactly one realization map on this path:
    `lem:remainder-glue-injection` (tex 7816-7850, `RemainderGlue.glue_injective`,
    `remainderStateCount_le_skeletonBudget`: `RS ≤ B` with G's outer edges
    fixed).  Varying the outer edge set gives the true (unpublished) relation
    `B ≥ RS·C(C(n,2) − C(|R₀|,2), m − e(R₀))`.  It proves the hook whenever
    `2^F ≤ C(C(n,2) − C(|R₀|,2), m − e(R₀))`; on the only arm where the hook is
    consumed (`[53]` active, `B < RS·2^F`) the same relation forces
    `C(…) < 2^F`, so at every use the hook sits where the glue argument cannot
    reach.  No lemma of the paper (and none in Lean: the `SeparatedFamily`
    realizations top out at `2^{13p}`) realizes the window package; the paper
    itself makes that realization the branch test `[158]` and states the joint
    comparison of `prop:p13-density` only as a hypothesis (tex 8490).
  - The other objects on the path (`[21]`, `[22]`, `[48]`, `[51]`, `[52]`,
    `lem:skeleton-dominates`, `lem:near-cubic-budget`, `lem:full-rank`) are on
    the ledger at `[54]`; none realizes the product family.  The missing fact
    about G is the premise of `lem:independent-target-entropy` for the family
    (remainder states of `R₀`) × (forced obstruction bits): a canonical state map
    on G's labelled skeleton class with `RS·2^F` states.
  - **Three routes on `¬X`** (X = the joint realization of the all-window
    package, the remainder states and the forced bits by one labelled class):
    (1) incompatible structure -- `¬X` is the `[53]`-active inequality itself
    and contradicts no earlier arm; (2) overload -- the only proved bounds are
    `RS ≤ B` (glue) and `F ≤ c_Ω r_Ω`, and on this arm `B < RS·2^F·2^{rate·L·p}`,
    so no count exceeds a proved bound; (3) compressibility -- the forced bits
    are rank coordinates of `R₀` (`lem:full-rank`), and an unrealized product
    family gives no smaller representative of any support.  All three fail; the
    concrete configuration at G is the arm's own inequality `B < demand·2^F`
    with `¬ WindowFamilyRealized P₀`.
  - The hook is `entropyCapBound_unretained` (renamed from
    `entropyCapBound_allCold`: the arm is now `¬ WindowFamilyRealized P₀`).
  - The numeric model above is supporting evidence only; the primary
    justification is the named failing step (2).

- **Addendum (2026-09-27, fix2-54): the joint realization built at G, and where it stops.**
  - *Inventory (tex path root → [54], Lean key / decl).* `G` minimal: `K .selection`;
    `P₀` maximal packing, `R₀ = R(P₀)`: `canonicalWindowPacking_spec`
    (`Statements/Spine.lean:352`), `K .maximalPacking`; `[13]`/`[25]`--`[27]`
    remainder normalized (componentwise `P₁₃`-free, no internal 3-core):
    `K .remainderNormalized` (`Strategy/SpineRows/RemainderNormalization.lean:41`);
    `[21]` enumeration / `lem:p13-window-package` rate: `K .windowPackageSeparated`;
    `lem:skeleton-dominates`: `K .skeletonDominates` (`Statements/SurplusPair.lean:1266`);
    `[158]` `K .windowPackageRealized`/`Unrealized`; `[22]` `K .hotColdPartition`
    (`WindowFamilyRealized`, `Statements/Spine.lean:399`); `[24]` `K .densityCap`
    (`Statements/Spine.lean:2863`) or `[160]`'s `K .denseDeficiencyBelow` /
    `K .coldRoute8Below`; `[34]`/`[47]` `K .curvatureFullRank`; `lem:wedge-lower`
    `K .wedgeSupply`; `[48]` `K .forcedCurvatureCost` (`forcedObstructionBits`,
    `Statements/Spine.lean:498`); `[50]`/`[51]` `K .remainderEntropyHigh`
    (`remainderStates`, `Statements/Spine.lean:294`); `[52]` `K .entropyPackageDemand`
    (`jointPackageDemand`, `Statements/Spine.lean:487`); `[53]` `K .entropyCapActive`;
    `lem:remainder-glue-injection`: `RemainderGlue.remainderStateCount_le_skeletonBudget`.
    Missing before this pass: the glue with *every* outer edge set (the relation
    `B ≥ RS·C(C(n,2)−C(|R₀|,2), m−e(R₀))` above was stated, not proved).  Now built:
    `Graph.RemainderGlue.remainderStateCount_mul_outerRoom_le_skeletonBudget`
    (vocabulary-free, `Graph/RemainderGlue.lean`) and, at `G`,
    `Contracts.Spine.remainderStates_mul_outerRoom_le` with
    `remainderOuterRoom = C(C(n,2)−C(|R₀|,2), m−e(G[R₀]))`.
  - *The construction (proved).* Supports are split into the pairs inside `R₀`
    (carrying the remainder state `H ∈ 𝒢(R₀)`) and the pairs not inside `R₀`
    (carrying everything else).  `Contracts.Spine.entropyCapBound_of_outerRoom`:
    if `2^{rate·s·p₁₃}·2^F ≤ remainderOuterRoom`, the window package of `P₀` and
    the forced bits are carried on the outer pairs, the product with the
    remainder states is realized by distinct skeletons of `G`'s class, and `[54]`'s
    bound holds.  The unretained arm of `entropyCapBound_of_hotColdPartition` now
    splits on this room at `G`; the hook `entropyCapBound_unretained` carries the
    complementary hypothesis `remainderOuterRoom < 2^{rate·s·p₁₃}·2^F`.
  - *Why disjoint supports stop there (explicit configuration at G).* The forced
    bits are not carried by the windows: `forcedObstructionBits` is the full-rank
    cost of `R₀`'s own curvature tests (`r_Ω(R₀)`, `lem:full-rank`), a function of
    the glued adjacency matrix (`lem:skeleton-dominates`' proof: every auxiliary
    datum is a function of it), so with the outer pairs fixed it is determined by
    `H`: it adds no states beyond `RS` unless the outer pairs vary.  The only room
    for the window package and the forced bits is therefore the outer room, and
    `Contracts.Spine.outerRoom_lt_of_entropyCapActive` proves that on `[54]`'s
    branch (`[53]` active) `remainderOuterRoom < 2^{rate·s·p₁₃}·2^F` at `G`: the
    hook is reached exactly in that configuration.
  - *Three routes on `¬X` at that configuration.* (1) Incompatible structure:
    `¬X` is a numeric relation among `n, m, p₁₃, |R₀|, e(G[R₀]), def⁺(R₀)` and
    `RS = |𝒢(R₀)|`; `[13]`/`[25]` (window-free, no 3-core), the packing's
    maximality and `P₁₃`-freeness of `R₀` are already inside `𝒢(R₀)`'s definition
    and only bound `RS` from *below* at `G` (`G[R₀] ∈ 𝒢(R₀)`), while the hook needs
    `RS ≤ B/(2^{rate·s·p₁₃}·2^F)` from *above*; no fact on the path gives an upper
    bound on `RS` beyond `C(C(|R₀|,2), e(G[R₀]))` (`remainderStateCount_le_choose`),
    and that bound gives only the outer room again (Vandermonde).  (2) Bound
    overload: the proved relation is `RS·room ≤ B`, and on the branch
    `room < 2^{rate·s·p₁₃}·2^F`; nothing is overloaded.  (3) Compressibility: a
    dependent pair (a forced bit determined by `H`) identifies no two supports of
    `G`; it only says the product is not a product.  All three fail.
  - *Circularity (Lean).* `Contracts.Spine.jointRealization_iff_entropyCapBound`:
    in its finite form (a state map on `𝒢_{n,m}` with range ≥ the family's count)
    the paper's step (2) is *equivalent* to `[54]`'s bound, i.e. to the negation of
    `[53]`-active.  So on every arm of `[54]` the paper's premise is its
    conclusion; the retained arm is proved only because `[22]` supplies it as an
    independent ledger fact (`WindowFamilyRealized P₀`).  On the `[158]`-no arms
    this is sharper: `[159]`'s `B < 2^{b_P}` refutes it before `[53]` is decided.
  - *Wiring against the tex diagram.* Part IV draws `[53]` yes → `[54]`; `[25]` is
    reached from `[24]` (bounded arm of `[153]`) and from `[161]` ("continue at
    [25]"), and the Lean arms `nearCubicLargeBudgetDensityCap` (`[158]`-yes) and
    `nearCubicLargeBudgetDenseRate` (`[161]`) match.  Part XII (tex 1327-1340)
    draws, on the dense pass `[162]`, `[53]` active → `[164]`
    (`def:all-cold-comparison`, closed by `lem:remainder-glue-injection`); the Lean
    arms `nearCubicLargeBudgetRateFailed`, `nearCubicLargeBudgetColdRate` and
    `nearCubicLargeBudgetDensityCap` called from `Survivor/Unrealized.lean` close
    `[53]`-active with the same `[54]` row (the `EG-NODE [164]` tag sits on those
    helpers).  Not rewired: `[164]`'s proof (tex 7843-7850) bounds only `|𝒢(R)|`
    ("the window package contributing nothing", the forced bits "realized inside
    `𝒢(R)` and not charged again", i.e. the `K = 0`, hot-only reading that the
    paper's own `eq:entropy-cap` and the approved exact `[53]` do not use), so a
    separate `[164]` terminal against `K .entropyCapActive` needs exactly this
    hook's bound and would add a second `sorry`.  The circularity is the paper's,
    not a Lean miswiring; `[164]` is the paper's own acknowledgement that on these
    arms only the glue (`RS ≤ B`) is available.  The wiring is user-approved: see "User-approved
    repairs", "[162]→[164] dense-pass wiring".
  - *Outcome.* The `sorry` stays (`OPEN-CONSTRUCTION [54] tex:9921`), narrowed to
    `remainderOuterRoom < 2^{rate·s·p₁₃}·2^F`.  The missing fact about `G` is an
    upper bound on the remainder class, `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`: the paper
    only ever supplies the lower bound `RS ≥ n^{|R₀|/d}` (`[50]` high arm).

## Open constructions

Each entry is a claim X that the paper asserts about G without constructing
it.  For each, ¬X was assumed at G, its witness built from G's objects, and
the three routes run (incompatible structure, bound overload,
compressibility).  An entry is here only if all three fail; if X is shown
false at G it is under Paper errors instead.  In the live Lean tree each open
construction is a `sorry` tagged `-- OPEN-CONSTRUCTION [node] tex:<line>` on
the proof of exactly that claim,
with the concrete obstruction at G recorded here, or, where the user decided
so, a residual carried by the node's open leaf (`[144a]`) or a returned outcome
(`[348]` at `[187]`).  `[153]`, `[162]` and `[54]` moved to "Returned
residuals (explicitly constructed)" (fix3).

### [144] `lem:same-token-bottleneck-routing`, parallel and cubic-first-separator cases (tex 5585-5620)

Both steps are open constructions (see "Open constructions"); this entry
keeps the paper claim and the [144a] representation.

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
- **Why it fails at G (the failing steps, about G's ledger at [144]).** At
  the node, G's ledger carries `K .homogeneousBottleneckPattern` (the audited
  role-homogeneous pattern at G's overloading token), `K .bottleneckRouting`
  (G's canonical same-token routing: the two equal-label pattern edges `π₁`,
  `π₂` and their demands), the capacity-token ledger, `K .bridgeless`,
  `K .highCentreNormalForm`, `K .selection` and `K .sparseSurplusSurvivor`.
  Let `Z = select?(X_{π₁} ∪ X_{π₂})` be the canonical connected support of the
  two response coordinates `r_{π₁} ≠ r_{π₂}` of G, and read each on G's own
  piece at `Z` (`SupportAtom.retainedPiece G Z X_{π_i}`).
  1. **tex 5589, "[the two coordinates] lie in the same boundary-degree
     fibre".**  The only equality the step has is the routing label's: equal
     token, blocker type, subtype and the boundary-degree entry of the
     demands' connector data at `T(p)`.  The step needs
     `(retainedPiece G Z X_{π₁}).boundaryDegreeProfile =
     (retainedPiece G Z X_{π₂}).boundaryDegreeProfile`, the profile of the
     two readings at `Z`.  No fact on G's ledger at [144] gives it, and the
     paper does not derive it from the label.
  2. **tex 5594 (and 5614 at a cubic first separator), "target-complete on a
     proper support ⇒ the target-complete compression exit".**  When the two
     readings are context-equivalent at `Z`, exit (c) of G needs
     `ReplacementSupport G Z`: a strictly smaller proper representative `Z'`
     of `Z` in G with the five hypotheses of `lem:replacement`.
     `def:admissible-rank-quotient` (tex 6026-6029) makes such a
     representative a condition of admissibility ("a target-complete
     proper-support correlation that has no smaller graph representative is
     not an admissible rank reduction"), not a consequence of
     context-equivalence.  The paper never constructs `Z'` for G's two
     readings, and no fact on G's ledger at [144] supplies it.
  The third case (same fibre and a separating context) is exit (b) at G's
  declared family (`declaredSparseSurplusExit_of_pairDefect`), which G's
  survivor refutes.  So on the no-handoff arm, G's ledger proves exactly the
  two cases above.  That is `SameTokenPatternPairUnresolvedStatement`
  (`sameTokenPatternUnresolvedRow`), pinned to G's canonical routing.
- **Step 2 (tex 5594/5614, 6026): OPEN CONSTRUCTION, pending the fold
  construction.**  The paper's compression step is about the admissible
  quotient's representative: the fold of the two context-equivalent readings
  realized by a smaller connected piece -- the same structure as [348] (the
  visibility of accepted cycles through the fold), and it is handed to the
  [348] construction.  Partial evidence only, built at G: a *reading* of G's
  piece at `Z` is not a replacement representative
  (`replacementSupport_of_retainedReading`, `Graph/NamedSurplusExits.lean`;
  `K .sameTokenReadingsNotReplacement`, idx 2905, published on the [144a] arm
  from G's survivor).  This does not decide the paper's step.
- **Missing constructions about G.** The profile equality of step 1 for G's
  two readings at `Z`, and the fold representative of step 2.  See "Open
  constructions".
- **Representation (user decision).** No `sorry`.  The two remaining cases are
  `SameTokenPatternPairUnresolvedStatement` (key
  `K .sameTokenPatternUnresolved`), published on the no-handoff arm of the exact
  decision `sameTokenHandoffDichotomy` (`K .typeBHandoff` /
  `K .typeBHandoffFails`).  They are carried by the open leaf [144a]:
  `Node144aOutcome` is the handoff, or the unresolved pattern pair, together
  with every [144] retained fact.

### [144] step 1 of `lem:same-token-bottleneck-routing`: equal boundary-degree profiles (tex 5589)

*Group SP (Surplus / Pair / [144]).*  Setting: G's ledger at the [144a] arm;
G's canonical routing, the equal-label pattern edges `π₁ ≠ π₂`, their
coordinates `r_{π₁} ≠ r_{π₂}` with declared supports `X₁ = X_{π₁}`,
`X₂ = X_{π₂}`, and `Z = select?(X₁ ∪ X₂)` with boundary `∂Z` (the vertices of
`Z` with an edge of G leaving `Z`).  Reading `i` is `retainedPiece G Z Xᵢ`:
G's piece at `Z` with only the edges inside `Xᵢ`.

- **X.** `𝐝_∂(reading 1) = 𝐝_∂(reading 2)`.
- **¬X witness at G.** A vertex `v ∈ ∂Z` whose number of G-neighbours in `Z`
  along edges inside `X₁` differs from that along edges inside `X₂`.  For
  example, `v ∈ ∂Z ∩ (X₁ ∖ X₂)` with a G-neighbour in `X₁ ∩ Z` has degree
  `≥ 1` in reading 1 and `0` in reading 2.
- **Route 1, incompatible structure: fails.**  The ledger's facts about the
  pair are the routing label (`def:same-token-routing-germs`, tex 5555-5562:
  token, role, subtype, open/triangular status, the profile of the *bounded
  port supports* `T(p), T(q)`, `P₁₃` labels, suppressed-chord flag), the
  canonical routes and first separator, the role-homogeneous pattern,
  `K .bridgeless`, `K .highCentreNormalForm`, `δ ≥ 3` and target avoidance.
  None of them constrains the degrees at `∂Z` of the unbounded response parts
  `Γ(p)`.  Two readings in different fibres are also not an exit: exit (b)
  needs one fibre.
- **Route 2, bound overload: fails.**  A degree difference at one boundary
  vertex changes no counted quantity of the [136]/[137] budgets (token loads,
  role fibres, `Q_geom`, the pattern size); the routing label, and so the
  pigeonhole that produced `π₁, π₂`, is unchanged.
- **Route 3, compressibility: fails.**  Readings in different fibres cannot
  be identified by a target-complete quotient (`lem:degree-profile-fibres`),
  so no quotient-based smaller representative arises; and no reading of G's
  piece at `Z` is a replacement at all (step 2 below).
- **Status.** OPEN CONSTRUCTION: the first disjunct of the [144a] residual
  `SameTokenPatternPairUnresolvedStatement`.

### [144] step 2 of `lem:same-token-bottleneck-routing`: the fold representative (tex 5594/5614, 6026)

*Group SP (Surplus / Pair / [144]).*

- **X.** For context-equivalent readings of `r_{π₁}`, `r_{π₂}` at `Z`, the
  admissible quotient identifying them has a strictly smaller proper
  representative (the fold realized by a smaller connected piece), giving
  exit (c).
- **Status.** OPEN CONSTRUCTION, pending the fold construction shared with
  [348]; handed to the [348] agent.  Partial evidence at G: no reading of G's
  piece at `Z` is a replacement (`K .sameTokenReadingsNotReplacement`, idx
  2905): each reading either loses `δ ≥ 3` at an internal vertex outside its
  support, changes `𝐝_∂`, or is not smaller.  The fold is a different object
  and is not decided by this.

### [144] step 2 (tex 5594/5614, 6026): the fold analysis of [348] applied (fix2-348)

*Handed over from fix2-SP (d69424b); complements fix2-SP's "[144] step 2"
open construction and changes no Lean.*  Evidence:
`audits/erdos-64-red-team/fix2-348/Obstruction144.lean` (compiles; axioms
propext, Classical.choice, Quot.sound; no sorry).  Setting: G's [144a] arm,
`Z = select?(X₁ ∪ X₂)`, readings `ρᵢ = retainedPiece G Z Xᵢ`, residual
disjunct `ContextEquivalent ρ₁ ρ₂`.

- **Clause check of any representative `Z'` of `Z` (the fold included).**
  Profile, `δ ≥ 3` and "smaller" can hold for a fold, but the response clause
  of `ReplacementSupport` fails at G's own context `Y_G` for EVERY smaller
  baseline `Z'` (`representative_not_responsive_at_G`: minimality gives an
  accepted cycle in `Z' ⊕ Y_G`, and `Z ⊕ Y_G ≅ G` has none).  So exit (c) at
  [144] can only arise as a contradiction derived from `ContextEquivalent ρ₁
  ρ₂`, through the analogue of `Visibility`: every accepted cycle of
  `Z' ⊕ Y_G` yields a context separating `ρ₁` from `ρ₂`.
- **What G's facts give.**  Spectral separation refutes context equivalence at
  G (`readings_not_contextEquivalent_of_spectra`, through the synthetic path
  context of `GluedCrossingCycle.lean`; `ρ₂ ⊆ G` has no internal accepted
  cycle): if two labels of `∂Z` are joined in `ρ₁` by a path whose length
  plus `k + 1` is accepted and `ρ₂` has no such path, the disjunct is false.
  So the residual disjunct forces equal accepted-complement label-path
  spectra of the two readings.
- **Where it fails (configuration at G).**  `X₁ = X₂` with
  `r_{π₁} ≠ r_{π₂}` (more generally, readings with no label-to-label
  structure that any context sees): the readings are equal, the disjunct holds
  (`readings_contextEquivalent_of_support_eq`), no context separates them, and
  the identification is label-only, "not an admissible rank reduction"
  (tex 6031-6035).  Visibility is false there; the ledger at [144] has no
  fact on the declared supports of the two pattern coordinates beyond the
  routing label, so no route closes it.  (The two coordinates differ by their
  label, the demand pair, `pairCoordinate label support`, so `first ≠ second`
  does not separate their supports: both are the canonical connected
  superset of their own seeds, and nothing on the ledger makes those
  differ.)
- **Follow-up (user): equal spectra as a compression candidate.**
  1. *Response determinacy.*  Pairwise label-to-label spectra do not
     determine the response of a target-free piece: a multi-crossing cycle
     uses a vertex-disjoint system of piece paths.  Two readings can have the
     same pairwise spectra with `a`-`b` and `c`-`d` paths disjoint in one and
     meeting in the other; a context with an `b`-`c` and a `d`-`a` path of
     tuned lengths then separates them.  The data that determine the response
     are the linkage spectra (vertex-disjoint path systems between labels,
     with their pairing, lengths and the labels they meet).  This needs no
     separate theorem here: `ContextEquivalent` quantifies over every context,
     multi-crossing ones included, so the residual disjunct already IS
     response equality of `ρ₁` and `ρ₂`, i.e. linkage equality.
  2. *Compression, clause by clause.*  Every representative `Z'` of `Z` is
     one of two kinds:
     - A subgraph of G's piece at `Z`.  This covers "replace `ρ₁` by `ρ₂`",
       i.e. delete the edges inside `X₁` not inside `X₂`, and every reading.
       The response clause holds for free in every context
       (`subgraph_response`), so the equivalence `ρ₁ ~ ρ₂` is not used.
       G's minimality refutes `δ ≥ 3 ∧ smaller` for it
       (`subgraph_not_baseline_and_smaller`): a deletion that keeps
       `δ ≥ 3` would be a smaller target-free graph.  The profile clause
       additionally fails whenever a deleted edge meets `∂Z`.
     - Not a subgraph (a fold).  Then the response clause fails at `Y_G`
       (`representative_not_responsive_at_G`).
     So no clause of `ReplacementSupport` or `CompressibleSupport` reads the
     equivalence of the two readings.  That equivalence relates two readings
     of `Z` to each other, never G's piece to a smaller piece, and equal
     linkage spectra of `ρ₁`, `ρ₂` build no compression of G.
  3. *[144a].*  The disjunct carries `ContextEquivalent` (full target, all
     contexts), i.e. already linkage equality.  That is consistent at G
     (configuration `X₁ = X₂`).
- **Follow-up (user): routes 1 and 2 at the configuration `X₁ = X₂`.**
  *Configuration at G.*
  - `canonicalSameTokenRouting G = some routing`, with pattern edges
    `π₁ = routing.demands.first ≠ π₂ = routing.demands.second` in the
    canonical homogeneous pattern (matching or star, `HomogeneousPatternSpec`).
  - `Xᵢ = (canonicalPairActivation.pairSupport πᵢ).getD ∅`, i.e. `select?`
    of the seed `pairSeed πᵢ = ⋃_{d ∈ πᵢ} (T(d) ∪ Γ(d))`, with `X₁ = X₂`.
  - The coordinates `pairCoordinate πᵢ Xᵢ` differ only in their label `πᵢ`.

  *Route 1, incompatible structure.  Fails; nothing G constructs separates
  the two supports.*
  - **Distinct endpoints and ports.**  `SameTokenDemandsSpec` asks
    `π₁ ≠ π₂` and equal actual routing labels.  In the matching case the
    pattern edges are disjoint as demand sets (`IsMatching`), but nothing
    makes the declared supports `T(d) ∪ Γ(d)` of distinct demands disjoint or
    distinct.  In the star case the two edges share the centre demand, so the
    seeds share `T(c) ∪ Γ(c)`.  Either way both seeds may lie in one minimum
    connected set.
  - **Activation injectivity.**  `DemandActivation` (`SurplusBlockers.lean:142`)
    has no injectivity field.  `declaredSupport` is a function of the
    demand, so it can repeat.
  - **Canonical support selection.**  `select?` returns the lexicographically
    first minimum-cardinality connected superset of the seed.  It is not
    injective on seeds (`select? S = X` only gives `S ⊆ X`), so equal outputs
    from distinct seeds are allowed.
  - **Maximal routes and first separator.**  The routes run from the token
    root to the demand endpoints `dᵢ.2`.  `SameTokenRoutesSpec` and the
    separator never read `Xᵢ`, so `X₁ = X₂` gives no information on them.
    Conversely, a trivial separator (e.g. equal demands `d₁ = d₂` at a star
    centre) does not force or exclude `X₁ = X₂`.  The [144a] statement pins
    the routing, not the separator, so no closed parallel case absorbs the
    configuration.
  - **Target and minimality.**  `X₁ = X₂` gives equal readings.  Neither is a
    replacement of G's piece (subgraph lemmas above), so there is nothing to
    contradict.

  *Route 2, bound overload.  Fails; no counted quantity reads the supports.*
  The token load and role fibre count pattern edges (Finsets of demands),
  and `Q_geom` / `patternBound` counts routing labels.  Two pattern edges
  with one support are still two edges with two labels, so no count
  doubles.  The only cap in play, `patternBound ≤ pattern.card`, is a lower
  bound that the configuration keeps.

  *Route 3* is as in the compression analysis above.  So the configuration is
  not refuted at G, and [144a]'s context-equivalence disjunct stays open.
- **Status.**  OPEN CONSTRUCTION, unchanged; [144a] keeps the disjunct.

### [348] (b) at a unified entry: the fold does not respond like `B_u` at G's own context (tex 15362)

*fix2-TR steps 2/2b; evidence `audits/erdos-64-red-team/fix2-TR/Step2Evidence348.lean`.*

- **Assertion X (tex 15362).**  At an entry `ξ = (X, w, u, B_u)` of G's
  unified set, alternative (b) is exit (5), a contradiction with
  `cor:uncompressible`: the quotient's smaller representative responds like
  `B_u` in every context, in particular in G's own context `Y_G`.
- **¬X built at G.**  With (b) at `ξ` (the `[348]` arm) and a fold pair
  `keep ≠ remove` of `B_u - ∂B_u` off the kept declared supports with no common
  neighbour, the fold `R = identifyInternal keep remove` is a realization of the
  quotient in `B_u`'s fibre, `δ(R ⊕ Y_G) ≥ 3`, `R ⊕ Y_G < G`
  (`fold_clauses`).  `invisibleCycle_of_b` proves at G: `R ⊕ Y_G` has an
  accepted cycle `C` (G's minimality) and `¬ declaredAlgebra R Y_G` ((b) at the
  profile-compatible context `Y_G`, `b_at_G_context`).  So the ¬X witness is
  the explicit accepted cycle `C` of `R ⊕ Y_G` through the merged vertex, not
  visible to the declared `u`-supported algebra.
- **Route (1), incompatible structure.**  `C` is not a cycle of G (unmerging
  turns it into a `keep`-`remove` path of G), so target avoidance is not
  contradicted.  [12] (key 2301) part 1 applies only to a `DeclaredQuotient`,
  whose `contextUniversal` field IS the full-target equivalence being sought;
  its "consequently" part concludes that the fold identification is
  target-defective, which is consistent with `C`.  (b) itself would be
  contradicted exactly when `C` is declared-visible (`closes_of_visibility`);
  `invisibleCycle_of_b` shows it is not.
- **Route (2), bound overload.**  The census bounds at `[123]`
  (`α(ξ) ≥ 2`, `K .route8UnifiedEntryCensus` 340; the deficit `K .route8UnifiedDeficit`
  339) count declared essential carriers and entries; an undeclared accepted
  cycle of a glued realization enters none of them.
- **Route (3), compressibility.**  The smaller representatives available at
  `B_u` are the folds and the retained readings; each glued to `Y_G` carries an
  accepted cycle by minimality (`response_clause_fails_at_G_context`), so
  none is a `CompressibleSupport` without the same visibility fact.
- **Open construction.**  `Visibility(R) : Target(R ⊕ Y_G) → declaredAlgebra R Y_G`
  at the fold of a (b)-entry of G, together with the fold pair.  Until it is
  constructed, `[348]` is routed as `thm:main` routes it: a returned outcome at
  `[187]` (no `sorry`).
- **fix2-348: what target-completeness gives, and the exact obstruction.**
  Evidence: `audits/erdos-64-red-team/fix2-348/Obstruction348.lean` (compiles,
  axioms propext, Classical.choice, Quot.sound; no sorry).
  - *Inventory of target-completeness (tex).*

    | source | tex | what it says | gives `Visibility(R)`? |
    |---|---|---|---|
    | `def:target-complete-quotient` | 5858-5866 | an identification preserves the profile and the *full* target predicate against every `T`-context | no: a property a quotient may have, not a fact about `B_u` |
    | `def:typeA-trace-basin`, declared family | 10738-10743 | `R_u(B_u)` is complete for the *declared* `u`-supported events; route-8 quotients "are tested only against this declared `u`-supported target algebra" | no: completeness is for declared events; an accepted cycle of `R ⊕ Y_G` need not be one |
    | `def:typeA-trace-basin`, (b) target-complete | 10757-10764 | all realizations give "the same target predicate" as `ρ_u(B_u)` at every compatible context | Lean `TraceResponseQuotient` clause 3 = declared-algebra equivalence (the declared reading of 10741-10743) |
    | target-complete-minimality | 10776-10796 | TCM = none of (a)-(d) | no: a (b)-entry is by definition not TCM (it is a target-defect entry); TCM is never available on `[348]`'s arm |
    | `lem:typeA-internal-quotient-mixed` | 12422-12457 | "a distinguishing event must use at least one coordinate forgotten ... Hence the chosen event is `u`-supported" | this sentence IS `Visibility` for full-target events, asserted without construction; under the declared reading it is `distinguishingEventCrosses` (trivial) |
    | `lem:typeA-one-terminal-collapse` | 12459-12500 | `α(ξ) ≤ 1` ⇒ a nontrivial target-complete quotient, i.e. (b) | Lean `route8Entry_smallCoreQuotient`: (b) HOLDS at every `α ≤ 1` entry |

  - *Is Lean's (b) weaker than the paper's?*  No restatement helps.  The
    full-target reading of 10760-10764 makes (b) empty at G (the realization
    `B_u` plus a disjoint internal cycle of accepted length responds with a
    cycle at `Y_G`, while `B_u ⊕ Y_G ≅ G` has none).  That would close `[348]`
    trivially but falsify `lem:typeA-one-terminal-collapse` at G, so the
    census `α ≥ 2` of `K .route8UnifiedEntryCensus` (340), proved from
    quotient-freeness through `route8Entry_smallCoreQuotient`, would lose its
    proof: the same gap moves to `[340]`.  The Lean keeps the declared reading,
    under which the collapse lemma is a theorem.  `TargetComplete`,
    `TargetCompleteMinimal`, `QuotientRealization` are unchanged.
  - *Exact obstruction (configuration at G).*  A unified entry `ξ` of G with
    `α(ξ) ≤ 1`.  At such `ξ`:
    1. the declared algebra is identically false, at every piece and context
       (`declaredAlgebra_empty_of_alpha_le_one`: a visible declared event is a
       core-retained crossing coordinate, two carriers, `α ≥ 2`);
    2. (b) holds (`b_of_alpha_le_one`, the project's
       `route8Entry_smallCoreQuotient` with empty crossing family), so G's
       ledger takes the `[348]` arm (`residual_of_alpha_le_one`:
       `¬ Route8QuotientFreeStatement`);
    3. `Visibility(R)` reduces to `¬ Target(R ⊕ Y_G)`, and for every fold `R`
       of `B_u` minimality refutes it (`not_visibility_of_alpha_le_one`).
    Conversely, the free arm gives `α ≥ 2` at every unified entry
    (`route8EntryFacts`).  So closing `[348]` is at least as strong as
    `α(ξ) ≥ 2` at every unified entry, which is the conclusion of
    `lem:typeA-unified-carriers` itself; its proof for target-defect entries
    is the step at tex 15362 (circular), and for route-8 entries it uses TCM,
    which a (b)-entry does not have.
  - *Three routes at that configuration.*  (1) Incompatible structure: the
    (b)-clause is vacuous there (empty algebra); (c) and (d) are already
    refuted (`not_traceDelocalization`, no-handoff filter); target avoidance
    is not contradicted (the fold cycle unfolds to a `keep`-`remove` path of
    G); [11]/[12] as in step 2b.  (2) Bound overload: at `[348]` G's ledger
    carries the deficit `K .route8UnifiedDeficit` (339), which counts entries,
    not `α`; every bound using `α ≥ 2` is downstream of `[348]`'s free arm.
    (3) Compressibility: the core restriction `ρ|_{C_ess}` is full-target
    equivalent to `ρ` (`Entry.essentialCore_complete`), but it is a
    deletion-type reading (internal edges outside retained supports dropped),
    so it breaks `δ ≥ 3` and is not a `CompressibleSupport`; the fold needs
    `Visibility`, false by 3.
  - *Remark (not formalized, not used).*  At an entry whose declared algebra
    has a core-retained crossing coordinate whose event passes through a
    label `ℓ ∈ ∂B_u` lying on a cycle of G with two interior vertices `a ≠ b`
    of `B_u`, (b) is refuted directly at `Y_G` without minimality: `B_u` plus
    a fresh `a`-`b` path of tuned length realizes every response quotient
    (identity placement, no old incidence changed) and closes an accepted
    cycle through `ℓ`.  So the (b)-arm lives on entries whose declared algebra
    is effectively empty, of which `α ≤ 1` is the formalized case.
  - *Status.*  OPEN CONSTRUCTION, unchanged: `[348]` stays a returned outcome
    at `[187]`.  The missing fact about G is `α(ξ) ≥ 2` at every unified
    target-defect entry (no unified entry with `α ≤ 1`).
  - *Follow-up (user): is `B_u` at an `α ≤ 1` entry compressible?*  No, and
    the reason is the same as at [144] step 2 below
    (`audits/erdos-64-red-team/fix2-348/Obstruction144.lean`; the lemmas are
    generic in the support, instantiated at `S = B_u`).
    - The `α ≤ 1` information is the core completeness
      `ρ|_{C_ess} ~ ρ` (`Entry.essentialCore_complete`, full target, every
      `∂B_u`-context).  It relates two *readings* of `B_u`, both built from
      `retainedBasinPiece`.  It does not relate G's piece at `B_u` to a
      smaller piece.
    - Candidate `Z' = retainedBasinPiece B_u (retained supports)`.  It keeps
      every label edge, so the profile holds
      (`retainedBasinPiece_boundaryDegreeProfile`).  It is a subgraph, so the
      response clause holds in every context without using `α`
      (`subgraph_response`).  G refutes `δ ≥ 3 ∧ smaller` for it
      (`subgraph_not_baseline_and_smaller`).
    - Any non-subgraph candidate, the fold included, fails the response
      clause at `Y_G`.
    - With a single carrier, the path spectra through it only restate the
      core equivalence.  They feed no clause.
    So `α ≤ 1` yields no compression of `B_u`.  [348] does not close.

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
`nearCubicLargeBudgetDensityCap`) with the [54] row. Reason: [164]'s proof uses
the K=0 / hot-only reading, which the approved exact [50]/[53] supersedes.

- **Where recorded.** The fix2-54 addendum under `[54]` ("Returned residuals
  (explicitly constructed)", analysis before fix3) gives the wiring analysis
  (tex 7843-7850).
