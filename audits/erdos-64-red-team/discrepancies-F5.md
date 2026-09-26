# Lean versus paper: registered discrepancies, family F5 (Spine / Cold / NearCubic)

Format and admission rule as in `lean-vs-paper-discrepancies.md`: the Lean
deviates only when it is kernel-checked, weakens no paper fact, closes the node
the paper closes, and is at least as strong.  Paper gaps that the Lean repairs
are recorded with the gap, the repair, and why the result is at least as
strong.

## [53]: the entropy-cap test sits on the high-entropy arm, with `K = 0`

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

## [57] and [173]: the exact collision test replaces the asymptotic cap

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

## [34]/[47]: exact full rank

- **Paper.** `lem:full-rank`: `r_Ω(R) ≥ W₂(R) − o(W₂)`.
- **Lean.** `curvatureRankDichotomy`'s no arm `K .curvatureFullRank` publishes
  `r_Ω(R) = W₂(R)` at the fixed maximum packing (now pinned:
  `packing = canonicalWindowPacking`).  It serves `[34]` and `[47]`.
- **Why the Lean prevails.** It is the exact finite complement of the rank-drop
  arm and implies the paper's inequality; kernel-checked.

## [8]: `NoProperBaseline` also records connectedness

- **Lean.** `K .noProperBaseline` = `lem:no-proper-core` ∧ `Connected`
  (`connected_of_noProperBaseline`).  The added conjunct is a proved
  consequence; nothing is weakened.

## [13]: `lem:replacement` without hypothesis (iii)

- **Lean.** `K .replacementExclusion` excludes every one-way replacement
  (`ReplacementSupport`); hypothesis (iii) (no internal power-of-two cycle in
  `X′`) is not required, because a cycle inside `X′` is already caught by the
  one-way inclusion (i) at `G`'s own outside context.  Excluding more
  replacements is a stronger exclusion.

## [14]: now paper-exact

`UncompressibleStatement` is `∀ support, ¬ ReplacementSupport …`, the first
assertion of `cor:uncompressible` ("exactly `lem:replacement`") under
`def:target-complete-compression` (one-way inclusion).  Consumers that hold a
two-way `CompressibleSupport` weaken it with
`replacementSupportOfCompressibleSupport`.

## [50]: now paper-exact at the fixed packing

`K .remainderEntropyHigh` / `K .remainderEntropyLow` are the rate test and its
negation on the remainder of the fixed maximum packing
(`packing = canonicalWindowPacking`), decided by `remainderEntropyDichotomy`.

## [56]: the density input differs by arm (`lem:dense-deficiency-routing`)

- **Paper** (tex:7648-7672): "Nodes [56]--[64] consume the density cap only
  through `def⁺(R) − σ(R) < |R|/4`"; `[161]` supplies it from the deficiency
  test in place of `[24]`.
- **Lean.** Three `[56]` rows publish `K .netDeficiencyCap` from the arm's
  input: `netDeficiencyCapRow` (`[24]`'s `K .densityCap`),
  `denseNetDeficiencyCapRow` (`[160]`'s `K .denseDeficiencyBelow`, the `[161]`
  arm), `routeEightNetDeficiencyCapRow` (`[146]`'s `K .coldRoute8Below`, the
  `[147]` arm, `τ(θ) < 3/13 < 1/4`).  The spine `[47]`--`[56]` is one
  composition per input (`nearCubicLargeBudget*`).

## [156]: G2 closes through the sparse exit (b) (gap repair)

- **Paper.** `lem:cold-bounded-germ-trichotomy` G2 (tex:7361): the induced
  quotient is target-defective, "routed to the sparse exit or exit-(4) ledger.
  Both are excluded by `def:surviving-cold-branch`."  The earlier Lean recorded
  G2 as the `[187]` cold outcome.
- **Lean.** `Contracts.Spine.sparseSurplusExit_of_distinguishing`
  (`Graph/Contracts/Spine/ColdGerm.lean`): the germ's two same-interface
  representatives, identified by its cold corridor state on its connected
  support, give the attempted quotient of `SparseSurplusExit.targetDefect`, and
  G2's distinguishing context is its defect.  Core closes the G2 arm against
  `K .sparseSurplusSurvivor` (`instIncompatibleColdGermSomeDistinguishingSurvivor`)
  on the realized arm, the dense linear arm and the absorbed `[176]` arm.
- **Why at least as strong.** It is the paper's argument, kernel-checked, and
  it closes the node the paper closes.
- **Caveat for the coordinator (not an F5 key).** `SparseSurplusExit.targetDefect`
  (`Graph/NamedSurplusExits.lean`) accepts *any* two boundary pieces on a
  connected support with a distinguishing context.  Two arbitrary pieces on the
  boundary of a single vertex (one containing an internal 4-cycle, one empty,
  glued to the empty context) already satisfy it, so
  `SurvivesSparseExits` fails on every graph with a vertex and
  `K .sparseSurplusSurvivor` is uninhabited on every counterexample.  The
  paper's clause (b) concerns identifications of *local target-response
  coordinates of the actual piece*; the Lean clause should be restricted to
  those (F4, `def:named-surplus-exits`).

## Remaining divergences (not admitted under the exception)

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
