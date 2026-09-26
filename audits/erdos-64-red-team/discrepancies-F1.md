# Lean versus paper: registered discrepancies, family F1 (Type A)

Format and admission rule as in `lean-vs-paper-discrepancies.md`: the Lean
argument is kernel-checked, weakens no paper fact, closes every node the paper
closes, and is at least as strong as the paper's argument.  Every entry names
the node, the paper's argument with tex lines, the Lean argument with its
declarations, and the reason the Lean is at least as strong.

## [89], [93], [95], [97], [99], [101], [103], [105], [107]: each exit test is asked of every candidate at once

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

## [62]: the surplus test is asked of every negative piece

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

## [102] → [89]: the recompute-`L₄` loop is realized by its terminating outcome

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
