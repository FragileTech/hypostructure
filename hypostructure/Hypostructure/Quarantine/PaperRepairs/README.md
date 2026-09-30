# Quarantined paper repairs (reference only)

This folder holds Lean analyses that are not part of the proof, which implements the paper
without deviations and reports its errors. They are kept as a reference.
- No live module may import them.
- They are listed in `hypostructure/quarantine.txt`.
- The live proof represents each paper error as a tagged `PAPER-ERROR` sorry at the node
  where the paper makes the claim.

| File | What it is |
|---|---|
| `Node144Gap.lean` | Lean-checked analysis of the [144] step "target-complete ⇒ compression (c)": the survivor dichotomy (L1′), a target-complete pair adds no exit (L3), the parallel-case positional lemma (L4), and the trie bound (P2). |
| `ColdF4Charge.lean` | Cold (F4) charge: exact characterization of the F4 count for whole-piece registries (the evidence that the tex 7234 whole-support registry fires (F4) at segment 0 on a subcubic support); the heavy-centre chain `heavy_handoff_not_subcubic` → the loss bound, whose generalized form is in the live tree (see below). |
| `ColdF2Refutation.lean` | Evidence for the [153] (F2) paper error (tex 7265-7270): an (F2) pair `(0, right)` is never a clause-(b) sparse exit (`not_residualTargetDefect_prefixPair_zero`, `coldF2_not_clauseB`); the all-presentations form of `coldFailureDefect_excluded` is false (`coldFailureDefect_excluded_is_false`); the two-label cut-state reading would make clause (b) vacuous (`edge_twoPath_sameFibre_targetDefect`). Includes the `F2PathContext` path-context analysis (Part 0). Part 4: at G the Lean (F2) at a segment is exactly an earlier equal cut state (`EqualStates.coldFirstFailureDefectAt_iff`), every (F2) pair is a `d_∂` separation and never a clause-(b) exit (`EqualStates.not_residualTargetDefect_prefixPair`), and distinct states force the first failure within `Q_cold` (`EqualStates.first_lt_stateBound`). |
| `EntropyCapAllCold.lean` | Evidence for the [54] all-cold paper error (tex 9921): the numeric relations the ledger gives at `[54]` (remainder glue, skeleton budget, the all-cold overflow `allCold_code_overflow`, node `[48]`, node `[51]`) are consistent with both `entropyCapBound_allCold` and its negation (checked with `decide`), so the hook is not refutable from them. |
| `SilentLaneClosure.lean` | A silent-lane closure at node `[184]` (`selectedSilentExitSevenFree_unifiedVisibleResidual_contradiction`) that splits node `[109]` by the node-`[94]` provenance and closes the silent lane against `lem:typeA-unified-visible-ownership`. The paper has no such split; `[109]` goes to `[110]` on every lane. The file does not elaborate against the live tree (its input statement is not in it). |

Relation to the live tree:
- The residual of the [144] paper error is carried by [144a] (key
  `sameTokenPatternUnresolved`), by user decision.
- The heavy-centre cold (F4) registry is in the live tree as a user-approved
  repair: `ColdDeclaredHandoffSupport` is G's heavy handoff centres
  (tex 7326-7329, 7926-7930), and the [153] F4 count bound is proved
  (`Contracts/Spine/ColdSubcubicCharge.lean`,
  `Contracts/Spine/ColdHandoff.lean` `coldF4_card_le_corridorLoss`).
  `ColdF4Charge.lean` is the whole-support analysis.
- F5's [156] G2 closure is not in the live tree.
