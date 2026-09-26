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

## [137] on the independent branch: the yes arm of the coupled-excess test

- **Paper** (diagram tex:1204 and 1235–1246; `cor:coupled-single-graph-overload-budget`
  tex:4105; `prop:single-graph-sparse-pressure-routing` tex:4361). The [131]
  "count holds: free pairs" edge enters the [137] diamond "coupled excess
  D_all>0?". On the independent branch every pair is blocker-free, so there is
  no blocked-pair demand, and the paper's route to [138] reads this as
  D_all = 0.
- **Lean.** `freePairCoupledExcessDichotomy`
  (`hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean`)
  decides the paper's predicate, which is D_all > 0 at the object's own
  capacity-token ledger. It uses the same yes key, `K .sparsePressureOverload`,
  as the dependent branch.
  - The no arm publishes σ(G) ≤ C_sp⌈√n⌉ from the [131] count and goes to
    [138].
  - The yes arm is closed through the framework:
    `freePairSurplusEstimateRow.runAndCloseIncompatible overloadHistory
    (K .surplusAbove) (K .spineSurplusEstimate)`, using the instance
    `instIncompatibleSurplusAboveSpineSurplusEstimate`.

  Caller: `Assembly.Internal.strictSurplusIndependent`
  (`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict/Independent.lean`).
- **Difference.** The paper excludes D_all > 0 through "no blocked pairs, so
  N_* = 0, so D_all = 0". The Lean closes the D_all > 0 arm with the [131]
  count's quadratic surplus bound against the strict-surplus test [19]. That
  contradiction holds on the whole [131]-realized branch, whatever D_all is.
- **Why the Lean prevails.**
  - The overload key's certified ledger carries its own entropy budget, and
    the paper never ties that budget to E_spine. The paper's step "N_* = 0,
    so D_all = 0" therefore needs a link that the paper does not state.
  - The Lean contradiction uses only facts the paper already establishes: the
    [131] count and [19].
  - It is kernel-checked, leaves no arm assumed, and closes the arm the paper
    closes.
