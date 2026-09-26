# Lean versus paper: F4 (Surplus / Homogeneous / Pair) discrepancies

Family register for the contract-lemma migration of F4, in the format of
`lean-vs-paper-discrepancies.md`.  Each entry names the node, the paper's
argument, the Lean argument and its declarations, and the reason the Lean is
at least as strong.

## [137] on the independent branch: one exact coupled-excess test, both arms closed by [138]

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

## [139], [141], [143]: the class tests are on the existence of an overload witness in the class

- **Paper** (diagram tex:1204-1208, 1240-1244). [139] asks whether "the
  overloading token" of [137] lies in 𝔗_W, [141] whether it lies in 𝔗_R, and
  the no-no arm is the primitive audit [143].
- **Lean.** `windowOverloadClassDichotomy` and `remainderOverloadClassDichotomy`
  (`HomogeneousBottleneckRows/WindowOverloadClass.lean`) decide, by exact case
  analysis, whether some overload witness of the object has its token in 𝔗_W
  (resp. 𝔗_R); the no arms `K .windowClassAbsent`, `K .remainderClassAbsent`
  are the literal negations.  `primitiveClassOverloadRow` (contract lemma
  `Graph.Contracts.SurplusPair.primitiveClassOverload_of_classesAbsent`) then
  shows that the [137] overload witness is primitive.  Each audit
  ([140] `windowBottleneckAuditRow`, [142] `remainderBottleneckAuditRow`, [143]
  `primitiveBottleneckAuditRow`, all through the one contract lemma
  `homogeneousBottleneckPattern_of_overloadAtClass`) reads the witness of its
  own class.
- **Difference.** The earlier Lean tested the class of one witness chosen
  inside the decision, and its two keys were two existentials over separately
  chosen witnesses (not complements).  The Lean now tests the class predicate
  itself.
- **Why the Lean prevails.** The three audits apply to every overload witness
  with no further hypothesis, so choosing a 𝔗_W (then 𝔗_R) witness whenever one
  exists routes every object to an audit of a class its overload actually
  has; the keys are exact complements on the object, and no arm is lost.

## [131] and [137]: the count-fails arm is the negation of the count

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

## [182]: each pair-code test has its own exact negation

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
