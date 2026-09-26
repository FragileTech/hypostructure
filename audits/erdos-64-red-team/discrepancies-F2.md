# Lean versus paper: registered discrepancies, family F2 (Type B)

Format as in `lean-vs-paper-discrepancies.md`: each entry names the node, the
paper's argument, the Lean argument with its declarations, and why the Lean is
at least as strong.

## [65]–[85]: Type B facts are stated over the support family, not per entry lane

- **Paper** (diagram tex:950–1035; `def:typeB-assigned-ledger`,
  `def:decorated-fan-envelope`, `lem:absorbed-germ-fan-data`,
  `lem:same-token-bottleneck-routing`). Node [65] receives one assigned Type B
  support `X = (Y_X, H_X)` from [64], [66]/[108], [177] or [144]; nodes
  [67]–[85] reason about that support.
- **Lean.** `TypeBSupport` (`hypostructure/Hypostructure/Graph/Statements/TypeB.lean`)
  is the family of all assigned supports of the object in the three entry forms
  (`TypeBCanonicalForm`, `TypeBAbsorbedForm`, `TypeBSameTokenForm`). Every
  Type B key is stated over this family: row facts are universal over it, and
  each decision ([68] `typeBFanDegreeDichotomy`, [71]/[80]
  `fanCertificateDichotomy`, [72]/[81] `directCycleDichotomy` and
  `b2AssignmentDichotomy`) is a family predicate and its exact negation, proved
  exact by `typeBFanDegreeFourCentres_iff_not_heavy`,
  `typeBFanCertificateResidual_iff_not_marked`,
  `typeBFanDirectCycleFree_iff_not_directCycle` and
  `typeBB2Obstruction_iff_not_choice` (`Graph/Contracts/TypeB/`). The previous
  three-lane Or keys (canonical | absorbed | same-token) are gone; so are the
  lane `rcases` inside decisions.
- **Why at least as strong.** Every universal fact holds in particular at the
  entering support, so no paper fact about X is weakened. The decisions are
  exhaustive and exclusive on one pinned object (the family is a definable
  predicate of the object, not a chosen witness). Each argument is one
  contract lemma instead of three lane copies. The terminal at [72]
  (a direct configuration is an accepted cycle) closes on either arm of the
  family exactly as the paper closes it for X.

## [70]: fan-safe graph and certificate cap are one fact

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
  on the [177] branch). `TypeBFanSafeStatement` is kept for the vocabulary.
- **Why at least as strong.** Clause (i) is now a proved fact at every centre
  instead of an iff with arbitrary predicates; clauses (ii)–(v) are defining
  conditions of the fan-safe graph, not claims.

## [74]/[82] → [76]/[85]: no split at the bridge reduction

- **Paper** (tex:976–979, 1020–1023; `prop:typeB-bridge-reduction`). The B2 yes
  edge goes [74] → [76] → [77]; [74] is not a diamond.
- **Previous Lean.** `typeBExclusionDichotomy` split on the sign of the
  remaining core charge and closed the nonnegative arm inline
  (`NearCubicCertificate`), an arm that was uninhabitable (its `Holds`
  contained both the support's negative charge and `N₀ ≥ 0`).
- **Lean now.** Two rows in paper order: `typeBExcludedRow` ([74],
  `prop:typeB-bridge-reduction`: a B2 ledger with nonnegative remaining core
  gives `N₀(X) ≥ 0`) and `typeBExclusionResidualRow` ([76]: a canonical support
  is negative, so its B2 ledger leaves a negative post-ledger core), then the
  mass row and the route-8 continuation [77]. This is the paper's topology; no
  deviation remains.

## [69]: routed local dichotomy on the heavy arm

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
  ports together with `TriangularPortsRoute` (`D_B ≥ (5k−19)/4`). Contract
  `Contracts.TypeB.heavyCentreRoutedAlternative`. The degree-four arm keeps the
  compatible-pair and fan-closed routing of `cor:degree-four-local-activation`.
  Paper-exact; no deviation remains.
