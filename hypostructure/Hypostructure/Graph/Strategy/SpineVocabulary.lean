import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.FiniteEdgeBudget
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.WindowRemainder
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.WedgeLowerBound
import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.OneThreeRepair
import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Core.CeilSqrt
import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.RemainderEntropy
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.ColdFirstFailure

/-!
# The minimum-degree cycle spine: fact vocabulary

The entry spine of a minimum-degree cycle problem proves a fixed sequence of
theorems about one selected minimal counterexample.  This module names them as
the closed semantic vocabulary of that residual domain, so each is a fact of
the one canonical `ExactLedger` rather than a payload, summary, or wrapper.

Nothing here is specialized to one manuscript.  The baseline threshold and the
accepted cycle-length predicate are parameters, so the same vocabulary serves
any minimum-degree cycle problem; a problem supplies its threshold through its
own presentation and never spells a numeral at a node.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

/-- **The registered data of a minimum-degree cycle spine.**

Every number the spine ever compares comes from this record, and a row is
forbidden to write one.  A problem supplies the record from its own
presentation; the manuscript's `3`, `13`, `399`, and window rate are its
values, not the framework's.

The one numeral that does appear below is the `3` of `three_le_threshold`, and
it is not a presentation constant: it is `⌈e⌉` from Stirling's bound
(`Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`), the constant that
makes the skeleton budget's `m !` pay for the density cap.  A presentation
whose baseline is below it does not reach node `[22]`. -/
structure Data where
  /-- The registered minimum-degree baseline `δ`. -/
  threshold : Nat
  /-- Stirling's `⌈e⌉` against the registered baseline; see the note above. -/
  three_le_threshold : 3 ≤ threshold
  /-- The accepted cycle lengths the counterexample must avoid. -/
  LengthOK : Nat → Prop
  /-- The order of the induced obstruction window.  For `thm:p13free` this is
  the induced-path order; nothing here knows its value. -/
  windowOrder : Nat
  windowOrder_pos : 0 < windowOrder
  /-- The cited external closure law.  An object meeting the baseline with no
  induced window of the registered order has an accepted cycle.  This is the
  only place a result outside the manuscript enters the spine, and it enters at
  the manuscript's own interface. -/
  freeForcesTarget : ∀ object : Graph.FiniteObject.{u},
    Graph.MinimumDegreeAtLeast threshold object →
    Graph.InducedPathFree object windowOrder →
    Graph.HasCycleWithLength LengthOK object
  /-- **`C_sp` of node `[19]`.**  The registered scale threshold is
  `C_sp·⌈√n⌉`; only its coefficient is registered, because the `⌈√n⌉` is the
  framework's own and the large-budget branch needs to *know* the threshold is a
  square-root scale in order to spend `σ(G) = O(√n) = o(n)` at node `[56]`. -/
  surplusScale : Nat
  /-- The registered per-window barrier rate of the finite enumeration. -/
  windowRate : Nat
  /-- The registered curvature rank allowance `o(W₂)` of node `[32]`, as a
  function of the wedge supply it is subtracted from.  Node `[32]` is the only
  comparison of the spine whose manuscript form still carries an asymptotic
  term after the exact substitutions of nodes `[29]`--`[30]`, so the allowance
  is registered here in the same way as the scale threshold of node `[19]`
  rather than written at the node. -/
  rankDefect : Nat → Nat
  /-- **`c_Ω`, node `[48]`'s registered curvature cost.**  The entropy price of
  one independent curvature coordinate, in the units the skeleton budget is
  measured in.  `rem:curvature-provenance` is explicit that the routing supplies
  the *independence* of the curvature cost, not its size, and that the value
  enters only through `K_win = c_Ω·ω_win` and `K = c_Ω·ω`; `rem:closure-robust`
  adds that the closure outside the explicit residuals does not use the exact
  value at all.  So it is a presentation constant, registered here. -/
  curvatureCost : Nat
  /-- **The `10` of node `[50]`.**  `prop:two-budget` splits on
  `η(R) ≥ (1/10)·log₂ n`, and the denominator is the proof's own threshold
  choice rather than anything measured on a graph.  Node `[50]` compares
  `n^{|R|}` against `|𝒢(R)|^d` at this `d`, so no logarithm or division is
  written. -/
  entropyDenominator : Nat
  entropyDenominator_pos : 0 < entropyDenominator
  /-- **The `4` of node `[58]`.**  `def:net-charge` is
  `N₀(X) = def⁺(X) − σ(X) − |V(X)|/s` at this discharge scale.  Every
  comparison of the charge is made after multiplying through by `s`, so the
  reciprocal never appears and nothing rounds. -/
  dischargeScale : Nat
  dischargeScale_pos : 0 < dischargeScale
  /-- **The manuscript's "for all sufficiently large `n`", as a binary
  exponent.**  `prop:negative-net-charge` is stated "for all sufficiently large
  `n`", and nodes `[55]`--`[56]` carry `+o(1)` on every display.  This is where
  that quantifier is registered, and node `[55]` decides the object's order
  against `2 ^ largeOrderExponent` with *both* arms retained — exactly the
  device node `[19]` already uses for its own registered `o(n)` threshold.  The
  small-order arm is the finite residue the manuscript does not address. -/
  largeOrderExponent : Nat
  largeOrderExponent_pos : 0 < largeOrderExponent
  /-- **`τ_win < ¼` at the registered rate.**

  `prop:p13-density` turns node `[24]`'s cap into `θ ≤ (δ/2)/rate + o(1)`, and
  `rem:closure-robust` records that `15θ_win/(1 − 13θ_win) = τ_win < ¼`.  The
  net-charge coefficient the collision needs is
  `A = s·(δ·order − 2(order−1)) + order` — the manuscript's `73` at its own
  values — and clearing denominators at the registered order exponent turns
  `τ_win < ¼` into exactly this comparison between registered numbers.

  Nothing about a graph occurs here: it is the presentation's own arithmetic,
  the analogue of `three_le_threshold`. -/
  netChargeRate :
    (dischargeScale * (threshold * windowOrder - 2 * (windowOrder - 1)) +
        windowOrder) * (largeOrderExponent + 1) * threshold <
      2 * windowRate * largeOrderExponent
  /-- **The registered order is past the surplus term's own square.**

  `σ(G) = O(√n)` is sublinear, so above some order it is below any positive
  share of the order.  This is where that order is registered, and it is stated
  in the registered numbers alone: four times the square of the coefficient the
  net-charge collision carries against the surplus.  `Data.surplusThreshold_sublinear`
  *derives* `σ(G) = o(n)` from it; nothing about the manuscript's decimal values
  is written anywhere. -/
  largeOrder_dominates_surplus :
    4 * (((dischargeScale * (threshold * windowOrder -
              2 * (windowOrder - 1)) + windowOrder) * (largeOrderExponent + 1) +
          2 * windowRate * largeOrderExponent * dischargeScale) *
        surplusScale) *
      (((dischargeScale * (threshold * windowOrder -
              2 * (windowOrder - 1)) + windowOrder) * (largeOrderExponent + 1) +
          2 * windowRate * largeOrderExponent * dischargeScale) *
        surplusScale) ≤
      2 ^ largeOrderExponent
  /-- **`def:declared-coordinate-signature`, registered.**  The fixed
  response-coordinate signature the whole proof argues against: the finite
  alphabets of its generating clauses (D1)--(D7), the label alphabet of its
  closure clause (D8), and the cut-state bound the local target algebra
  imposes.  `Q_cold` is `Fintype.card` of the cut-state this signature builds,
  so it is a constant of the signature and never of a graph. -/
  coldSignature : Graph.ColdCorridor.DeclaredSignature
  /-- The signature's window order is the spine's own registered window order:
  the cold-window offsets a corridor interface meets are the offsets of the
  same induced window every earlier node argued about. -/
  coldSignature_windowOrder : coldSignature.windowOrder = windowOrder

/-- **The registered scale threshold `C_sp·⌈√n⌉` of node `[19]`**, derived from
its coefficient and the framework's own ceiling square root.  Every node that
compared against `surplusThreshold` before still does; what has changed is that
the spine now knows the shape, which is what node `[56]` spends. -/
def Data.surplusThreshold (data : Data.{u}) (size : Nat) : Nat :=
  data.surplusScale * Core.ceilSqrt size

/-- **`A`, the net-charge coefficient of `cor:global-window-join-pressure`.**
`s·(δ·order − 2(order−1)) + order`, the manuscript's `73` at its own values.
No node writes it; it is read from the registered numbers. -/
def Data.netChargeCoefficient (data : Data.{u}) : Nat :=
  data.dischargeScale *
      (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) +
    data.windowOrder

/-- **`σ(G) = O(√n) = o(n)` at the registered order — derived.**

The registered scale threshold is `C_sp·⌈√n⌉`, and the registered order is past
the square of the coefficient the net-charge collision carries against it, so
above that order the surplus term is strictly below the margin the collision
leaves.  This is the exact-finite content of the manuscript's `σ(G) = o(n)`, and
it is a theorem of the registered numbers rather than one of them. -/
theorem Data.surplusThreshold_sublinear (data : Data.{u}) (size : Nat)
    (large : 2 ^ data.largeOrderExponent ≤ size) :
    (data.netChargeCoefficient * (data.largeOrderExponent + 1) +
          2 * data.windowRate * data.largeOrderExponent * data.dischargeScale) *
        data.surplusThreshold size <
      (2 * data.windowRate * data.largeOrderExponent -
          data.netChargeCoefficient * (data.largeOrderExponent + 1) *
            data.threshold) * size := by
  have rate := data.netChargeRate
  have dominatesSquare := data.largeOrder_dominates_surplus
  rw [show data.netChargeCoefficient =
      data.dischargeScale *
          (data.threshold * data.windowOrder -
            2 * (data.windowOrder - 1)) + data.windowOrder from rfl]
  set coefficient :=
    data.dischargeScale *
        (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) +
      data.windowOrder with coefficientDef
  set weight :=
    (coefficient * (data.largeOrderExponent + 1) +
      2 * data.windowRate * data.largeOrderExponent * data.dischargeScale) *
      data.surplusScale with weightDef
  set margin :=
    2 * data.windowRate * data.largeOrderExponent -
      coefficient * (data.largeOrderExponent + 1) *
        data.threshold with marginDef
  have marginPos : 0 < margin := by omega
  have square : 4 * weight * weight ≤ size := le_trans dominatesSquare large
  have sizePos : 0 < size :=
    Nat.lt_of_lt_of_le (Nat.two_pow_pos data.largeOrderExponent) large
  -- The framework's own `⌈√n⌉` bound, at twice the weight.
  have dominates : (2 * weight) * (2 * weight) ≤ margin * margin * size := by
    calc (2 * weight) * (2 * weight) = 4 * weight * weight := by ring
      _ ≤ size := square
      _ ≤ margin * margin * size :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos marginPos marginPos)
  have ceiling := Core.mul_ceilSqrt_le (2 * weight) margin size dominates
  have small : 2 * weight < margin * size := by
    rcases Nat.eq_zero_or_pos weight with zero | positive
    · rw [zero]
      simpa using Nat.mul_pos marginPos sizePos
    · have doubled : 2 * weight < 4 * weight * weight := by nlinarith
      have widened : size ≤ margin * size := Nat.le_mul_of_pos_left _ marginPos
      omega
  have regroup :
      (coefficient * (data.largeOrderExponent + 1) +
          2 * data.windowRate * data.largeOrderExponent * data.dischargeScale) *
          data.surplusThreshold size =
        weight * Core.ceilSqrt size := by
    rw [weightDef, Data.surplusThreshold]; ring
  have doubledCeiling : 2 * (weight * Core.ceilSqrt size) ≤
      margin * size + 2 * weight := by
    calc 2 * (weight * Core.ceilSqrt size)
        = (2 * weight) * Core.ceilSqrt size := by ring
      _ ≤ margin * size + 2 * weight := ceiling
  rw [regroup]
  omega

/-- The problem this spine argues about: a minimum-degree baseline at the
registered threshold, with the problem's own presentation attached. -/
abbrev problem (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Core.Problem.{u + 1, v} :=
  Graph.problemWithPresentation (Graph.MinimumDegreeAtLeast data.threshold)
    BranchState Presentation presentation

/-- The registered progress order: vertex count, then edge count. -/
abbrev progress (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Core.Progress.{u + 1, v, 0}
      (problem BranchState Presentation presentation data) :=
  (Graph.CanonicalProgress.progress
    (P := problem BranchState Presentation presentation data))

/-- The semantic facts the entry spine proves.

Each constructor is one manuscript statement.  A key determines exactly one
value schema, so two unrelated facts cannot impersonate one another. -/
inductive Key where
  /-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
  strictly smaller baseline object does not. -/
  | selection
  /-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
  accepted set at every oriented edge.  This is the return-set form of target
  avoidance, the standing invariant the rest of the spine consumes. -/
  | returnAvoidance
  /-- Node `[8]`: no proper subgraph satisfies the baseline. -/
  | noProperBaseline
  /-- Node `[9]`: every oriented edge has an endpoint exactly at the
  threshold. -/
  | tightEndpoint
  /-- Node `[10]`: vertices strictly above the threshold are pairwise
  nonadjacent. -/
  | slackIndependent
  /-- Nodes `[11]`--`[14]`: no proper atom admits a nontrivial target-complete
  compression (`cor:uncompressible`). -/
  | uncompressible
  /-- Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family
  of induced windows, and the family is nonempty. -/
  | maximalPacking
  /-- Node `[18]`: the local label algebra of the registered window order is
  exactly enumerated and its curvature relation is decided (`lem:labels`). -/
  | localAlgebra
  /-- Node `[19]`, above arm: the degree surplus exceeds the registered scale
  threshold. -/
  | surplusAbove
  /-- Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite
  form. -/
  | surplusAtOrBelow
  /-- Node `[21]`, cap arm: the packing's entropy demand fits inside the
  labelled skeleton budget, which is itself stable under a variable edge
  count. -/
  | barrierCap
  /-- Node `[21]`, overflow arm: the demand exceeds the budget. -/
  | barrierOverflow
  /-- Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing
  in the object's own dyadic scale. -/
  | densityCap
  /-- Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no
  window and no subgraph meeting the baseline (`sec:remainder`). -/
  | remainderNormalized
  /-- Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by
  its boundary incidences (`lem:surplus-aware-window-stub`). -/
  | boundaryDemand
  /-- Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the
  object's own surplus and the registered near-cubic threshold spent against it.
  This is the manuscript's *supply ceiling* of the final collision. -/
  | stubSupply
  /-- Node `[30]`, the lemma proper: every region of the remainder meets the
  baseline out of its own internal wedge supply and twice its own positive
  deficiency (`lem:wedge-lower`). -/
  | wedgeSupply
  /-- Node `[30]`, the demand floor it is stated for: the wedge lower bound
  with the boundary-demand ceiling substituted for the deficiency.  This is
  invariant 28, the demand side of the final collision. -/
  | curvatureDemandFloor
  /-- Node `[31]`: the curvature target-rank of the remainder is attained by a
  subfamily of raw internal curvature tests that survives every functional
  admissible rank quotient, and every test outside that subfamily is
  target-dependent on it (`def:curvature-target-rank`,
  `lem:target-rank-circuit`). -/
  | curvatureTargetRank
  /-- Node `[32]`, yes arm: `r_Ω(R) < W₂(R) − o(W₂)` for some admissible
  quotient system, together with the proper target-dependence the rank drop
  yields.  This is node `[33]`, Branch D. -/
  | curvatureRankDrop
  /-- Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible
  quotient system.  This is node `[34]`, Residual B. -/
  | curvatureFullRank
  /-- Nodes `[33]` and `[35]`: Branch D, entered with the determination
  certificate.  `lem:target-rank-circuit` turns the rank drop into a proper
  target-dependence, and `lem:curvature-dependence-routing` opens its proof by
  choosing a certificate for that dependence: an admissible rank quotient on a
  connected determination support, rank-reducing on the raw curvature tests.
  That certificate is the object nodes `[36]`, `[38]` and `[40]` route. -/
  | branchDependence
  /-- Node `[36]`, yes arm: the determination the certificate makes is valid
  against every outside context, and the states it identifies lie in one
  boundary-degree fibre (`lem:context-universality`,
  `lem:degree-profile-fibres`).  This is the residual node `[38]` consumes. -/
  | contextUniversal
  /-- Node `[36]`, no arm — the terminal `[37]`: some pair of states the
  certificate identifies is separated, either by an outside context or already
  by its boundary-degree profile.  This is case (i) of
  `lem:curvature-dependence-routing`, a target-defective quotient. -/
  | contextDefect
  /-- Node `[38]`, yes arm — the terminal `[39]`: the context-universal
  determination is already certified inside the proper atom `C`, so the
  quotient is a target-complete rank-reducing quotient of `C` and
  `def:admissible-rank-quotient` supplies a strictly smaller proper
  representative.  This is case (ii), proper atom compression. -/
  | atomCompression
  /-- Node `[40]`: the determination is certified only after adjoining
  structure outside `C`, so the connected support it needs strictly contains
  `C`.  This is case (iii)'s entry. -/
  | delocalizedSupport
  /-- Node `[41]`, yes arm — the terminal `[42]`: the enlarged support is still
  proper in `G`.  `lem:proper-smearing`: a proper boundaried support carrying
  the dependence is a target defect or a target-complete compression, and both
  are excluded at a minimal counterexample. -/
  | properDelocalization
  /-- Node `[43]`: the enlarged support is the whole graph, so the dependence
  delocalizes globally and the quotient is a closed exact-profile quotient. -/
  | globalDelocalization
  /-- Node `[44]`: `lem:smearing-support-repair`'s identity
  `s = p − 2 + 2β − σ` for a delayed compensation component of the
  delocalization support, at every `1`--`3` repair network up to surplus. -/
  | repairIdentity
  /-- Node `[45]`: the global profile barrier `lem:no-silent-global-smearing`
  raises against a whole-graph dependence — the closed clause of
  `def:admissible-rank-quotient` yields either a proper-support replacement or
  a strictly smaller admissible closed representative. -/
  | globalBarrier
  /-- Nodes `[145]`--`[157]`, the corridor cut-state `T(J)`
  (`def:cold-corridor-first-failure`).  The cold corridor state retains exactly
  the four items that definition names, and retaining them is enough: two
  segments with equal states agree at *every* declared coordinate supported in
  the active interface, derived (D8) ones included.  Reading `Q_cold + 1`
  states therefore forces a repeat, which is the pigeonhole the repeat subcase
  of (F5) is entered by. -/
  | coldCorridorState
  /-- Nodes `[145]`--`[157]`, the same-interface table.  Every row of
  `def:cold-same-interface-table` is routed to an already closed outcome
  (`lem:cold-same-interface-table`), so no equal-length cold bounded germ is a
  terminal cold residual; and a short self-return whose smear interval meets an
  accepted length realizes it (`lem:cold-short-self-return-filter`). -/
  | coldSameInterfaceTable
  /-- Node `[155]`, G1 of `lem:cold-bounded-germ-trichotomy`.  A cold bounded
  germ whose own compatible completion realizes the target would hand the
  selected object the target it avoids, so no germ is *hit-realized*; and the
  three cases G1, G2, G3 of the trichotomy are exhaustive, which is what makes
  the routing of the remaining two an exhaustive routing. -/
  | coldGermRealized
  /-- Node `[156]`, G2 of `lem:cold-bounded-germ-trichotomy`.  A germ some
  compatible outside context *distinguishes* identifies its two representatives
  target-defectively: `lem:context-universality` denies target-completeness of
  that identification in every immutable profile fibre, which is the routing to
  the sparse exit or the exit-(4) ledger. -/
  | coldGermDistinguished
  /-- Node `[157]`, G3 of `lem:cold-bounded-germ-trichotomy` with
  `lem:cold-increment-arithmetic`.  A *silent* length-changing germ would be a
  target-complete compression of its own proper support, which node `[14]`
  excludes; and the finite arithmetic of the increment `δ` -- the overlapping
  blocks of case (a), the doubling-orbit hit of case (b), the order criterion
  forcing it, the transient of an even modulus, and case (d)'s equal-length
  switch -- decides which of the three arms a germ falls into. -/
  | coldGermSilent
  /-- Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.  The full-rank residual
  pays `c_Ω·r_Ω(R) ≥ K_win|R| − o(|R|)`, which is the wedge demand floor of node
  `[30]` with node `[34]`'s rank substituted for its wedge supply and the
  registered cost applied to both sides. -/
  | forcedCurvatureCost
  /-- Node `[50]`, yes arm — node `[51]`, the high-entropy remainder branch:
  `η(R) ≥ (1/d)·log₂ n`, i.e. the remainder's realized target-complete states
  number at least `n^{|R|/d}` (`prop:two-budget` (a)). -/
  | remainderEntropyHigh
  /-- Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch
  `prop:two-budget` (b) and (c) share. -/
  | remainderEntropyLow
  /-- Node `[52]`: the window package and the remainder accounting, joined.
  `eq:feasibility`'s left-hand side in exact integer form — the joint
  window/remainder/curvature coordinate family realizes at least
  `2^{rate·p}·n^{|R|/d}·2^{c_Ω·r_Ω(R)}` states. -/
  | entropyPackageDemand
  /-- Node `[53]`, yes arm — the terminal `[54]`: the remaining non-curvature
  budget is strictly smaller than the forced curvature cost, so the joint
  package overflows the labelled skeleton budget (`eq:entropy-cap`,
  `prop:entropy-high-theta`). -/
  | entropyCapActive
  /-- Node `[53]`, no arm — node `[55]`, Residual C: the joint package still
  fits the skeleton budget, and the branch is the large-budget residual. -/
  | largeBudgetResidual
  /-- Node `[55]`, large arm: the object's order is at or above the registered
  one.  This is the manuscript's "for all sufficiently large `n`", made
  explicit. -/
  | largeOrderResidual
  /-- Node `[55]`, small arm: the finite residue below the registered order,
  which the manuscript's asymptotic statements do not address. -/
  | smallOrderResidual
  /-- Node `[56]`: `Δ_net(R) = (def⁺(R) − σ_R)/|R| ≤ τ_win + o(1) < ¼`, in the
  exact integer form node `[59]` collides with — node `[29]`'s stub ceiling and
  node `[24]`'s density cap at the registered discharge scale, with the packing
  eliminated through `|R| + order·p = n`.  Below the quarter, `N₀(R) < 0`, so
  the whole remainder already has negative net charge. -/
  | netDeficiencyCap
  /-- Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.  The
  canonical support decomposition is exact on all three of the charge's terms,
  so a remainder of negative net charge has a *connected* admissible support of
  negative net charge. -/
  | netChargeLocalization
  /-- Node `[59]`, yes arm: `N₀(R) ≥ 0`. -/
  | netChargeNonNegative
  /-- Node `[59]`, no arm: `N₀(R) < 0`. -/
  | netChargeNegative
  /-- Node `[60]`: `cor:global-window-join-pressure`.  On the arm where no
  negative support appears, the window surplus must exceed the remainder
  surplus by a linear amount, `σ_W − σ_R ≥ (n − 73p₁₃)/4` at the manuscript's
  own values. -/
  | windowJoinPressure
  /-- Node `[61]`: `prop:negative-net-charge`.  A connected admissible support
  of the remainder carries negative net charge. -/
  | negativeSupport
  /-- Node `[62]`, no arm — node `[63]`, Type A: the selected negative support
  carries no assigned high-degree surplus. -/
  | typeALowSurplus
  /-- Node `[62]`, yes arm — node `[64]`, Type B: the selected negative support
  carries assigned high-degree surplus. -/
  | typeBHighSurplus
  /-- Nodes `[154]`, `[155]`, the (F1) producer.  A compatible completion
  through a cold-window offset that realizes a power-of-two cycle would be an
  accepted cycle of the selected object, which node `[1]` excludes: (F1) never
  occurs on this branch (`lem:cold-corridor-first-failure` (i)). -/
  | coldFailureCycle
  /-- Nodes `[154]`, `[156]`, the (F2) producer.  Two prefixes with the same
  cold corridor state but different target response against some compatible
  outside context identify target-defectively -- `lem:context-universality` --
  and with the discrepancy excluded they are context-equivalent
  (`lem:cold-corridor-first-failure` (ii)). -/
  | coldFailureDefect
  /-- Nodes `[154]`, `[157]`, the (F3) producer.  A named earlier prefix whose
  own piece is a strictly smaller proper representative of a later one is a
  target-complete compression of a proper support, which node `[14]` excludes:
  (F3) never occurs (`lem:cold-corridor-first-failure` (iii)). -/
  | coldFailureCompression
  /-- Nodes `[154]`, `[156]`, the (F4) producer and its handoff exit.  A
  corridor that first enters the declared handoff interfaces recorded in the
  branch state reaches *precisely one* of them, and the charge transfers to that
  already existing ledger (`lem:cold-corridor-first-failure` (iv)). -/
  | coldFailureHandoff
  /-- Node `[154]`, the classified state.  Every cold return corridor has a
  first failure: either it reaches its successor stub inside `Q_cold` states, or
  `Q_cold + 1` states are read and two are equal.  With it, the hot/cold ledger
  split of `def:cold-window-ledger` and the branch-excess count of
  `def:cold-skeleton-excess`/`lem:cold-window-stub-excess`
  (`lem:cold-corridor-first-failure`, existence half). -/
  | coldFailureRouting
  deriving DecidableEq

/-- **`𝒲₂(R)`**: the raw internal length-two curvature tests carried by the
remainder a packing leaves.  This is the family whose rank
`def:curvature-target-rank` takes, and `internalWedgeFamily_card` says it has
exactly `W₂(R)` members. -/
noncomputable abbrev remainderCurvatureTests (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Finset (object.InternalWedge (object.remainderSupport packing)) :=
  object.internalWedgeFamily (object.remainderSupport packing)

/-- **The admissible quotient system `def:curvature-target-rank` computes
against**, at the remainder and at the spine's registered baseline and accepted
cycle lengths.  It is the manuscript's own system —
`Graph.FiniteObject.curvatureQuotientSystem` — not a parameter and not a
supplied field: a member is a target-complete quotient of the exact response
profile of a connected determination support carrying `𝒲₂(R)`, functional on
that family, and representable as its scope requires. -/
noncomputable abbrev remainderQuotientSystem (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Core.TargetRank.QuotientSystem
      (object.InternalWedge (object.remainderSupport packing))
      (remainderCurvatureTests object packing) :=
  object.curvatureQuotientSystem (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) (object.remainderSupport packing)

/-- **`r_Ω(R)`**: the curvature target-rank of the remainder. -/
noncomputable abbrev remainderCurvatureTargetRank (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  object.curvatureTargetRank (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) (object.remainderSupport packing)

/-- **An admissible rank quotient of the remainder**, in the manuscript's own
sense: `Graph.CurvatureQuotient` is `def:admissible-rank-quotient` at the raw
curvature tests, carrying its connected determination support, the
target-completeness clauses of `def:target-complete-quotient`, and the two
representative clauses its scope requires.  A determination certificate of
`def:curvature-target-dependence` is one of these together with the
rank-reduction it performs. -/
abbrev remainderQuotient (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Type (u + 2) :=
  Graph.CurvatureQuotient (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object
    (object.remainderSupport packing)

/-- **A determination certificate of `def:curvature-target-dependence`**, at the
remainder a packing leaves.

The definition's tuple is `𝔠 = (X, T, q, 𝒫)`, and each clause is here:

* (a) `X` is a connected `T`-boundaried support carrying the coordinates.  That
  is the quotient's own `support`, `connected` and `carries`, and `T` is the
  support's own cut interface, which is why no boundary is a parameter.
* (b) `q` is a functional admissible rank quotient of the exact response profile
  of `X`.  That is `remainderQuotient`, a member of the manuscript's own system.
* (c) the `q`-value of `a` is a function of the `q`-value vector on `ℬ`.  That
  is `Determines`, together with the properness clause `a ∉ ℬ`.
* (d) `𝒫`, the finite declared support data, is carried by `carries`: the
  support already contains the declared support of every coordinate under
  discussion, which is what the certificate records `𝒫` for.

The rank reduction is the drop Branch D was entered on: the certificate is the
quotient that loses label-injectivity on `𝒲₂(R)`. -/
def DeterminationCertificate (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (quotient : remainderQuotient data object packing) : Prop :=
  ¬ Set.InjOn quotient.label ↑(remainderCurvatureTests object packing) ∧
    ∃ test ∈ remainderCurvatureTests object packing,
      ∃ determiners ⊆ (↑(remainderCurvatureTests object packing) : Set _),
        test ∉ determiners ∧
          quotient.toRankQuotient.Determines test determiners

/-- **`Z`, the connected support the determination actually needs.**

`lem:curvature-dependence-routing` compares the certificate's support with the
atom `C` whose curvature tests it determines: the determination either holds
"already with support `C`", or "only once additional structure outside `C` is
adjoined", in which case an inclusion-minimal connected such support is `Z ⊋ C`.
`Z` is the certificate's own support together with `C`, so it contains `C` by
construction and strictly contains it exactly when the certificate reaches
outside.  Node `[41]` then compares `Z` with `G`. -/
noncomputable def delocalizationSupport (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (quotient : remainderQuotient data object packing) :
    Finset object.Vertex := by
  classical
  exact quotient.support ∪ object.remainderSupport packing

theorem remainderSupport_subset_delocalizationSupport (data : Data.{u})
    {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing) :
    object.remainderSupport packing ⊆
      delocalizationSupport data object packing quotient := by
  classical
  intro vertex member
  simp [delocalizationSupport, member]

/-- **`Z ⊋ C` exactly when the certificate reaches outside `C`**, which is the
alternative node `[38]` sends to node `[40]`. -/
theorem remainderSupport_ssubset_delocalizationSupport (data : Data.{u})
    {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing)
    (outside : ¬ quotient.support ⊆ object.remainderSupport packing) :
    object.remainderSupport packing ⊂
      delocalizationSupport data object packing quotient := by
  classical
  refine ⟨remainderSupport_subset_delocalizationSupport data quotient,
    fun contained => outside fun vertex member => ?_⟩
  exact contained (by simp [delocalizationSupport, member])

/-- **The realizations a quotient identifies.**  `def:target-complete-quotient`
governs exactly the pairs of `T`-boundaried states that carry the same quotient
datum, which here is the same value at every declared raw curvature test. -/
def Identified {data : Data.{u}} {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        quotient.support)) : Prop :=
  ∀ test ∈ remainderCurvatureTests object packing,
    quotient.value left (quotient.label test) =
      quotient.value right (quotient.label test)

/-- **The determination a quotient certifies is target-complete.**

Both clauses of `def:target-complete-quotient` at the quotient's own boundaried
states: identified states lie in one boundary-degree fibre
(`lem:degree-profile-fibres`) and no outside context separates them
(`lem:context-universality`).  Node `[36]`'s yes arm commits this of every
quotient on the remainder; nodes `[38]`, `[41]` and `[43]` carry it on the
certificate they route, because the manuscript's cases (ii) and (iii) are about
a *target-complete* rank-reducing quotient and not merely a rank-reducing
one. -/
def TargetCompleteAt (data : Data.{u}) {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing) : Prop :=
  ∀ left right, Identified quotient left right →
    left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
      Graph.Response.ContextEquivalent
        (Graph.HasCycleWithLength data.LengthOK) left right

/-- **`W₂(R)`**, and the allowance node `[32]` subtracts from it. -/
noncomputable abbrev remainderWedgeSupply (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  object.internalWedgeCount (object.remainderSupport packing)

/-- **`|𝒢(R)|`** of `def:remainder-entropy`, at the remainder a packing leaves:
the labelled simple graphs on `V(R)` carrying the constraints node `[27]` has
already imposed on the branch — window-freeness at the registered order, and no
subregion meeting the registered baseline.  It is the *only* thing the entropy
definition consumes; no enumeration is prescribed. -/
noncomputable abbrev remainderStates (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  Graph.remainderStateCount data.windowOrder data.threshold
    (object.remainderSupport packing).card

/-- **The joint package demand of nodes `[52]`--`[53]`.**  The window
coordinates of `lem:p13-window-package`, the remainder states of
`def:remainder-entropy`, and the forced curvature coordinates of
`cor:forced-curvature-cost`, multiplied: the number of target-complete states
the branch has to distinguish.  `eq:entropy-cap` compares exactly this against
the labelled skeleton budget. -/
noncomputable abbrev jointPackageDemand (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  2 ^ (data.windowRate * Graph.dyadicScaleCount object * packing.card) *
      remainderStates data object packing *
    2 ^ (data.curvatureCost *
      remainderCurvatureTargetRank data object packing)

/-- The value schema of each spine fact, stated of the *object* alone.

Every spine fact is a statement about the selected graph, never about the
branch state carried beside it.  Making that explicit is what lets a fact
transport along a refinement by a rewrite: refinement is object equality.

`localAlgebra` is the one clause that does not mention the object: the window
algebra is a property of the registered order, and saying so is what makes it
transport for free. -/
def Holds (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Key → Graph.FiniteObject.{u} → Prop
  | .selection, object =>
      (¬ Graph.HasCycleWithLength data.LengthOK object ∧
        ∀ smaller : Graph.FiniteObject.{u},
          (progress BranchState Presentation presentation data).Smaller
            smaller object →
          Graph.MinimumDegreeAtLeast data.threshold smaller →
          Graph.HasCycleWithLength data.LengthOK smaller)
  | .returnAvoidance, object =>
      (∀ dart : object.graph.Dart,
        Disjoint (Graph.returnLengthSet object dart)
          (Graph.shiftedAcceptedSet data.LengthOK))
  | .noProperBaseline, object =>
      (∀ subgraph : Graph.ProperSubgraph object,
        ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value)
  | .tightEndpoint, object =>
      (∀ dart : object.graph.Dart,
        object.degree dart.fst = data.threshold ∨
          object.degree dart.snd = data.threshold)
  | .slackIndependent, object =>
      (∀ left right : object.Vertex,
        data.threshold < object.degree left →
        data.threshold < object.degree right →
        ¬ object.graph.Adj left right)
  | .uncompressible, object =>
      (∀ support : Finset object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object support)
  | .maximalPacking, object =>
      (0 < object.windowPackingNumber data.windowOrder ∧
        ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            ∀ support : Finset object.Vertex,
              object.InducesWindow data.windowOrder support →
              ∃ member ∈ packing, ¬ Disjoint support member)
  | .localAlgebra, _object =>
      ((Graph.WindowCurvature.legalCodeList data.windowOrder).length =
          (Graph.WindowCurvature.Labels data.windowOrder).card ∧
        ∀ source middle target : Graph.WindowCurvature.Label data.windowOrder,
          Graph.WindowCurvature.curvatureTwo source middle target = true ↔
            Graph.WindowCurvature.Safe 1 source middle ∧
              Graph.WindowCurvature.Safe 1 middle target ∧
              ¬ Graph.WindowCurvature.Safe 2 source target)
  | .surplusAbove, object =>
      (data.surplusThreshold object.vertexCount <
        object.degreeSurplus data.threshold)
  | .surplusAtOrBelow, object =>
      (object.degreeSurplus data.threshold ≤
        data.surplusThreshold object.vertexCount)
  | .barrierCap, object =>
      -- `lem:p13-window-package`.  The registered rate is a per-window cost
      -- *per dyadic scale* -- that is what `windowRate`'s provenance and
      -- `dyadicScaleCount`'s own docstring both say -- so the package the
      -- packing demands is `rate · (number of scales) · p` bits, the
      -- manuscript's `c₁₃ p₁₃ log₂ n`.  Dropping the scale factor would state a
      -- demand that grows a whole `log₂ n` slower than the manuscript's, and
      -- node `[24]` would then cap nothing.
      (2 ^ (data.windowRate * Graph.dyadicScaleCount object *
            object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget object ∧
        ∀ family : Finset Nat, object.edgeCount ∈ family →
          Graph.skeletonBudget object ≤
            Graph.variableEdgeBudget object.vertexCount family)
  | .barrierOverflow, object =>
      (Graph.skeletonBudget object <
        2 ^ (data.windowRate * Graph.dyadicScaleCount object *
          object.windowPackingNumber data.windowOrder))
  | .densityCap, object =>
      -- `prop:p13-density`.  Spending the skeleton budget's `m !` against the
      -- packed demand leaves `2·rate·scaleCount·p ≤ (scaleCount + 1)(δn + T(n))`,
      -- whose asymptotic form is exactly `θ ≤ (δ/2)/rate + o(1)`, the
      -- manuscript's `θ_win = 1.5/118.108581006…`.  The `o(1)` is the
      -- `(scaleCount + 1)/scaleCount` factor and the `T(n)` term; both are
      -- exact here.
      (2 * (data.windowRate * Graph.dyadicScaleCount object *
          object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount object + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount))
  | .remainderNormalized, object =>
      -- Quantified over every maximal packing, so no family has to travel from
      -- the row that produced one: the statement is about all of them.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ support : Finset object.Vertex,
          support ⊆ object.remainderSupport packing →
          ¬ object.InducesWindow data.windowOrder support ∧
            ¬ Graph.MinimumDegreeAtLeast data.threshold
              (object.induce support))
  | .boundaryDemand, object =>
      -- `lem:surplus-aware-window-stub`, the manuscript's chain
      --   `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`,
      -- both links kept: the first is invariant 24's demand, the second is
      -- invariant 23's window stub capacity, which is about the cut alone.  At
      -- the registered presentation the second reads `e(R,W) ≤ 15p₁₃ + σ_W`.
      -- No near-cubic hypothesis, and the statement holds at every packing, so
      -- none travels.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.positiveDeficiency (object.remainderSupport packing)
              data.threshold ≤
            object.boundaryIncidence (object.remainderSupport packing) ∧
          object.boundaryIncidence (object.remainderSupport packing) +
              2 * (data.windowOrder - 1) * packing.card ≤
            data.threshold * (data.windowOrder * packing.card) +
              object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
                data.threshold)
  | .stubSupply, object =>
      -- `lem:stub-positive`, exactly: the same chain with the object's own
      -- surplus in place of the windows', `def⁺(R) ≤ 15p₁₃ + σ(G)`, and then
      -- the registered near-cubic ceiling `σ(G) ≤ T(n)` spent against it.  The
      -- manuscript spends `σ(G) = O(√n) = o(n)` here and writes
      -- `def⁺(R) ≤ 15p₁₃ + o(n)`; `T` is the spine's exact `o(n)`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.positiveDeficiency (object.remainderSupport packing)
              data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            data.surplusThreshold object.vertexCount)
  | .wedgeSupply, object =>
      -- `lem:wedge-lower`, subtraction-free: `δ·|X| ≤ W₂(X) + 2·def⁺(X)`.
      -- Stated at every region of the remainder, which is both of the lemma's
      -- displayed inequalities at once: the componentwise bound at a component
      -- of `R`, and its sum over the components at `R` itself.  Quantified over
      -- every maximal packing, so none has to travel.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ support : Finset object.Vertex,
          support ⊆ object.remainderSupport packing →
          data.threshold * support.card ≤
            object.internalWedgeCount support +
              2 * object.positiveDeficiency support data.threshold)
  | .curvatureDemandFloor, object =>
      -- The lemma's "in particular", with the exact boundary-demand ceiling in
      -- place of the manuscript's asymptotic one.  The two doubled terms are
      -- literally twice the two sides of `boundaryDemand`, substituted for the
      -- `2·def⁺(R)` of the wedge bound:
      --   `δ|R| + 2·(2(order−1)p) ≤ W₂(R) + 2·(δ·order·p + σ_W)`,
      -- i.e. `W₂(R) ≥ δ|R| − 2((δ·order − 2(order−1))p + σ_W)`, which at the
      -- registered presentation is `W₂(R) ≥ 3|R| − 2(15p₁₃ + σ_W)`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        data.threshold * (object.remainderSupport packing).card +
              2 * (2 * (data.windowOrder - 1) * packing.card) ≤
            object.internalWedgeCount (object.remainderSupport packing) +
              2 * (data.threshold * (data.windowOrder * packing.card) +
                object.ambientSurplus
                  (Graph.FiniteObject.windowSupport packing) data.threshold))
  | .curvatureTargetRank, object =>
      -- `def:curvature-target-rank` with `lem:target-rank-circuit`.  `r_Ω(R)`
      -- is attained by a subfamily of `𝒲₂(R)` surviving every functional
      -- admissible rank quotient, and every raw test outside it is
      -- target-dependent on a subfamily of it.  Stated at every packing, so
      -- none travels; the quotient system is the manuscript's own.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∃ independent ⊆ remainderCurvatureTests object packing,
          (remainderQuotientSystem data object packing).Survives ↑independent ∧
            independent.card =
              remainderCurvatureTargetRank data object packing ∧
            ∀ test ∈ remainderCurvatureTests object packing,
              test ∉ independent →
              ∃ determiners ⊆ (↑independent : Set _),
                Core.TargetRank.Dependence
                  (remainderQuotientSystem data object packing) test determiners)
  | .curvatureRankDrop, object =>
      -- Node `[32]`, yes: `r_Ω(R) < W₂(R) − o(W₂)`, with the proper
      -- target-dependence the drop yields.  This is node `[33]`, Branch D.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          remainderCurvatureTargetRank data object packing <
              remainderWedgeSupply object packing -
                data.rankDefect (remainderWedgeSupply object packing) ∧
            ∃ test determiners,
              Core.TargetRank.Dependence
                (remainderQuotientSystem data object packing) test determiners)
  | .curvatureFullRank, object =>
      -- Node `[32]`, no: `r_Ω(R) ≥ W₂(R) − o(W₂)`.  This is node `[34]`,
      -- Residual B, the residual `lem:full-rank` is stated on at node `[47]`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        remainderWedgeSupply object packing -
            data.rankDefect (remainderWedgeSupply object packing) ≤
          remainderCurvatureTargetRank data object packing)
  | .branchDependence, object =>
      -- Nodes `[33]`/`[35]`.  `lem:curvature-dependence-routing`'s proof opens
      -- by choosing a determination certificate for the dependence the rank
      -- drop yields; clause (b) of `def:curvature-target-dependence` says its
      -- quotient is a functional admissible rank quotient, and the drop is
      -- exactly the rank reduction that quotient performs on `𝒲₂(R)`.  Clause
      -- (a) -- the connected support carrying the coordinates -- is the
      -- quotient's own `support`, `connected` and `carries`.  Branch D is a
      -- rank-reducing curvature *dependence*, so the determined coordinate `a`
      -- and its determiners `ℬ` travel with the certificate: that is clause
      -- (c), and `DeterminationCertificate` carries all four clauses.  The
      -- certificate is chosen with *inclusion-minimal* connected support, as
      -- the proof says and as `def:curvature-target-dependence`'s minimality
      -- clause means: no proper subsupport carries a determination certificate.
      -- `[40]` is where that minimality is spent, so it is fixed here, at the
      -- entry, and not re-chosen later.  Two readings of that clause differ and
      -- the stronger one is what gets proved: the definition says "no proper
      -- connected subsupport carries a proper target-dependence *with the same
      -- determined coordinate*", and the choice made here -- a support of
      -- minimum size among all that carry any determination certificate --
      -- rules out every determined coordinate at once.  Connectedness is not a
      -- separate clause either: a subsupport carrying a certificate carries a
      -- `remainderQuotient`, whose `connected` field is that hypothesis.

      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              ∀ smaller : Finset object.Vertex, smaller ⊂ quotient.support →
                ∀ narrower : remainderQuotient data object packing,
                  narrower.support = smaller →
                  ¬ DeterminationCertificate data object packing narrower)
  | .contextUniversal, object =>
      -- Node `[36]`, yes: the determination is target-complete.  Both clauses
      -- of `def:target-complete-quotient` at the certificate's own boundaried
      -- states -- `lem:degree-profile-fibres` for the fibre and
      -- `lem:context-universality` for the all-context response -- because that
      -- conjunction is the eligibility test the manuscript branches on, and it
      -- is what `[38]` asks about a smaller proper representative.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ quotient : remainderQuotient data object packing,
          TargetCompleteAt data quotient)
  | .contextDefect, object =>
      -- Node `[36]`, no -- the terminal `[37]`, "target-defective quotient":
      -- the exact negation of the clause above, with the separating witness
      -- exhibited.  Both ways of failing are target-defective, and the
      -- manuscript says so of each: `def:target-complete-quotient` calls an
      -- identification failing the context-universal test target-defective, and
      -- the sparse-exit routing writes "a non-fibrewise quotient is
      -- target-defective" of the other.  Invariant 6 is attributed to `[36]`
      -- *and* `[37]` with failure mode "otherwise target-defective", which is
      -- the same statement in the manuscript's own bookkeeping.  So the
      -- terminal admits both, and neither is a third alternative: they are the
      -- two halves of one negation.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            ∃ left right, Identified quotient left right ∧
              (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
                Graph.Response.TargetDefect
                  (Graph.HasCycleWithLength data.LengthOK) left right))
  | .atomCompression, object =>
      -- Node `[38]` yes, the terminal `[39]`: the determination is certified
      -- without leaving `C`, which is case (ii) -- "it holds for every outside
      -- context already with support `C`".
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              TargetCompleteAt data quotient ∧
                quotient.support ⊆ object.remainderSupport packing)
  | .delocalizedSupport, object =>
      -- Node `[40]`: case (iii)'s entry.  The certificate reaches outside `C`,
      -- so the connected support the determination needs strictly contains it.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ object.remainderSupport packing ∧
                  object.remainderSupport packing ⊂
                    delocalizationSupport data object packing quotient)
  | .properDelocalization, object =>
      -- Node `[41]` yes, the terminal `[42]`: `Z ⊊ G`.  `lem:proper-smearing`
      -- is stated exactly under this hypothesis.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ object.remainderSupport packing ∧
                  ∃ vertex,
                    vertex ∉ delocalizationSupport data object packing quotient)
  | .globalDelocalization, object =>
      -- Node `[43]`: `Z = G`.  The quotient is then a closed exact-profile
      -- quotient, which is the hypothesis of `lem:no-silent-global-smearing`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ object.remainderSupport packing ∧
                  ∀ vertex,
                    vertex ∈ delocalizationSupport data object packing quotient)
  | .repairIdentity, _object =>
      -- Node `[44]`, `lem:smearing-support-repair`: a delayed compensation
      -- component with `p` boundary leaves, `s` internal vertices, cycle rank
      -- `β` and surplus `σ` satisfies `s = p − 2 + 2β − σ`.  Like the window
      -- algebra of node `[18]`, the statement is about the class of such
      -- components and not about the selected object, which is what makes it
      -- transport for free.
      (∀ component : Graph.OneThreeRepair.Component.{u},
        (component.internal.card : Int) =
          component.boundary.card - 2 + 2 * component.cycleRank -
            component.surplus)
  | .globalBarrier, object =>
      -- Node `[45]`: the barrier `lem:no-silent-global-smearing` raises.  The
      -- closed clause of `def:admissible-rank-quotient` leaves exactly two
      -- readings of a rank-reducing whole-graph quotient, and node `[46]` is
      -- that both are impossible in the selected minimal counterexample.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            DeterminationCertificate data object packing quotient ∧
              (Graph.Strategy.InterfaceReplacement.ReplacementSupport
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object
                  quotient.support ∨
                ∃ representative : Graph.FiniteObject.{u},
                  representative.LexicographicallySmaller object ∧
                    Graph.MinimumDegreeAtLeast data.threshold representative ∧
                      (Graph.HasCycleWithLength data.LengthOK representative →
                        Graph.HasCycleWithLength data.LengthOK object)))
  | .coldCorridorState, object =>
      -- `def:cold-corridor-first-failure`, the cut-state clauses.  Stated at
      -- every presentation of the object's corridor segments, so no corridor
      -- construction travels with the fact: what is committed is that the
      -- retained state is *complete* and that it is *bounded*.
      --
      -- The first clause is the manuscript's "after excluding (F2), equality of
      -- cold corridor states is equality for every target-response coordinate
      -- used by the local replacement" -- and it holds at every declared
      -- coordinate of `def:declared-coordinate-signature`, derived (D8) ones
      -- included, although the state retains only the generating ones.
      --
      -- The second is "the set of possible cold corridor states is bounded by a
      -- constant `Q_cold` depending only on the fixed declared signature":
      -- `Q_cold + 1` segments cannot have pairwise distinct states.  That is the
      -- pigeonhole `lem:cold-corridor-first-failure` reaches the repeat subcase
      -- of (F5) by.
      --
      -- The third is the sentence the second half of the paragraph draws:
      -- "if two prefixes have the same finite cut-state but differ in exact
      -- target response against some compatible context, that discrepancy is
      -- recorded as a first failure of type (F2)", and "thus, after excluding
      -- (F2), equality of cold corridor states is equality for every
      -- target-response coordinate used by the local replacement".  It holds at
      -- every reading of the corridor's responses, so no carrier travels.
      (∀ presentation : Graph.ColdCorridor.Presentation data.coldSignature object,
        (∀ left right : presentation.Segment,
          presentation.state left = presentation.state right →
          ∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
            presentation.support coordinate ⊆
                ↑(presentation.activeInterface left) →
              presentation.reading left coordinate =
                presentation.reading right coordinate) ∧
        (∀ segments : Fin (Graph.ColdCorridor.stateBound data.coldSignature + 1) →
            presentation.Segment,
          ∃ left right, left ≠ right ∧
            presentation.state (segments left) =
              presentation.state (segments right)) ∧
        ∀ (boundary : Graph.Boundary)
          (carrier : presentation.Segment → Graph.BoundaryPiece boundary)
          (left right : presentation.Segment),
          (¬ presentation.FirstFailureResponse
              (Graph.HasCycleWithLength data.LengthOK) carrier left right →
            presentation.state left = presentation.state right →
              Graph.Response.ContextEquivalent
                (Graph.HasCycleWithLength data.LengthOK)
                (carrier left) (carrier right)) ∧
          -- And the converse the same sentence states: a genuine response
          -- discrepancy at equal states *is* recorded as a first failure of
          -- type (F2).  Committing only one direction would leave the
          -- manuscript's dichotomy at a repeated state half-stated.
          (presentation.state left = presentation.state right →
            ¬ Graph.Response.ContextEquivalent
                (Graph.HasCycleWithLength data.LengthOK)
                (carrier left) (carrier right) →
              presentation.FirstFailureResponse
                (Graph.HasCycleWithLength data.LengthOK) carrier left right))
  | .coldSameInterfaceTable, object =>
      -- `lem:cold-same-interface-table` and `lem:cold-short-self-return-filter`.
      --
      -- The first clause closes every row of `def:cold-same-interface-table`:
      -- no row is realizing, and every row is either handed off to an already
      -- closed ledger or distinguishing.  It is quantified over every handoff
      -- ledger the branch state might carry, so a row cannot escape by naming
      -- its own; a row that is not handed off and not distinguishing is a
      -- target-complete compression of its own proper support, which node
      -- `[14]` has already excluded.
      --
      -- The second is the short self-return filter: a cold-window outside
      -- self-return whose smear interval `[ℓ, ℓ+order−1]` meets an accepted
      -- length realizes it.  The surviving lengths are the rows of the table,
      -- and the first clause closes them with the germs.
      --
      -- The table has two row families, and both are closed here.  The first
      -- clause is the equal-length cold bounded germs; the second is the short
      -- self-return exceptions, whose lengths are *proved* to be
      -- `lem:cold-short-self-return-filter`'s surviving ones -- an accepted
      -- length in a self-return's smear interval would be realized through its
      -- cold-window offset, and the selected object realizes none.
      ((∀ Handoff : Finset object.Vertex → Prop,
        ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object Handoff,
          ¬ row.Realizing ∧ (Handoff row.support ∨ row.Distinguishing)) ∧
        (∀ Handoff : Finset object.Vertex → Prop,
          ∀ self : Graph.ColdCorridor.SelfReturn data.coldSignature data.LengthOK
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object Handoff,
            Graph.ColdCorridor.SurvivesSmear data.LengthOK
                (data.coldSignature.windowOrder - 1) self.outsideLength ∧
              ¬ self.row.Realizing ∧
                (Handoff self.row.support ∨ self.row.Distinguishing)) ∧
        (∀ length : Nat,
          ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
              (data.windowOrder - 1) length →
            ∃ tested, length ≤ tested ∧ tested ≤ length + (data.windowOrder - 1) ∧
              data.LengthOK tested) ∧
        -- `def:cold-same-interface-table`'s own finiteness claim -- "the table
        -- is finite because the support size, boundary size, window labels, and
        -- declared coordinate labels are bounded" -- and the equal-length
        -- condition `δ = 0` that makes a row a row.
        (Graph.ColdCorridor.tableBound data.coldSignature =
          Fintype.card (Graph.ColdCorridor.Record data.coldSignature)) ∧
        ∀ Handoff : Finset object.Vertex → Prop,
          ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object Handoff,
            row.increment = 0)
  | .coldGermRealized, object =>
      -- `lem:cold-bounded-germ-trichotomy`, G1 and the exhaustiveness of the
      -- three cases.
      --
      -- G1 is "some compatible live completion and window offset close a dyadic
      -- cycle.  This contradicts the counterexample condition": a germ's own
      -- compatible completion *is* the selected object, up to the
      -- decomposition's reconstruction isomorphism, so a realizing germ would
      -- hand it the target node `[1]` says it avoids.  No germ realizes.
      --
      -- The second clause is the manuscript's own reading of the split -- "by
      -- whether a compatible completion realizes a dyadic hit, distinguishes
      -- dyadic truth without realization in `G`, or never distinguishes the two
      -- representatives" -- and it is what makes the routing of the remaining
      -- two arms exhaustive rather than partial.  It is also the case
      -- distinction `lem:cold-increment-arithmetic` (c) appeals to when it
      -- sends a target-visible periodic carrier to G2 and a target-invisible one
      -- to G3.
      ((∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
          ¬ germ.Realizing) ∧
        ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
          germ.Realizing ∨ germ.Distinguishing ∨ germ.Neutral)
  | .coldGermDistinguished, object =>
      -- `lem:cold-bounded-germ-trichotomy`, G2, through
      -- `lem:context-universality`: "the two local responses agree in the actual
      -- quotient but disagree in a compatible context.  By
      -- `lem:context-universality`, such an identification is not
      -- target-complete; equivalently it is a target-defective quotient."
      --
      -- The conclusion is drawn in *every* immutable profile fibre, which is
      -- what makes it a statement about the quotient rather than about one
      -- chosen profile, and it is the same shape node `[156]` already commits
      -- for the (F2) discrepancy.  No cycle is claimed: the manuscript is
      -- explicit that G2 distinguishes "without already realizing the cycle in
      -- the current graph", and what the germ is routed to is the defect exit.
      (∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
        ∀ (Profile : Type)
          (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
          germ.Distinguishing →
            ¬ Graph.Response.TargetComplete profile
              (Graph.HasCycleWithLength data.LengthOK) germ.piece germ.canonical)
  | .coldGermSilent, object =>
      -- `lem:cold-bounded-germ-trichotomy`, G3, with
      -- `lem:cold-increment-arithmetic`.
      --
      -- First clause, G3: "replacing the longer representative by the shorter
      -- one preserves the boundary degree profile and the target response
      -- against every context, creates no dyadic cycle, and strictly decreases
      -- the support.  This is a nontrivial target-complete compression of a
      -- proper support", forbidden by `cor:uncompressible`.  The germ is
      -- oriented as the manuscript orients it: its support carries the longer
      -- representative, so `δ < 0` and the replacement is the shorter one.  No
      -- silent length-changing germ survives.
      --
      -- The remaining clauses are `lem:cold-increment-arithmetic`, which decides
      -- which arm a length-changing germ falls into.  Everything is stated at
      -- the smear `order − 1` of `lem:cold-short-self-return-filter`, so the
      -- manuscript's `12` and `13` are the registered window order and no
      -- numeral is written.
      --
      -- (a) `1 ≤ δ ≤ 12`: "the achievable length blocks `[L+jδ, L+jδ+12]`
      -- overlap … Hence their union is an interval.  An interval containing a
      -- power of two gives G1."  An accepted length in the covered interval
      -- makes one block fail the smear filter, which is the offset that closes
      -- the cycle.
      --
      -- (b) `δ ≥ 13` with the doubling orbit hitting a smear residue: "a
      -- congruence `2^k ≡ L + r (mod δ)` with `0 ≤ r ≤ 12` means that, after
      -- adding the appropriate number of homogeneous copies, one attainable
      -- length is `2^k`.  This is exactly a hit-realized germ."
      --
      -- The order criterion: "for odd `δ`, `ord_δ(2) > δ − 13` forces case
      -- (b)", the pigeonhole between the doubling orbit and the complement of
      -- the thirteen smear residues.
      --
      -- The even transient: "for `δ = 2^a u`, the initial powers with `k < a`
      -- form a bounded transient, and for `k ≥ a` the congruence reduces to the
      -- odd modulus `u`."
      --
      -- (d) `δ = 0`: "the equal-length switch belongs to the finite
      -- same-interface cold table", which is `def:cold-same-interface-table`'s
      -- own defining clause and routes the germ to node `[157]`'s table.
      ((∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
          germ.increment < 0 → ¬ germ.Neutral) ∧
        (∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
          germ.increment = 0 ↔
            germ.canonical.internalVertexCount =
              germ.piece.internalVertexCount) ∧
        (∀ increment base copies length : Nat,
          0 < increment →
          increment ≤ (data.coldSignature.windowOrder - 1) + 1 →
          base ≤ length →
          length ≤ base + copies * increment +
            (data.coldSignature.windowOrder - 1) →
          data.LengthOK length →
            ∃ j ≤ copies, ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
              (data.coldSignature.windowOrder - 1) (base + j * increment)) ∧
        (∀ increment base exponent residue : Nat,
          0 < increment →
          residue ≤ (data.coldSignature.windowOrder - 1) →
          base + residue ≤ 2 ^ exponent →
          2 ^ exponent % increment = (base + residue) % increment →
          data.LengthOK (2 ^ exponent) →
            ∃ j, ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
              (data.coldSignature.windowOrder - 1) (base + j * increment)) ∧
        (∀ (increment base : Nat) (_ : NeZero increment),
          (data.coldSignature.windowOrder - 1) + 1 ≤ increment →
          increment - ((data.coldSignature.windowOrder - 1) + 1) <
              orderOf (2 : ZMod increment) →
            ∃ k < orderOf (2 : ZMod increment),
              ∃ residue ≤ (data.coldSignature.windowOrder - 1),
                2 ^ k % increment = (base + residue) % increment) ∧
        ∀ transient exponent odd : Nat, transient ≤ exponent →
          2 ^ exponent % (2 ^ transient * odd) =
            2 ^ transient * (2 ^ (exponent - transient) % odd))
  | .coldFailureCycle, object =>
      -- `lem:cold-corridor-first-failure` (i).  The displayed completion of
      -- clause (F1) -- the window position the entry stub lands on, the stub,
      -- the corridor prefix, the return adjacency, and the window segment
      -- between the two offsets -- is literally a closed walk of the object, so
      -- an accepted one would be an accepted cycle of the selected object.
      -- Node `[1]` says there is none, so (F1) never occurs.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (order : Nat) (window : Graph.ColdCorridor.Window object order)
        (segment : corridor.Segment),
        ¬ corridor.FirstFailureCycle window data.LengthOK segment)
  | .coldFailureDefect, object =>
      -- `lem:cold-corridor-first-failure` (ii), through
      -- `lem:context-universality`.  First clause: an (F2) discrepancy denies
      -- target-completeness of the identification in *every* immutable profile
      -- fibre -- that is what "target-defective quotient" means.  Second:
      -- with the discrepancy excluded, two prefixes carrying the same cold
      -- corridor state have the same target response against every compatible
      -- context, which is what the local replacement consumes.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (presentation :
          Graph.ColdCorridor.Presentation data.coldSignature object)
        (index : corridor.Segment → presentation.Segment)
        (boundary : Graph.Boundary)
        (carrier : presentation.Segment → Graph.BoundaryPiece boundary)
        (left right : corridor.Segment),
        (∀ (Profile : Type) (profile : Graph.BoundaryPiece boundary → Profile),
          Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation index
              (Graph.HasCycleWithLength data.LengthOK) carrier left right →
            ¬ Graph.Response.TargetComplete profile
              (Graph.HasCycleWithLength data.LengthOK)
              (carrier (index left)) (carrier (index right))) ∧
          (¬ Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation index
              (Graph.HasCycleWithLength data.LengthOK) carrier left right →
            presentation.state (index left) = presentation.state (index right) →
              Graph.Response.ContextEquivalent
                (Graph.HasCycleWithLength data.LengthOK)
                (carrier (index left)) (carrier (index right))) ∧
          -- `lem:cold-corridor-first-failure` (ii)'s routing, against the
          -- branch: `def:surviving-cold-branch` (ii) says every identification
          -- the branch makes is context-universal, so an (F2) discrepancy is
          -- not one of them.  The branch is quantified, so no row supplies one.
          ∀ branch : Graph.ColdCorridor.SurvivingColdBranch
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object,
            Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation
                index (Graph.HasCycleWithLength data.LengthOK) carrier left right →
              ¬ branch.Identified boundary
                (carrier (index left)) (carrier (index right)))
  | .coldFailureCompression, object =>
      -- `lem:cold-corridor-first-failure` (iii).  An (F3) pair is a
      -- target-complete compression of the later prefix's own proper support --
      -- same boundary-degree profile, baseline preserved, strictly smaller,
      -- equal response against every outside context -- and node `[14]`'s
      -- `cor:uncompressible` forbids it.  So (F3) never occurs.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (presentation :
          Graph.ColdCorridor.Presentation data.coldSignature object)
        (index : corridor.Segment → presentation.Segment)
        (support : corridor.Segment → Finset object.Vertex),
        ¬ Graph.ColdCorridor.Corridor.FirstFailureCompression.Occurs corridor presentation
          index (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) support)
  | .coldFailureHandoff, object =>
      -- `lem:cold-corridor-first-failure` (iv).  A corridor that first enters
      -- the declared handoff interfaces already recorded in the branch state
      -- reaches *precisely* one of them -- the declared supports are disjoint --
      -- and the charge transfers to that envelope.  Nothing is closed at the
      -- corridor, and the ledger is the branch's, quantified here so no row
      -- manufactures one.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (ledger : Graph.ColdCorridor.Corridor.HandoffLedger object)
        (segment : corridor.Segment),
        Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor ledger segment →
          ∃! envelope, corridor.head segment ∈ ledger.support envelope)
  | .coldFailureRouting, object =>
      -- `lem:cold-corridor-first-failure`, the existence half, together with
      -- the two ledgers it is counted against.
      --
      -- First clause: every cold return corridor has a first failure.  Either
      -- it reaches its successor boundary stub inside `Q_cold` states, or
      -- `Q_cold + 1` states are read and two of them are equal.  This is a case
      -- split on the corridor's own length against `Q_cold`, so (F5) is not the
      -- complement of the other four and the conclusion is not vacuous.
      --
      -- Second: `M_cold` bounds the first-failure cold exchange.
      --
      -- Third: `def:cold-window-ledger`'s split `𝒫 = 𝒫_hot ⊔ 𝒫_cold`.
      --
      -- Fourth: `lem:cold-window-stub-excess`, subtraction-free -- the
      -- branch excess of the ambient-cubic cold windows plus the excess spent
      -- on the `o(n)` non-cubic ones covers `b(P)·C`.
      ((∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (presentation :
          Graph.ColdCorridor.Presentation data.coldSignature object)
        (index : corridor.Segment → presentation.Segment),
        Function.Injective index →
          Graph.ColdCorridor.Corridor.TerminalCorridor corridor data.coldSignature ∨
            Graph.ColdCorridor.Corridor.RepeatedState corridor presentation index) ∧
        (∀ (windows component : Finset object.Vertex)
          (corridor : Graph.ColdCorridor.Corridor object windows component),
          Graph.ColdCorridor.Corridor.TerminalCorridor corridor data.coldSignature →
            corridor.statesRead +
                Graph.ColdCorridor.interfaceBudget data.coldSignature ≤
              Graph.ColdCorridor.exchangeBound data.coldSignature) ∧
        (∀ (Window Coordinate : Type) (_ : DecidableEq Window)
          (_ : DecidableEq Coordinate) (retained : Window → List Coordinate)
          (packageLength : Nat) (packing : Finset Window),
          Graph.ColdCorridor.coldCount retained packageLength packing +
              (Graph.ColdCorridor.hotWindows retained packageLength packing).card =
            packing.card) ∧
        -- `def:cold-skeleton-excess`: dropping the two transit stubs leaves
        -- exactly the branch-excess contribution, so `|𝓔_br(P)| = b(P)` is the
        -- definition and not a second number.
        (∀ (Stub : Type) (stubs : List Stub),
          (Graph.ColdCorridor.selectedBranchExcess stubs).length =
            Graph.ColdCorridor.branchExcessOf stubs.length) ∧
        ∀ cubicCount coldCount nonCubicBound : Nat,
          coldCount ≤ cubicCount + nonCubicBound →
            Graph.ColdCorridor.branchExcessOf
                  (data.threshold * data.windowOrder -
                    2 * (data.windowOrder - 1)) * coldCount ≤
              Graph.ColdCorridor.branchExcessOf
                    (data.threshold * data.windowOrder -
                      2 * (data.windowOrder - 1)) * cubicCount +
                Graph.ColdCorridor.branchExcessOf
                  (data.threshold * data.windowOrder -
                    2 * (data.windowOrder - 1)) * nonCubicBound)
  | .forcedCurvatureCost, object =>
      -- `cor:forced-curvature-cost`, whose whole proof is "this follows from
      -- `lem:full-rank`, `lem:wedge-lower` and the definitions of `K_win` and
      -- `K`".  Node `[30]`'s demand floor is
      --   `δ|R| + 2·(2(order−1)p) ≤ W₂(R) + 2(δ·order·p + σ_W)`,
      -- node `[34]` gives `W₂(R) ≤ r_Ω(R) + o(W₂)`, and the registered cost
      -- multiplies both sides.  At the manuscript's values the left-hand side
      -- is `K_win|R| − o(|R|)` and the right-hand side is `c_Ω·r_Ω(R)`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        data.curvatureCost *
              (data.threshold * (object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
            data.curvatureCost *
                (remainderCurvatureTargetRank data object packing +
                  data.rankDefect (remainderWedgeSupply object packing)) +
              data.curvatureCost *
                (2 * (data.threshold * (data.windowOrder * packing.card) +
                  object.ambientSurplus
                    (Graph.FiniteObject.windowSupport packing)
                    data.threshold)))
  | .remainderEntropyHigh, object =>
      -- Node `[50]`, yes -- node `[51]`.  `η(R) ≥ (1/d)·log₂ n`, exponentiated
      -- by `d·|R|`: the remainder's realized states number at least
      -- `n^{|R|/d}`, which is `prop:two-budget` (a)'s own display.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        Graph.AtLeastEntropyRate object.vertexCount data.entropyDenominator
          data.windowOrder data.threshold
          (object.remainderSupport packing).card)
  | .remainderEntropyLow, object =>
      -- Node `[50]`, no.  The exact negation, with the witness exhibited.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
            data.windowOrder data.threshold
            (object.remainderSupport packing).card)
  | .entropyPackageDemand, object =>
      -- Node `[52]`: `eq:feasibility`'s left-hand side.  Raising the joint
      -- demand to the `d`-th power clears the `1/d` the entropy split carries,
      -- and the high-entropy arm's `n^{|R|} ≤ |𝒢(R)|^d` is substituted for the
      -- remainder factor.  What the inequality says is that the window,
      -- remainder and forced-curvature coordinates together realize at least
      -- `2^{rate·p}·n^{|R|/d}·2^{c_Ω·r_Ω(R)}` states.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (2 ^ (data.windowRate * Graph.dyadicScaleCount object *
              packing.card)) ^ data.entropyDenominator *
              object.vertexCount ^ (object.remainderSupport packing).card *
              (2 ^ (data.curvatureCost *
                remainderCurvatureTargetRank data object packing)) ^
                data.entropyDenominator ≤
            jointPackageDemand data object packing ^ data.entropyDenominator)
  | .entropyCapActive, object =>
      -- Node `[53]`, yes -- the terminal `[54]`.  `eq:entropy-cap`: the
      -- remaining non-curvature budget is strictly smaller than the forced
      -- curvature cost, i.e. the joint package strictly overflows the labelled
      -- skeleton budget of `lem:near-cubic-budget`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        Graph.skeletonBudget object < jointPackageDemand data object packing)
  | .largeBudgetResidual, object =>
      -- Node `[53]`, no -- node `[55]`, Residual C.  The exact negation.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          jointPackageDemand data object packing ≤ Graph.skeletonBudget object)
  | .largeOrderResidual, object =>
      -- Node `[55]`, large arm.
      (2 ^ data.largeOrderExponent ≤ object.vertexCount)
  | .smallOrderResidual, object =>
      -- Node `[55]`, small arm.
      (object.vertexCount < 2 ^ data.largeOrderExponent)
  | .netDeficiencyCap, object =>
      -- Node `[56]`, `Δ_net(R) ≤ τ_win + o(1) < ¼`.  Node `[29]`'s ceiling
      -- divided by `|R|` is the manuscript's `Δ_net`; multiplying back through
      -- by the discharge scale, substituting node `[24]`'s density cap for the
      -- packing, and eliminating it with `|R| + order·p = n` leaves the
      -- manuscript's own `73p₁₃ + 4·o(n) < n` — that is, `N₀(R) < 0`.
      --
      -- Stated at a maximal packing rather than at every one: the cap needs the
      -- packing *number*, which is what node `[24]` bounds, so the statement is
      -- about the packings that attain it.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          object.NegativeNetCharge (object.remainderSupport packing)
            data.threshold data.dischargeScale)
  | .netChargeLocalization, object =>
      -- Nodes `[57]`--`[58]`.  `lem:netcharge-superadd`'s only consumed
      -- consequence, at the registered discharge scale: the canonical
      -- decomposition is exact on the vertex count, the positive deficiency and
      -- the assigned surplus, so a remainder whose own charge is negative has a
      -- connected piece whose charge is negative.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.NegativeNetCharge (object.remainderSupport packing)
            data.threshold data.dischargeScale →
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale)
  | .netChargeNonNegative, object =>
      -- Node `[59]`, yes: `N₀(R) ≥ 0`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.NonNegativeNetCharge (object.remainderSupport packing)
          data.threshold data.dischargeScale)
  | .netChargeNegative, object =>
      -- Node `[59]`, no: `N₀(R) < 0`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          object.NegativeNetCharge (object.remainderSupport packing)
            data.threshold data.dischargeScale)
  | .windowJoinPressure, object =>
      -- Node `[60]`, `cor:global-window-join-pressure`.  Substituting
      -- `lem:surplus-aware-window-stub`'s two links into the nonnegative arm
      -- and eliminating the packing with `|R| + order·p = n` gives
      --   `n + s·σ_R + s·2(order−1)p ≤ s·δ·order·p + s·σ_W + order·p`,
      -- which at the manuscript's values is `σ_W − σ_R ≥ (n − 73p₁₃)/4`.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.vertexCount +
              data.dischargeScale *
                object.ambientSurplus (object.remainderSupport packing)
                  data.threshold +
              data.dischargeScale *
                (2 * (data.windowOrder - 1) * packing.card) ≤
            data.dischargeScale *
                (data.threshold * (data.windowOrder * packing.card)) +
              data.dischargeScale *
                object.ambientSurplus
                  (Graph.FiniteObject.windowSupport packing) data.threshold +
              data.windowOrder * packing.card)
  | .negativeSupport, object =>
      -- Node `[61]`, `prop:negative-net-charge`.  The support is data, so what
      -- the ledger records is its existence, with the two clauses of
      -- `def:admissible` the decomposition supplies: it is a connected piece of
      -- the remainder, and its net charge is negative.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale)
  | .typeALowSurplus, object =>
      -- Node `[62]`, no -- node `[63]`, Type A: the selected support carries no
      -- assigned surplus.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0)
  | .typeBHighSurplus, object =>
      -- Node `[62]`, yes -- node `[64]`, Type B: it carries some.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold)

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys. -/
def name : Key → Lean.Name
  | .selection => `Hypostructure.Graph.Strategy.Spine.selection
  | .returnAvoidance => `Hypostructure.Graph.Strategy.Spine.returnAvoidance
  | .noProperBaseline => `Hypostructure.Graph.Strategy.Spine.noProperBaseline
  | .tightEndpoint => `Hypostructure.Graph.Strategy.Spine.tightEndpoint
  | .slackIndependent => `Hypostructure.Graph.Strategy.Spine.slackIndependent
  | .uncompressible => `Hypostructure.Graph.Strategy.Spine.uncompressible
  | .maximalPacking => `Hypostructure.Graph.Strategy.Spine.maximalPacking
  | .localAlgebra => `Hypostructure.Graph.Strategy.Spine.localAlgebra
  | .surplusAbove => `Hypostructure.Graph.Strategy.Spine.surplusAbove
  | .surplusAtOrBelow => `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow
  | .barrierCap => `Hypostructure.Graph.Strategy.Spine.barrierCap
  | .barrierOverflow => `Hypostructure.Graph.Strategy.Spine.barrierOverflow
  | .densityCap => `Hypostructure.Graph.Strategy.Spine.densityCap
  | .remainderNormalized =>
      `Hypostructure.Graph.Strategy.Spine.remainderNormalized
  | .boundaryDemand => `Hypostructure.Graph.Strategy.Spine.boundaryDemand
  | .stubSupply => `Hypostructure.Graph.Strategy.Spine.stubSupply
  | .wedgeSupply => `Hypostructure.Graph.Strategy.Spine.wedgeSupply
  | .curvatureDemandFloor =>
      `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor
  | .curvatureTargetRank =>
      `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank
  | .curvatureRankDrop => `Hypostructure.Graph.Strategy.Spine.curvatureRankDrop
  | .curvatureFullRank => `Hypostructure.Graph.Strategy.Spine.curvatureFullRank
  | .branchDependence => `Hypostructure.Graph.Strategy.Spine.branchDependence
  | .contextUniversal => `Hypostructure.Graph.Strategy.Spine.contextUniversal
  | .contextDefect => `Hypostructure.Graph.Strategy.Spine.contextDefect
  | .atomCompression => `Hypostructure.Graph.Strategy.Spine.atomCompression
  | .delocalizedSupport =>
      `Hypostructure.Graph.Strategy.Spine.delocalizedSupport
  | .properDelocalization =>
      `Hypostructure.Graph.Strategy.Spine.properDelocalization
  | .globalDelocalization =>
      `Hypostructure.Graph.Strategy.Spine.globalDelocalization
  | .repairIdentity => `Hypostructure.Graph.Strategy.Spine.repairIdentity
  | .globalBarrier => `Hypostructure.Graph.Strategy.Spine.globalBarrier
  | .coldCorridorState =>
      `Hypostructure.Graph.Strategy.Spine.coldCorridorState
  | .coldSameInterfaceTable =>
      `Hypostructure.Graph.Strategy.Spine.coldSameInterfaceTable
  | .coldGermRealized => `Hypostructure.Graph.Strategy.Spine.coldGermRealized
  | .coldGermDistinguished =>
      `Hypostructure.Graph.Strategy.Spine.coldGermDistinguished
  | .coldGermSilent => `Hypostructure.Graph.Strategy.Spine.coldGermSilent
  | .coldFailureCycle => `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
  | .coldFailureDefect => `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
  | .coldFailureCompression =>
      `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
  | .coldFailureHandoff => `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff
  | .coldFailureRouting => `Hypostructure.Graph.Strategy.Spine.coldFailureRouting
  | .forcedCurvatureCost =>
      `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost
  | .remainderEntropyHigh =>
      `Hypostructure.Graph.Strategy.Spine.remainderEntropyHigh
  | .remainderEntropyLow =>
      `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow
  | .entropyPackageDemand =>
      `Hypostructure.Graph.Strategy.Spine.entropyPackageDemand
  | .entropyCapActive => `Hypostructure.Graph.Strategy.Spine.entropyCapActive
  | .largeBudgetResidual =>
      `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual
  | .largeOrderResidual =>
      `Hypostructure.Graph.Strategy.Spine.largeOrderResidual
  | .smallOrderResidual =>
      `Hypostructure.Graph.Strategy.Spine.smallOrderResidual
  | .netDeficiencyCap => `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap
  | .netChargeLocalization =>
      `Hypostructure.Graph.Strategy.Spine.netChargeLocalization
  | .netChargeNonNegative =>
      `Hypostructure.Graph.Strategy.Spine.netChargeNonNegative
  | .netChargeNegative => `Hypostructure.Graph.Strategy.Spine.netChargeNegative
  | .windowJoinPressure =>
      `Hypostructure.Graph.Strategy.Spine.windowJoinPressure
  | .negativeSupport => `Hypostructure.Graph.Strategy.Spine.negativeSupport
  | .typeALowSurplus => `Hypostructure.Graph.Strategy.Spine.typeALowSurplus
  | .typeBHighSurplus => `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus

/-- The value schema at a residual: the object-level statement, read at the
residual's own object. -/
def Value (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key)
    (input : Core.Strategy.ProblemInput
      (problem BranchState Presentation presentation data)) : Type :=
  PLift (Holds BranchState Presentation presentation data k input.object)

theorem name_injective : Function.Injective name := by
  intro left right same
  cases left <;> cases right <;> simp_all [name]

/-- The spine's closed fact vocabulary.  Every value depends on the residual
only through its object, so transport along a refinement is a rewrite. -/
def vocabulary (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    FactVocabulary.{u + 1, v, 0, 0}
      (problem BranchState Presentation presentation data) where
  Key := Key
  keyDecidableEq := inferInstance
  name := name
  name_injective := name_injective
  name_ne_closure := by intro key; cases key <;> decide
  Value := Value BranchState Presentation presentation data
  -- Every spine fact is `PLift` of a proposition, so its value type has at
  -- most one inhabitant: the fact is the statement, and the graph it speaks
  -- about is the residual's.
  value_subsingleton := fun _ _ => ⟨fun left right => by
    cases left; cases right; rfl⟩
  transport := fun {_key} {_new _old} refinement value =>
    ⟨by rw [show _new.object = _old.object from refinement]; exact value.down⟩

/-- The spine's sole `FactSystem`.  It is a definition rather than an
instance because the registered `Data` is a parameter of the spine, not of the
problem; a caller installs it with `letI` for the run it is compiling. -/
noncomputable def factSystem
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    FactSystem
      (Core.Strategy.ProblemInput
        (problem BranchState Presentation presentation data)) :=
  problemInputFactSystem
    (vocabulary BranchState Presentation presentation data)

/-- The exact semantic keys, as callers name them. -/
abbrev key (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key) :
    @FactKey _ _ (factSystem BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

end Hypostructure.Graph.Strategy.Spine
