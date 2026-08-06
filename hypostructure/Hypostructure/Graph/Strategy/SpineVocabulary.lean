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
import Hypostructure.Graph.FanCertificate
import Hypostructure.Graph.TypeBDirectCycle
import Hypostructure.Graph.TypeBFanIncidence
import Hypostructure.Graph.TypeBHybridIncidence
import Hypostructure.Graph.TypeBRefinedSupport
import Hypostructure.Graph.TypeBEnvelopeCharge
import Hypostructure.Graph.TypeADischarge
import Hypostructure.Graph.AnchoredReturnCompletion
import Hypostructure.Graph.ExitFourFamily
import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.ReceiverRouting
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.CommonPortReturnCycle
import Hypostructure.Graph.WindowLabelCollision
import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.WedgeLowerBound
import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.OneThreeRepair
import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Core.CeilSqrt
import Hypostructure.Graph.SeparatedPackageSkeleton
import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.RemainderEntropy
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.ColdBranchClosure
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.CapacityTokenLedger
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparseEntropySandwich

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
  /-- **The quadrilateral is an accepted length.**

  The local fan analysis puts a high centre's neighbourhood into normal form by
  excluding the two quadrilaterals `hxyzh` and `hxzyh` of
  `lem:heavy-neighbourhood-normal-form`, and the *only* thing that argument asks
  of the accepted set is that it contains `4`.

  Registering it here is the analogue of `three_le_threshold`: it is a fact
  about the registered target predicate, discharged once by the presentation --
  for a power-of-two target it is `4 = 2 ^ 2` -- and never a hypothesis about a
  graph.  A presentation whose accepted set misses the quadrilateral does not
  reach the local fan branch. -/
  quadrilateralAccepted : LengthOK 4
  /-- **The degenerate closure is rejected.**

  `lem:labels` derives legality from "if `x` is adjacent to `vᵢ` and `vⱼ` with
  `i < j`, then the subpath `vᵢ⋯vⱼ`, which has length `j − i`, together with the
  two edges `x vᵢ` and `x vⱼ` forms a cycle of length `(j − i) + 2`.  As
  `1 ≤ j − i ≤ 12`, this length lies in `{3, …, 14}`."  The lower end of that
  range is the manuscript reading its own target: the *degenerate* closure --
  one attachment counted twice, with no outside connector -- has closing length
  `Graph.WindowCurvature.closingLength 0 0 = 2`, and it is not a cycle.

  Registering it here is the analogue of `quadrilateralAccepted`: it is a fact
  about the registered target predicate, discharged once by the presentation --
  for a power-of-two target `2 = 2 ^ 1` is below the registered exponent floor
  -- and never a hypothesis about a graph. -/
  degenerateClosureRejected : ¬ LengthOK 2
  /-- **The `4` of node `[58]`.**  `def:net-charge` is
  `N₀(X) = def⁺(X) − σ(X) − |V(X)|/s` at this discharge scale.  Every
  comparison of the charge is made after multiplying through by `s`, so the
  reciprocal never appears and nothing rounds. -/
  dischargeScale : Nat
  dischargeScale_pos : 0 < dischargeScale
  /-- **The marked-fan slack of `lem:typeB-multiclosed-budget`.**

  The local Type B fan ledger pays the closed-neighbour deficit
  `D_B = c − (δ − (k+1)α)` out of half-credits, and that arithmetic needs the
  slack `δ − (k+1)α` to be nonnegative — the manuscript's `(11−k)/4 ≥ 3/4`,
  which it gets from `k ≤ 8`.  The `8` is not a parameter: it is the label
  algebra's own packing number `α(D)` at the registered window order, so the
  condition relates two registered quantities and nothing else.

  Registering it here is the analogue of `quadrilateralAccepted`: a presentation
  whose label algebra is too rich for its discharge scale does not reach the
  local fan ledger. -/
  fanCapSlack :
    Graph.WindowCurvature.fanPackingCap windowOrder + 1 ≤
      dischargeScale * threshold
  /-- **Two fan-closed ports already make the deficit positive.**

  `prop:fan-closed-port-typeB-routing` (b): at `r ≥ 2` fan-closed ports the
  deficit is at least `r − (δ − (k+1)α) ≥ (k−δ)α > 0`.  Cleared of denominators
  at the smallest high-centre degree `k = δ + 1`, that is this comparison between
  registered numbers — the manuscript's `12 < 13`. -/
  highCentreDeficitSlack :
    dischargeScale * threshold < 2 * dischargeScale + (threshold + 2)
  /-- **`C_sp` of node `[19]`.**  The registered scale threshold is
  `C_sp·⌈√n⌉`; only its coefficient is registered, because the `⌈√n⌉` is the
  framework's own and the large-budget branch needs to *know* the threshold is a
  square-root scale in order to spend `σ(G) = O(√n) = o(n)` at node `[56]`. -/
  surplusScale : Nat
  /-- The registered per-window barrier rate of the finite enumeration. -/
  windowRate : Nat
  /-- **The selected dyadic scales of `lem:p13-window-package`.**

  The manuscript's package "uses `⌊log₂ n⌋ − O(1)` separated dyadic scales for
  these finite barriers", the `O(1)` loss absorbing "endpoint collisions with the
  finitely many reserved boundary and tie-breaking choices inside the canonical
  packing".  So the count is the object's own dyadic scale count less a bounded
  discard, and this is where that count is registered — the same way node `[19]`
  registers its scale threshold and node `[32]` its rank allowance.  A row reads
  it; no row writes it. -/
  separatedScaleCount : Nat → Nat
  /-- The selected scales are among the object's own: the discard only loses
  scales, it never invents them. -/
  separatedScaleCount_le : ∀ size : Nat, separatedScaleCount size ≤ Nat.log2 size
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
  /-- **The manuscript's "for all sufficiently large `n`", as a binary
  exponent.**  `prop:negative-net-charge` is stated "for all sufficiently large
  `n`", and nodes `[55]`--`[56]` carry `+o(1)` on every display.  This is where
  that quantifier is registered, and node `[55]` decides the object's order
  against `2 ^ largeOrderExponent` with *both* arms retained — exactly the
  device node `[19]` already uses for its own registered `o(n)` threshold.  The
  small-order arm is the finite residue the manuscript does not address. -/
  largeOrderExponent : Nat
  largeOrderExponent_pos : 0 < largeOrderExponent
  /-- **The discard is bounded**, which is the other half of the manuscript's
  `⌊log₂ n⌋ − O(1)`: `separatedScaleCount_le` says the selection only loses
  scales, and this says it loses boundedly many, so the selected count keeps pace
  with the object's own.  It is stated in the exact form node `[56]` consumes —
  the comparison that lets node `[24]`'s cap be divided at the registered order
  exponent instead of at the raw scale count — and every quantity in it is
  registered. -/
  separatedScaleReach : ∀ size : Nat, 2 ^ largeOrderExponent ≤ size →
    largeOrderExponent * (Nat.log2 size + 1) ≤
      (largeOrderExponent + 1) * separatedScaleCount size
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
  /-- **`F`, the registered Type B bridge-mass factor.**

  `lem:typeB-bridge-deficit-bound` charges each bridge residual centre at
  `No_-(X) ≤ F·Σ_{h∈H_X}(d_G(h) − δ)` — the manuscript's `8`.  The value is not
  forced by anything: the estimate `(k − δ + α) + cα ≤ F(k − δ)` holds for every
  factor above a floor the next field records, and the manuscript picks a round
  one.  So it is a presentation constant, registered here in the same way as the
  order exponent, and `prop:typeB-bridge-sublinear`'s `16σ(G)` is this factor
  against the at-most-twice occurrence convention. -/
  bridgeMassFactor : Nat
  /-- **`27k ≥ 85`, in registered numbers.**

  The manuscript's per-centre estimate is `5k/4 − 11/4 ≤ 8(k−3)`, and it says
  this "is equivalent to `27k ≥ 85`, and holds for every `k ≥ 4`".  Cleared of
  denominators at the registered baseline and discharge scale and spent against
  the smallest high-centre surplus `k − δ = 1`, that equivalence is exactly this
  comparison between registered numbers.

  Registering it here is the analogue of `fanCapSlack`: it is arithmetic of the
  presentation, discharged once, and never a hypothesis about a graph.  A
  presentation whose mass factor is too small for its baseline does not reach the
  Type B bridge. -/
  bridgeMassSlack :
    threshold + 2 + dischargeScale ≤ bridgeMassFactor * dischargeScale

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
  /-- Nodes `[21]`--`[22]`: `lem:p13-window-package`.  The selected coordinates of
  the multi-scale window package are separated, and each carries the audited
  per-window rate.  This is the arm on which `lem:independent-target-entropy`
  applies; the arm where the coordinates collide is the `O(1)` the manuscript's
  scale count discards. -/
  | windowPackageSeparated
  /-- Nodes `[21]`--`[22]`, the other arm: the selected coordinates collide.  This
  is the `O(1)` the manuscript's scale count discards — "endpoint collisions with
  the finitely many reserved boundary and tie-breaking choices inside the
  canonical packing" — and it leaves the block rather than being assumed away. -/
  | windowPackageCollided
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
  /-- Node `[88]`: the routing and threshold algebra of a Type A support.
  `lem:typeA-receiver-loads` — every vertex spending the whole baseline inside
  the support is routed by the canonical trace to exactly one receiver — and
  `lem:typeA-threshold-algebra` — a receiver of internal degree `δ − 1 − j` has
  `q(w) = j + 1`, so its saturation threshold is `H_j = s·(j+1)`, never above
  `s·δ`.  For the manuscript's baseline and discharge scale this is
  `H₀ ≤ 4`, `H₁ ≤ 8`, `H₂ ≤ 12`. -/
  | typeAReceiverRouting
  /-- Node `[89]`, yes arm — the entry of node `[93]`: some receiver of a Type A
  support has reached its saturation threshold, `L(w) ≥ s·q(w)`. -/
  | typeASaturatedReceiver
  /-- Node `[89]`, no arm — node `[90]`: every receiver of every Type A support
  is unsaturated, `L(w) ≤ s·q(w) − 1`.  This is the capacity the `3/7/11`
  discharging of node `[91]` spends. -/
  | typeAUnsaturatedReceivers
  /-- Node `[93]`, yes arm — the entry of the saturated exit chain at node
  `[95]`: some completion port of a saturated receiver of the Type A support
  carries `s` visible receiver-entry returns, in the sense of
  `def:typeA-visible-load`.  This is the hypothesis of
  `lem:typeA-visible-entry`, whose conclusion is the exit list
  `def:typeA-saturated-exits` (1)--(7); the exits themselves are the nodes
  `[95]`--`[107]` this arm enters. -/
  | typeAVisibleEntry
  /-- Node `[93]`, no arm — node `[94]`, `lem:typeA-silent-excess-count`: no
  saturated receiver of the Type A support has a completion port carrying `s`
  visible receiver-entry returns, so the visible-first excess basins of
  `def:typeA-excess-basin` are silent and carry the whole excess,
  `S_sil^exc(X) ≥ s·D_A(X)`.  Cleared of the division and the subtraction,
  `|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`. -/
  | typeAVisibleFirstExcess
  /-- Node `[95]`, yes arm — exit `(1)` of `def:typeA-saturated-exits`: *"an
  anchored return through a completion port of `w` has length in `Mers`"*, at a
  saturated receiver `w` of a Type A support.  `Mers` is the shifted accepted
  set: the return's length plus the restored port edge is an accepted cycle
  length.  `lem:return-equivalence` closes the port edge over the return, so
  this alternative *is* a target cycle, which is why `lem:typeA-exits-discharged`
  lists exit `(1)` among the closed exits. -/
  | typeAExitOneReturn
  /-- Node `[95]`, no arm — the entry of node `[97]`: no anchored return through
  any completion port of any saturated receiver of any Type A support has
  accepted length, so exit `(1)` is not the exit this branch realizes and the
  saturated exit list continues at exit `(2)`. -/
  | typeAExitOneFree
  /-- Node `[97]`, yes arm — exit `(2)` of `def:typeA-saturated-exits`: *"two
  anchored receiver-entry returns through one completion port are internally
  vertex-disjoint as anchored paths and their lengths sum to a power of two"*,
  at a saturated receiver `w` of a Type A support.  Both returns run between the
  two ends of the same port, so `lem:typeA-common-port-return-cycle` glues them
  into a simple cycle of length `|P₁| + |P₂|`; the exit's own side condition is
  that this sum is accepted, which is why `lem:typeA-exits-discharged` lists
  exit `(2)` among the closed exits. -/
  | typeAExitTwoTheta
  /-- Node `[97]`, no arm — the entry of node `[99]`: at every saturated
  receiver of every Type A support, no two receiver-entry returns through one
  of its completion ports are internally vertex-disjoint with accepted total
  length, so exit `(2)` is not the exit this branch realizes and the saturated
  exit list continues at exit `(3)`. -/
  | typeAExitTwoFree
  /-- Node `[99]`, yes arm — exit `(3)` of `def:typeA-saturated-exits`: *"a
  shared `P₁₃` window violates the corresponding legal-label relation `C_s`"*.
  `lem:typeA-visible-entry` reads it as *"if two traces pass through a common
  `P₁₃` window, their labels are governed by the relations `C_s` of
  `lem:labels`; failure of the corresponding `C_s` test is the stated label
  collision"*: two outside vertices attach to one packed window, the simple path
  joining them avoids that window, and the cycle their attachment coordinates
  close through the window has accepted length.  `lem:typeA-exits-discharged`
  lists exit `(3)` among the closed exits, and this is why: the collision *is* a
  target event. -/
  | typeAExitThreeCollision
  /-- Node `[99]`, no arm — the entry of node `[101]`: every shared window of
  the packing satisfies its legal-label relation at every outside connector, so
  exit `(3)` is not the exit this branch realizes and the saturated exit list
  continues at exit `(4)`. -/
  | typeAExitThreeFree
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
  /-- Node `[156]`, the (F4) dispatch arm.  A corridor that enters the declared
  handoff interfaces transfers its charge to that already existing ledger, and
  `def:surviving-cold-branch` (iv)--(v) is what makes the transfer a closure
  rather than an open residual: no Type B or route-8 residual remains outside
  its ledger. -/
  | coldHandoffTransfer
  /-- Nodes `[153]`, `[154]`, the (F5) arm.  `lem:hot-failure-cold-mass` bounds
  the hot windows by the skeleton budget, so the cold count carries the rest;
  `lem:cold-germ-extraction` turns the branch excess into a pairwise
  vertex-disjoint candidate germ family by greedy independence in the
  intersection graph of maximum degree `M_cold·B_cold`; and a positive candidate
  count forces a positive disjoint count, so the (F5) partition is never
  empty. -/
  | coldGermExtraction
  /-- Nodes `[145]`--`[157]`, `thm:cold-branch-quantitative-closure`.  No
  terminal cold branch survives: every germ the extraction produces is
  distinguishing, and a distinguishing germ's identification is a
  target-defective quotient the branch does not carry.  This is the total
  closure -- no arm returns "no target". -/
  | coldBranchClosed
  /-- Node `[68]`, the standing law: every high centre of the object has its
  neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` --
  cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside
  `{h}` for a nonadjacent pair.  Both arms of the degree split run on it. -/
  | highCentreNormalForm
  /-- Node `[68]`, yes arm — the entry of node `[69]`: the Type B support
  carries a *heavy* centre, one whose degree exceeds the high-centre degree
  `δ + 1`.  For the manuscript's baseline this is `d_G(h) ≥ 5`. -/
  | typeBHeavyCentre
  /-- Node `[68]`, no arm — the entry of node `[78]`: no centre of any Type B
  support exceeds `δ + 1`, so every high centre it carries has degree exactly
  `δ + 1`.  For the manuscript's baseline this is the degree-four case. -/
  | typeBDegreeFourCentres
  /-- Node `[69]`: the heavy-centre local dichotomy.  At a heavy centre either
  two open ports are fan-compatible, or at least `d_G(h) − 2` ports are
  triangular -- in particular three (`cor:heavy-center-local-dichotomy`). -/
  | typeBLocalDichotomy
  /-- Node `[70]`: the certificate-marked fan-degree cap.  Every high centre
  carrying a fan-certificate labelling has degree at most the label algebra's
  own packing number -- the manuscript's `d_G(h) ≤ 8`
  (`lem:fan-certificate`, `rem:fan-finite`). -/
  | fanCertificateCap
  /-- Node `[71]`/`[80]`, yes arm: every high centre of the object carries a
  fan-certificate labelling, so every Type B fan it supports is
  certificate-marked (`def:marked-typeB-fan`). -/
  | fanCertificateMarked
  /-- Node `[71]`/`[80]`, no arm: some high centre carries no fan-certificate
  labelling.  `def:marked-typeB-fan` calls it a *fan-certificate residual
  center*; it is charged to the Type B bridge-residual mass of
  `def:typeB-residual-mass` and takes no part in the certificate-closed local
  discharging step. -/
  | fanCertificateResidual
  /-- Nodes `[78]`--`[79]`: the degree-four fan profile.  At a centre sitting
  exactly one above the baseline, `cor:degree-four-local-activation` gives either
  a fan-compatible open pair or `δ − 1` triangular ports -- the manuscript's "at
  least two" at `δ = 3` -- and `[79]`'s three readings hold: the centre surplus
  is `1`, the cubic-closed count is at most the degree, and the closed-neighbour
  deficit of `def:typeB-multiclosed-residual` is `c − (δ − (k+1)α)`, the
  manuscript's `c − 7/4` at its own values. -/
  | typeBDegreeFourProfile
  /-- Node `[74]`/`[82]`: the hybrid B1 fan ledger.  At every certificate-marked
  centre of an assigned Type B support, the non-`h` incidences of its cubic-closed
  neighbours are pairwise distinct carriers, they split into the window count
  `I_W` and the non-window count `I_N` of `def:typeB-hybrid-incidence`, their
  half-credit pays the closed-neighbour deficit `D_B`, the non-window half-credit
  covers the remaining demand `D_N`, and two cubic-closed neighbours already make
  `D_B` positive (`lem:typeB-hybrid-incidence-budget`, `lem:typeB-hybrid-B1`,
  `prop:fan-closed-port-typeB-routing`). -/
  | typeBHybridEntry
  /-- Node `[72]`, the closing arm: some assigned centre carries one of the four
  direct fan-window configurations of
  `lem:typeB-direct-fan-window-cycles`/`lem:typeB-two-window-cycles`, so the
  envelope contains a cycle of accepted length.  The branch that commits this is
  uninhabited: the object was selected to avoid those lengths. -/
  | typeBDirectCycle
  /-- Node `[72]`, the surviving arm — the entry of the B2 question: every closed
  fan-window pair at every assigned centre is direct-cycle-free
  (`def:direct-cycle-free-closed-pair`), so the local fan-window ledger is
  complete and the incidence payment may be counted. -/
  | typeBDirectCycleFree
  /-- Node `[72]`/`[81]`, yes arm — the entry of `[74]`/`[82]`: every connected
  assigned Type B support admits the refined support ledger (B2) of
  `def:typeB-bridge-statements` — a disjoint choice of candidate entries at all
  its assigned centres, maximal for the support assignment. -/
  | typeBDisjointAssignment
  /-- Node `[72]`/`[81]`, no arm — the entry of `[73]`/`[83]`: B2's
  disjoint-carrier clause fails on some assigned support, which by
  `lem:typeB-bridge-to-overlap` carries a minimal Type B overlap obstruction of
  `def:typeB-overlap-obstruction`.  The fact records the obstruction, not the
  bare failure: the minimality is what the fan-mass accounting consumes. -/
  | typeBOverlapObstruction
  /-- Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B bridge fan-mass estimate.
  In the augmented ledger of `def:typeB-assigned-ledger` the only negative terms
  of an assigned fan envelope are its centre and its cubic-closed neighbours; the
  unpaid part they leave is at most the registered mass factor against the
  centre's own surplus (`lem:typeB-bridge-deficit-bound`), summing over the
  assigned centres of a support to `Ĉh_B(X) ≥ −F·σ(X)` and over the pieces of the
  packed-window remainder to the ordinary-role half of
  `prop:typeB-bridge-sublinear`, `M_B ≤ F·S_B ≤ F·σ(G)`. -/
  | typeBBridgeMass
  /-- Nodes `[76]`/`[85]`: `lem:typeB-exclusion`, Step 1 and the accounting
  identity it is spent through.  At every high centre of the object, in every
  assigned fan envelope, the closed-neighbourhood charge of
  `def:typeB-assigned-ledger` is at least `−D_B(𝔉_h)` — the manuscript's
  `(11−k)/4 − c` — so a certificate-closed fan carries nonnegative closed
  neighbourhood charge; at every support the augmented ledger satisfies
  `(B-ledger)`, `No(X) = Ĉh_B(X) + α|H_X|`, so `Ĉh_B(X) ≥ 0` gives
  `defp(X) − σ(X) ≥ α|V(X)|`; and the post-ledger core of
  `lem:typeB-postledger-core-hygiene` carries nonnegative charge, by
  `lem:typeA-unsaturated-discharge` applied to each of its connected
  components. -/
  | typeBExclusionCharge
  /-- Nodes `[76]`/`[85]`, yes arm — `thm:branch-kill` (b).  Every connected
  assigned Type B support of the object is an *excluded* Type B support in the
  sense of `lem:typeB-exclusion`: its assigned centres are certificate-closed on
  coherent, pairwise disjoint fan blocks, and the core outside those blocks
  carries the two Type A conditions of `lem:typeB-postledger-core-hygiene`.  On
  such a support `prop:typeB-bridge-reduction` gives `No(X) ≥ 0`, which the
  node-`[64]` residual denies -- so the branch that commits this fact is
  uninhabited. -/
  | typeBExcluded
  /-- Nodes `[76]`/`[85]`, no arm — the alternative `lem:typeB-exclusion`
  excludes.  Some connected assigned Type B support carries, in its refined
  ledger, an entry that spends half-incidence credits -- an *admissible
  positive-deficit Type B fan-window residual* of
  `def:typeB-multiclosed-residual` -- or a post-ledger core that does not
  discharge, which is an *admissible route-8 Type A residual profile*.  These are
  exactly the two alternatives the lemma assumes away. -/
  | typeBExclusionResidual
  /-- Node `[101]`, the ladder's own exit-`(4)` test, yes arm: exit `(4)` of
  `def:typeA-saturated-exits` occurs at an unpeeled routed load -- a quotient in
  the canonical family `𝒬₄(w)` of `def:typeA-exit4-family` is target-defective
  and its declared support contains that load's canonical coordinate, which is
  `def:typeA-exit4-peeling`'s exit-`(4)` witness.  This is
  `lem:typeA-exit4-residual-routing`'s exit-`(4)` case: while a receiver's
  peeled residual is still saturated, exit `(4)` supplies a witnessed fresh
  unpeeled load, which `lem:typeA-exit4-discharge` adjoins to the peeling
  set. -/
  | typeAExitFourPeel
  /-- Node `[101]`, no arm: exit `(4)` witnesses no unpeeled load of any
  receiver, so no peeling set can be enlarged. -/
  | typeAExitFourNoPeel
  /-- Node `[102]`, the peel's own output, which the manuscript routes back to
  node `[89]`: every receiver has a peeling set -- each of its loads carrying its
  own exit-`(4)` witness, as `def:typeA-exit4-peeling` requires -- leaving it
  unsaturated, so by `lem:typeA-exit4-peeling-charge` its remaining charge
  `q(w) − ¼ − ¼·L₄(w)` is nonnegative.  The descent that produces it is finite
  because each peel drops `L₄(w)` by exactly one. -/
  | typeAPeeledCharge
  /-- Node `[103]`, the exit-`(5)` realization test, yes arm: the nontrivial
  target-complete response compression *is realized by a smaller proper atom*,
  so it is a target-complete compression in the sense of `lem:replacement` --
  which `cor:uncompressible` at node `[14]` excludes. -/
  | typeAExitFiveCompression
  /-- Node `[103]`, the same test's no arm: the compression occurs only at the
  trace-basin response level, so it is exactly failure alternative (b) of
  `def:typeA-trace-basin` and the branch is not an admissible route-8
  residual. -/
  | typeAExitFiveTraceLevel
  /-- Node `[101]`, yes arm: some indexed route-8 entry of the object realizes
  the canonical exit-`(4)` quotient of clause (Q5) of
  `def:typeA-exit4-family` -- a two-carrier entry whose declared deletion witness
  makes a carrier-deletion quotient target-defective.  This is the arm the
  manuscript peels a target-defective routed load on. -/
  | typeAExitFour
  /-- Node `[101]`, no arm: exit `(4)` is absent, which is (R2) of
  `def:typeA-true-route8-residual` for exit `(4)`.  Every later row of the
  route-8 arm reads this fact rather than assuming it. -/
  | typeAExitFourFree
  /-- Node `[103]`, yes arm: some indexed route-8 entry admits a nontrivial
  target-complete quotient of its trace-basin reading -- alternative (b) of
  `def:typeA-trace-basin`, which is exit `(5)`, the target-complete
  compression. -/
  | typeAExitFive
  /-- Node `[103]`, no arm: exit `(5)` is absent, so the internal-forgetting
  reading of every indexed entry is a proper quotient of its core reading.  This
  is the surviving trace `lem:typeA-one-terminal-collapse` collapses against. -/
  | typeAExitFiveFree
  /-- Node `[105]`, yes arm: some indexed route-8 entry has an equality among
  the declared coordinates of its trace-basin reading that becomes
  target-complete only after adjoining a larger connected support `Z ⊋ B_u`.
  This is clause (c) of `def:typeA-trace-basin`, which is exit `(6)`, the
  response delocalization. -/
  | typeAExitSix
  /-- Node `[105]`, no arm: exit `(6)` is absent, which is (R2) of
  `def:typeA-true-route8-residual` for exit `(6)`: no equality among an indexed
  entry's declared coordinates delocalizes to a larger connected support. -/
  | typeAExitSixFree
  /-- Node `[105]`, the scope test's yes arm — the terminal `[106]`, proper
  case: the enlarging support is proper in `G`, so by `lem:proper-smearing` the
  dependence is a replacement of that proper boundaried support, which the
  selection's own uncompressibility and minimality exclude. -/
  | typeAExitSixProper
  /-- Node `[105]`, the same test's no arm — the terminal `[106]`, global case:
  the enlarging support is the whole graph, so by
  `lem:no-silent-global-smearing` the quotient supplies a strictly smaller
  admissible closed representative, which contradicts the selection's
  minimality. -/
  | typeAExitSixGlobal
  /-- Node `[109]`, the route-8 arm: the object carries an admissible true
  large-budget route-8 carrier residual -- `def:typeA-silent-core-residual`'s
  reduced silent profile, `def:typeA-true-route8-residual`'s absence clause
  (R2), the target-complete-minimal trace basins of (R4), and the large-budget
  deficit of `def:typeA-large-budget-deficit` with its burden and rate
  readings. -/
  | route8Residual
  /-- Node `[109]`, the complementary arm: the object carries no such residual,
  so the route-8 exit is not entered and the branch leaves this block. -/
  | route8Free
  /-- Nodes `[111]`--`[113]`: the collection's own burden `N_basin ≥ 4·D_A`
  (`lem:typeA-route8-burden`) and the large-budget deficit bound
  (`def:typeA-large-budget-deficit`), read off every route-8 residual of the
  object. -/
  | route8Burden
  /-- Nodes `[114]`--`[116]`: `lem:typeA-one-terminal-collapse`.  Every indexed
  entry of a true route-8 residual has at least two essential carriers, because
  a smaller carrier core makes the internal-forgetting reading target-complete
  (`lem:typeA-carrier-cut-parity`) and target-complete-minimality of the basin
  then fires one of exits `(4)`--`(7)`, which (R2) denies. -/
  | route8CarrierCore
  /-- Nodes `[117]`--`[122]`: `prop:typeA-route8-carrier-reduction`.  Private
  essential carriers of distinct indexed entries are disjoint boundary
  incidences, so three per entry would exceed the boundary supply the burden
  already spends; hence some indexed entry is two-carrier. -/
  | route8Census
  /-- Node `[123]`: the pressure descent.  No indexed entry of a true route-8
  residual is exit-`(4)` peelable, and every peel of the active entry set
  strictly decreases it, so the descent terminates at the terminal package of
  node `[124]`. -/
  | route8Descent
  /-- Node `[124]`: `thm:typeA-two-carrier-nogo` and
  `prop:typeA-route8-closure-from-nogo`.  There is no terminal two-carrier
  route-8 obstruction, so the object carries no route-8 carrier residual at
  all and the arm closes. -/
  | route8Closed
  /-- Node `[126]`, `lem:sparse-slack-surplus`: the sparse slack identity
  `m = (3/2)n + (1/2)σ(G)`, cleared of division at the registered baseline. -/
  | sparseSlackSurplus
  /-- Node `[127]`, `lem:sparse-excess-port-extraction`, with the family half of
  `lem:surviving-active-family`: the excess selector `𝒫_exc` has exactly `σ(G)`
  members, every selected port has a centre strictly above the baseline and an
  endpoint exactly at it, and therefore carries exactly `δ − 1` shoulders. -/
  | activeSurplusFamily
  /-- Node `[128]`, `lem:sparse-port-activation`, clauses (a)--(d): at a
  selected port carrying a shoulder pair, the port carries the return path
  `R_p ⊆ G − c(p)x(p)` whose first edge after `x(p)` is a shoulder, an open port
  carries the suppression witness `Q_p ⊆ G − x(p)` whose restored length is
  accepted, and a triangular port carries the triangle `x a_p b_p x`. -/
  | sparsePortActivation
  /-- Node `[129]`, `def:baseline-spine-demand` with
  `lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and
  `def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later
  surplus accounting is measured against, evaluated in both directions; the room
  an edge count above the cubic one buys over it; the definition itself, at
  every declared target coordinate family the branch may present, with the
  deficit `E_spine(n)` as this node's own output; and the ordering of the three
  lower-bound packages that supply it.  Every display is committed with the
  logarithms cleared. -/
  | baselineSpineDemand
  /-- Nodes `[130]`--`[134]`, `def:sparse-pair-response`'s pair schedule with
  `def:canonical-blocker-ledger` and
  `lem:canonical-blocker-ledger-no-overcount`: `Π(𝒜₀)` has `C(σ(G),2)` members,
  and at every reading of the closed clause list of `def:surplus-blockers` the
  canonical charge is single-valued, so `Π_blk` and `Π_free` exhaust the
  schedule and `|Π_blk| = Σ_B μ(B)`. -/
  | canonicalPairLedger
  /-- Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with
  `lem:primitive-carrier-supply` and `lem:token-ledger-no-overcount`:
  `|𝔘_sp(G)| = n + 2m + σ(G)`, which is `≤ 6n` on the sparse upper envelope, and
  the token ledger's own fibre identity `|Π_blk| = Σ_t ℓ_cap(t)` at every
  declared token alphabet and assignment. -/
  | capacityTokenLedger
  /-- Node `[137]`, the role split of `def:same-token-blocker-roles`: at every
  token of every presented capacity-token ledger, the role fibres partition the
  token's load, `ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`. -/
  | roleFibrePartition
  /-- Nodes `[137]`--`[143]`, `lem:capacity-token-high-load` with
  `cor:forced-homogeneous-same-token-scale`: the coupled high-load display
  `C(s,2) ≤ E + L_max|𝔗_cap|` at a token that realizes `L_max`, and a role fibre
  there carrying a matching or a star of size `ψ` of its own count. -/
  | fibrePressure
  /-- Nodes `[140]`, `[142]`, `[143]`, the three geometric class audits: a token
  whose load exceeds `Cap_hom(L)` for the bound registered at its own token class
  carries a role-homogeneous `L`-matching or `L`-star. -/
  | bottleneckClassification
  /-- Node `[144]`, `cor:homogeneous-same-token-caps-close`: fixed class caps
  bound every token load by `M₀`, hence `|Π_blk| ≤ M₀|𝔗_cap|` and
  `σ(G) ≤ 1 + 2M₀ + √(2E + 2M₀·scale)`. -/
  | homogeneousBottleneck
  /-- Node `[125]`, `def:named-surplus-exits`: the selected object survives the
  five sparse surplus exits.  This is the standing hypothesis every node of the
  block reads, derived from the selection entry rather than assumed. -/
  | sparseSurplusSurvivor
  /-- Node `[125]`, `def:active-surplus-demands` with
  `lem:surviving-active-family`: the active family is the excess-port family,
  it has `σ(G)` members, and every member carries its canonical return path. -/
  | activeSurplusDemands
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
  2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        packing.card) *
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
      (2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
            object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget object ∧
        ∀ family : Finset Nat, object.edgeCount ∈ family →
          Graph.skeletonBudget object ≤
            Graph.variableEdgeBudget object.vertexCount family)
  | .barrierOverflow, object =>
      (Graph.skeletonBudget object <
        2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
          object.windowPackingNumber data.windowOrder))
  | .densityCap, object =>
      -- `prop:p13-density`.  Spending the skeleton budget's `m !` against the
      -- packed demand leaves `2·rate·scaleCount·p ≤ (scaleCount + 1)(δn + T(n))`,
      -- whose asymptotic form is exactly `θ ≤ (δ/2)/rate + o(1)`, the
      -- manuscript's `θ_win = 1.5/118.108581006…`.  The `o(1)` is the
      -- `(scaleCount + 1)/scaleCount` factor and the `T(n)` term; both are
      -- exact here.
      (2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
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
          ¬ germ.LengthChanging ↔
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
          ∀ branch : Graph.ColdCorridor.SurvivingColdBranch data.coldSignature
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
        (envelopes : Graph.ColdCorridor.Corridor.HandoffEnvelopes object)
        (segment : corridor.Segment),
        Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor envelopes segment →
          ∃! envelope, corridor.head segment ∈ envelopes.support envelope)
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
  | .windowPackageSeparated, object =>
      -- `lem:p13-window-package`.  One coordinate per packed window per selected
      -- dyadic scale, separated, each carrying at least the audited rate, and
      -- fitting the object's own edge count.  The family is data, so what the
      -- ledger records is its existence -- exactly as the packing itself is
      -- recorded by node `[17]` and never carried.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∃ (coordinateCount : Nat)
          (family : Graph.PackedWindowRealization.SeparatedFamily object
            (Fin coordinateCount)),
          2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
                object.windowPackingNumber data.windowOrder) ≤
              Nat.card (∀ coordinate, family.State coordinate) ∧
            jointPackageDemand data object packing ≤
              Nat.card (∀ coordinate, family.State coordinate) ∧
            family.slots.card ≤ object.edgeCount ∧
            object.edgeCount ≤ family.pool.card)
  | .windowPackageCollided, object =>
      -- Nodes `[21]`--`[22]`, the collided arm: the exact negation.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∀ (coordinateCount : Nat)
            (family : Graph.PackedWindowRealization.SeparatedFamily object
              (Fin coordinateCount)),
            ¬ (2 ^ (data.windowRate *
                    data.separatedScaleCount object.vertexCount *
                    object.windowPackingNumber data.windowOrder) ≤
                  Nat.card (∀ coordinate, family.State coordinate) ∧
              jointPackageDemand data object packing ≤
                  Nat.card (∀ coordinate, family.State coordinate) ∧
              family.slots.card ≤ object.edgeCount ∧
              object.edgeCount ≤ family.pool.card))
  | .coldHandoffTransfer, object =>
      -- `lem:cold-corridor-first-failure` (iv), as a closure rather than an
      -- open arm.  A corridor that first enters the declared handoff
      -- interfaces reaches precisely one, and the charge transfers to *that*
      -- envelope of the branch's own recorded ledger.  The ledger is the
      -- branch's, quantified here, so nothing manufactures an empty schedule
      -- and discharges the arm against it.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (envelopes : Graph.ColdCorridor.Corridor.HandoffEnvelopes object)
        (segment : corridor.Segment)
        (failure : Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor
          envelopes segment),
        corridor.head segment ∈
          envelopes.support (Graph.ColdCorridor.Corridor.handoffExit failure).1)
  | .coldGermExtraction, _object =>
      -- `lem:hot-failure-cold-mass` and `lem:cold-germ-extraction`.
      --
      -- First: the hot windows the unclosed comparison leaves are bounded by
      -- the near-cubic skeleton budget, so across `𝒫 = 𝒫_hot ⊔ 𝒫_cold` the cold
      -- count carries everything the hot budget could not -- `C ≥ (θ−θ_win)n −
      -- o(n)`, with every `log₂ n` cancelled and no division.
      --
      -- Second: greedy independence.  A candidate germ family whose
      -- intersection graph has maximum degree `M_cold·B_cold` contains a
      -- pairwise vertex-disjoint subfamily covering it `D_cold`-fold.  This is
      -- the extraction, multiplicatively, so nothing rounds.
      --
      -- Third: a positive candidate count forces a positive disjoint count, so
      -- the (F5) partition is never empty -- "at least one bounded candidate
      -- germ is present on every remaining branch".
      ((∀ hotRate skeletonRate order slack hotCount coldCount packing : Nat,
        packing = hotCount + coldCount →
        hotRate * hotCount ≤ skeletonRate * order + slack →
          hotRate * packing ≤
            hotRate * coldCount + (skeletonRate * order + slack)) ∧
        -- The extraction at the manuscript's own constants: a candidate family
        -- whose intersection graph has maximum degree `M_cold·B_cold` -- each
        -- germ has at most `M_cold` vertices and each vertex lies in at most
        -- `B_cold` germs -- contains a pairwise vertex-disjoint subfamily
        -- covering it `D_cold`-fold.  `D_cold = M_cold·B_cold + 1` is the
        -- registered constant of `def:cold-corridor-first-failure`, so this is
        -- `N_germ ≥ b/D_cold` with the division cleared.
        (∀ (Germ : Type) (_ : DecidableEq Germ) (Overlaps : Germ → Germ → Prop)
          (_ : DecidableRel Overlaps),
          (∀ left right, Overlaps left right → Overlaps right left) →
          ∀ candidates : Finset Germ,
            (∀ candidate ∈ candidates,
              (candidates.filter fun other => Overlaps candidate other).card ≤
                Graph.ColdCorridor.exchangeBound data.coldSignature *
                  Graph.ColdCorridor.overlapBound data.threshold
                    data.coldSignature) →
            ∃ disjointFamily ⊆ candidates,
              Graph.ColdCorridor.IndependentFor Overlaps disjointFamily ∧
                candidates.card ≤ disjointFamily.card *
                  Graph.ColdCorridor.extractionDenominator data.threshold
                    data.coldSignature) ∧
        ∀ (Germ : Type) (_ : DecidableEq Germ)
          (candidates disjointFamily : Finset Germ) (denominator : Nat),
          candidates.card ≤ disjointFamily.card * denominator →
            0 < candidates.card → 0 < disjointFamily.card)
  | .coldBranchClosed, object =>
      -- `thm:cold-branch-quantitative-closure`: "no terminal cold branch
      -- survives after the near-cubic spine estimate has been supplied".
      --
      -- Every length-changing bounded germ is distinguishing.  That is the
      -- elimination of `lem:cold-bounded-germ-trichotomy` against its two
      -- already-closed arms: node `[155]` committed that no germ realizes and
      -- node `[157]` that no oriented germ is silent, so exhaustiveness leaves
      -- G2.  The first clause therefore mentions no branch — it is a statement
      -- about the germ alone, and the branch enters only at the second.
      --
      -- A distinguishing germ's identification is a target-defective quotient,
      -- which `def:surviving-cold-branch` (ii) says the branch does not carry.
      -- So a branch that reaches a germ contradicts its own clause (ii): there
      -- is no terminal cold residual.
      ((∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object,
          germ.increment < 0 → germ.Distinguishing) ∧
        -- `lem:cold-bounded-germ-trichotomy` in full: no length-changing germ
        -- survives, in *either* orientation.  The manuscript's "oriented so
        -- `δ ≥ 0`" names which representative is `E`; `OrientedGerm` records
        -- both occurrences, so the naming is always available and `δ ≠ 0` is
        -- the only hypothesis.
        (∀ branch : Graph.ColdCorridor.SurvivingColdBranch data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object,
          ∀ germ : Graph.ColdCorridor.OrientedGerm data.coldSignature
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object,
            germ.forward.increment ≠ 0 → False) ∧
        -- The other two germ families of the manuscript.  A row of
        -- `def:cold-same-interface-table` -- an equal-length germ or a short
        -- self-return exception -- cannot be realizing and cannot be
        -- distinguishing either, because clause (ii) forbids a distinguishing
        -- germ.  So it is *handed off*: its charge is in the recorded ledger
        -- and nothing is retained at the corridor.  With the clause above, all
        -- three families are closed and the cold branch has no terminal
        -- residual.
        ∀ (Handoff : Finset object.Vertex → Prop)
          (branch : Graph.ColdCorridor.SurvivingColdBranch data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object)
          (row : Graph.ColdCorridor.TableRow data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object Handoff),
          Handoff row.support)
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
        (2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
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
      -- about the packings that attain it.  The maximality is *carried*, not
      -- merely used: `def:admissible`'s inherited clauses are node `[27]`'s
      -- conclusions about `R = G − W`, and node `[27]` is stated at a maximal
      -- packing, so every later node that argues inside `R` needs the same
      -- packing to still be known maximal.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
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
      -- Node `[59]`, yes: `N₀(R) ≥ 0`.  At the maximal packings, which is where
      -- `R = G − W` is the manuscript's remainder.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        object.NonNegativeNetCharge (object.remainderSupport packing)
          data.threshold data.dischargeScale)
  | .netChargeNegative, object =>
      -- Node `[59]`, no: `N₀(R) < 0`, at a maximal packing.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
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
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
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
      -- the remainder, and its net charge is negative.  The packing is carried
      -- with its maximality, which is what lets node `[27]` be read on the
      -- piece: `def:admissible`'s remaining inherited clauses are statements
      -- about the remainder of a *maximal* packing.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale)
  | .typeALowSurplus, object =>
      -- Node `[62]`, no -- node `[63]`, Type A: the selected support carries no
      -- assigned surplus.  The packing keeps its maximality: `def:typeA-support`
      -- is `def:admissible` with `σ(X) = 0`, and the inherited clauses the Type
      -- A ladder spends -- window-freeness and the empty internal `δ`-core --
      -- are node `[27]`'s conclusions about the remainder of a maximal packing.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
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
  | .typeAReceiverRouting, object =>
      -- Node `[88]`.  Stated at every Type A support the object carries, in
      -- the same way node `[27]` is stated at every subregion of a remainder:
      -- a support is data and cannot travel, so what the ledger records is the
      -- statement about all of them.
      --
      -- `def:typeA-support` is `def:admissible` with `σ(X) = 0`; the two
      -- clauses below are `def:typeA-receiver-load`'s own consequences at such
      -- a support.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          object.ambientSurplus piece data.threshold = 0 →
          -- `lem:typeA-receiver-loads`: `r(u)` is defined for every vertex of
          -- internal degree `δ`, and it is a receiver.  Uniqueness is the
          -- routing being a function of `u`.
          (∀ vertex ∈ piece,
            object.internalDegree piece vertex = data.threshold →
            ∃ receiver : object.Vertex,
              object.traceReceiver? piece data.threshold vertex = some receiver ∧
                object.IsReceiver piece data.threshold receiver) ∧
            -- `lem:typeA-threshold-algebra`: `H_j = s·q(w) = s·(j+1) ≤ s·δ`.
            (∀ receiver : object.Vertex,
              object.IsReceiver piece data.threshold receiver →
              data.dischargeScale *
                    object.missingPorts piece data.threshold receiver =
                  data.dischargeScale *
                    (data.threshold - 1 -
                      object.internalDegree piece receiver + 1) ∧
                data.dischargeScale *
                    object.missingPorts piece data.threshold receiver ≤
                  data.dischargeScale * data.threshold))
  | .typeASaturatedReceiver, object =>
      -- Node `[89]`, yes: some receiver of a Type A support is saturated.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver)
  | .typeAUnsaturatedReceivers, object =>
      -- Node `[89]`, no -- node `[90]`: `L(w) ≤ s·q(w) − 1` at every receiver of
      -- every Type A support, written without subtraction.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          object.ambientSurplus piece data.threshold = 0 →
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            1 + object.routedLoad piece data.threshold receiver ≤
              data.dischargeScale *
                object.missingPorts piece data.threshold receiver)
  | .typeAVisibleEntry, object =>
      -- Node `[93]`, yes: `def:typeA-visible-load`'s count at a completion port
      -- of a saturated receiver of the Type A support has reached the
      -- registered multiple.  This is the hypothesis of
      -- `lem:typeA-visible-entry`; its conclusion is the exit list the arm
      -- enters.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ outside ∈
                    Graph.VisibleEntry.completionPorts object piece receiver,
                    data.dischargeScale ≤
                      (Graph.VisibleEntry.visibleLoadsAt object piece
                        data.threshold receiver outside).card)
  | .typeAVisibleFirstExcess, object =>
      -- Node `[93]`, no -- node `[94]`, `lem:typeA-silent-excess-count`:
      -- `S_sil^exc(X) ≥ s·D_A(X)` at every Type A support, with
      -- `s·D_A(X) = |V(X)| − s·def⁺(X)` written without division or
      -- subtraction.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          object.ambientSurplus piece data.threshold = 0 →
          piece.card ≤
            (∑ receiver ∈
                Graph.VisibleEntry.receivers object piece data.threshold,
              (Graph.VisibleEntry.silentExcess object piece data.threshold
                data.dischargeScale receiver).card) +
              data.dischargeScale *
                object.positiveDeficiency piece data.threshold)
  | .typeAExitOneReturn, object =>
      -- Node `[95]`, yes: exit `(1)` of `def:typeA-saturated-exits`, *"an
      -- anchored return through a completion port of `w` has length in
      -- `Mers`"*.
      --
      -- The exit is stated exactly as `def:typeA-saturated-exits` states it:
      -- at a *saturated receiver* of a Type A support, over the anchored
      -- returns through *any* of its completion ports.  Unlike exit `(2)`, the
      -- definition's clause (1) carries no visibility condition and does not
      -- restrict to receiver-entry returns, so neither is written here: the
      -- visible-entry hypothesis is node `[93]`'s own fact, read off the ledger
      -- by the row rather than conjoined into this alternative.
      --
      -- The anchored return is `def:typeA-visible-load`'s `P : h ⤳ w` in
      -- `G − wh`, and `|P| ∈ Mers` is the shifted predicate: `|P| + 1` is an
      -- accepted cycle length.
      --
      -- A support, a receiver and a port are data and cannot travel on the
      -- ledger, so the fact is the statement that some one of them realizes the
      -- exit, exactly as node `[89]`'s arm states its saturated receiver.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ outside ∈
                    Graph.VisibleEntry.completionPorts object piece receiver,
                    ∃ return' :
                        Graph.VisibleEntry.AnchoredReturn object receiver
                          outside,
                      Graph.ShiftedCycleLength data.LengthOK
                        return'.path.length)
  | .typeAExitOneFree, object =>
      -- Node `[95]`, no -- the entry of node `[97]`: the same configuration
      -- with the length test denied at every anchored return of every
      -- completion port of every saturated receiver.  This is the manuscript's
      -- *"assume exits (1)--(3) do not occur"* at its first clause, in the
      -- full strength `def:typeA-saturated-exits` (1) is stated with, and it is
      -- the hypothesis exit `(2)` is asked under.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          object.ambientSurplus piece data.threshold = 0 →
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            object.Saturated piece data.threshold data.dischargeScale
              receiver →
            ∀ outside ∈
              Graph.VisibleEntry.completionPorts object piece receiver,
              ∀ return' :
                  Graph.VisibleEntry.AnchoredReturn object receiver outside,
                ¬ Graph.ShiftedCycleLength data.LengthOK
                  return'.path.length)
  | .typeAExitTwoTheta, object =>
      -- Node `[97]`, yes -- exit `(2)` of `def:typeA-saturated-exits`: *"two
      -- anchored receiver-entry returns through one completion port are
      -- internally vertex-disjoint as anchored paths and their lengths sum to a
      -- power of two"*.
      --
      -- The clause names the port itself -- *"through one completion port"* --
      -- and names the returns as the *receiver-entry* returns of
      -- `def:typeA-visible-load`, not arbitrary paths of the object, so both are
      -- written here.  What the clause does not carry is node `[93]`'s visible
      -- *count*: that is the branch's warrant for being on the exit list, read
      -- off the ledger by exact key, and conjoining it would weaken the no arm
      -- below past `def:typeA-saturated-exits` (2)'s own negation.
      --
      -- `data.LengthOK (|P₁| + |P₂|)` is the exit's own side condition; nothing
      -- writes a power of two, and `lem:typeA-common-port-return-cycle` is what
      -- turns the condition into an accepted cycle.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ outside ∈
                    Graph.VisibleEntry.completionPorts object piece receiver,
                    Graph.VisibleEntry.ExitTwoThrough object piece
                      data.LengthOK receiver outside)
  | .typeAExitTwoFree, object =>
      -- Node `[97]`, no -- the entry of node `[99]`: the same configuration
      -- with the exit-`(2)` test denied at every completion port of every
      -- saturated receiver.  This is the manuscript's *"assume exits (1)--(3)
      -- do not occur"* at its second clause, in the full strength
      -- `def:typeA-saturated-exits` (2) is stated with, and it is the hypothesis
      -- exit `(3)` is asked under.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          object.ambientSurplus piece data.threshold = 0 →
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            object.Saturated piece data.threshold data.dischargeScale
              receiver →
            ∀ outside ∈
              Graph.VisibleEntry.completionPorts object piece receiver,
              ¬ Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK
                receiver outside)
  | .typeAExitThreeCollision, object =>
      -- Node `[99]`, yes -- exit `(3)` of `def:typeA-saturated-exits`: *"a
      -- shared `P₁₃` window violates the corresponding legal-label relation
      -- `C_s`"*.
      --
      -- Unlike clauses (1) and (2), clause (3) names no receiver and no
      -- completion port: it is a statement about a window shared by two
      -- attachments, and `WindowLabelCollision.LabelCollision` takes the
      -- packing alone.  So neither a receiver nor a port nor node `[93]`'s
      -- visible count is written here; the configuration is the Type A support
      -- the exit list is scoped to, and the branch's warrant for being on that
      -- list stays where it belongs, on the ledger.
      --
      -- The exit itself is the *local label test*, which is how
      -- `lem:typeA-exits-discharged` discharges it: "precisely failure of
      -- the legal `P₁₃` label relation from `lem:labels`".  Two outside
      -- vertices attach to one packed window, the simple path joining them
      -- avoids that window, and the cycle their coordinates close has accepted
      -- length -- which `WindowLabelCollision.labelCollision_iff_not_safe` says
      -- is exactly `¬ C_s(S, T)` at the registered dyadic target.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              Graph.WindowLabelCollision.LabelCollision object
                data.windowOrder data.LengthOK packing)
  | .typeAExitThreeFree, object =>
      -- Node `[99]`, no -- the entry of node `[101]`: the same configuration
      -- with the exit-`(3)` test denied.  This is the manuscript's *"assume
      -- exits (1)--(3) do not occur"* at its third clause, and it is the
      -- hypothesis the exit-`(4)` family is built under.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          object.ambientSurplus piece data.threshold = 0 →
          Graph.WindowLabelCollision.LabelCollisionFree object
            data.windowOrder data.LengthOK packing)
  | .highCentreNormalForm, object =>
      -- Node `[68]`: `lem:heavy-neighbourhood-normal-form`, at every high
      -- centre of the object at once.  It is not about one support, so it is
      -- stated of the object and both arms of the split read it.
      (∀ centre : object.Vertex,
        Graph.IsHighCentre object data.threshold centre →
        Graph.NormalForm object data.threshold centre)
  | .typeBHeavyCentre, object =>
      -- Node `[68]`, yes -- node `[69]`: some Type B support carries a centre
      -- above the high-centre degree `δ + 1`, i.e. a heavy centre.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece, data.threshold + 1 < object.degree centre)
  | .typeBDegreeFourCentres, object =>
      -- Node `[68]`, no -- node `[78]`: no Type B support carries a centre
      -- above `δ + 1`, so every high centre any of them carries sits exactly
      -- at `δ + 1`.  Stated positively, and over every support rather than a
      -- named one: a support is data and no fact can carry it.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          ∀ centre ∈ piece, data.threshold < object.degree centre →
            object.degree centre = data.threshold + 1)
  | .typeBLocalDichotomy, object =>
      -- Node `[69]`, `cor:heavy-center-local-dichotomy`, at every heavy centre
      -- of the object at once: a centre is data, so the fact quantifies rather
      -- than naming the one the arm was entered on.
      (∀ centre : object.Vertex,
        data.threshold + 1 < object.degree centre →
        (∃ left right : object.Vertex,
            Graph.FanCompatible object centre left right) ∨
          (object.degree centre - 2 ≤
              (Graph.triangularEndpoints object centre).card ∧
            3 ≤ (Graph.triangularEndpoints object centre).card))
  | .fanCertificateCap, object =>
      -- Node `[70]`, `lem:fan-certificate`.  The bound is the label algebra's
      -- own packing number at the registered window order, never a numeral: at
      -- the manuscript's order it evaluates to its `8`.  The labelling is data,
      -- so the fact quantifies over every one rather than carrying one.
      (∀ centre : object.Vertex,
        Graph.IsHighCentre object data.threshold centre →
        ∀ _marking :
            Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder)
  | .fanCertificateMarked, object =>
      -- Node `[71]`/`[80]`, yes.  `def:marked-typeB-fan` scopes the question to
      -- centres *assigned to a Type B support*, so the quantifier runs over the
      -- centres of such a support and not over the object's high centres at
      -- large: a high centre outside every Type B support is not a
      -- fan-certificate residual center and carries no Type B bridge mass.
      -- A labelling is data, so the fact records that one exists rather than
      -- carrying any.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          ∀ centre ∈ piece,
            Graph.IsHighCentre object data.threshold centre →
            Nonempty
              (Graph.FanCertificateLabelling object data.windowOrder centre))
  | .fanCertificateResidual, object =>
      -- Node `[71]`/`[80]`, no: some centre assigned to a Type B support
      -- carries no labelling.  That centre is `def:marked-typeB-fan`'s
      -- *fan-certificate residual center*.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre ∧
                  IsEmpty
                    (Graph.FanCertificateLabelling object data.windowOrder
                      centre))
  | .typeBDegreeFourProfile, object =>
      -- Nodes `[78]`--`[79]`.  Stated at every centre of the object sitting one
      -- above the baseline at once, because `[78]`'s own fact says every high
      -- centre a Type B support carries is such a centre, and a centre is data
      -- that no fact can carry.  The envelope is quantified for the same reason:
      -- which vertices a marked fan assigns is fan data.
      (∀ centre : object.Vertex, object.degree centre = data.threshold + 1 →
        ((∃ left right : object.Vertex,
              Graph.FanCompatible object centre left right) ∨
            data.threshold - 1 ≤
              (Graph.triangularEndpoints object centre).card) ∧
          object.degree centre - data.threshold = 1 ∧
          ∀ envelope : Finset object.Vertex,
            Graph.TypeBFanIncidence.closedCount object data.threshold envelope
                centre ≤ data.threshold + 1 ∧
              Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                  data.dischargeScale envelope centre =
                (data.dischargeScale : Int) *
                    (Graph.TypeBFanIncidence.closedCount object data.threshold
                      envelope centre : Int) -
                  (data.dischargeScale : Int) * (data.threshold : Int) +
                    ((data.threshold : Int) + 2))
  | .typeBHybridEntry, object =>
      -- Node `[74]`/`[82]`.  Scoped to the centres of a Type B support, because
      -- `k ≤ α(D)` is available only at a certificate-marked fan, and quantified
      -- over the envelope and the packed-window union because both are fan data.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          ∀ centre ∈ piece,
            Graph.IsHighCentre object data.threshold centre →
            ∀ envelope windowSupport : Finset object.Vertex,
              -- The carriers are distinct: no non-`h` endpoint is shared.
              (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours object
                  data.threshold envelope centre,
                ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours object
                    data.threshold envelope centre,
                  left ≠ right →
                  ∀ shared : object.Vertex,
                    shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences object
                      centre left →
                    shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences object
                      centre right) ∧
                -- `I_W + I_N = (δ − 1)·c`.
                Graph.TypeBHybridIncidence.windowIncidences object data.threshold
                      envelope windowSupport centre +
                    Graph.TypeBHybridIncidence.nonWindowIncidences object
                      data.threshold envelope windowSupport centre =
                  (data.threshold - 1) *
                    Graph.TypeBFanIncidence.closedCount object data.threshold
                      envelope centre ∧
                -- The hybrid entry pays `D_B`.
                2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                        data.dischargeScale envelope centre ≤
                    (data.dischargeScale : Int) *
                      ((Graph.TypeBHybridIncidence.windowIncidences object
                          data.threshold envelope windowSupport centre : Int) +
                        (Graph.TypeBHybridIncidence.nonWindowIncidences object
                          data.threshold envelope windowSupport centre : Int)) ∧
                -- The non-window half-credit covers `D_N`.
                Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
                      data.dischargeScale envelope windowSupport centre ≤
                    (data.dischargeScale : Int) *
                      (Graph.TypeBHybridIncidence.nonWindowIncidences object
                        data.threshold envelope windowSupport centre : Int) ∧
                -- Two cubic-closed neighbours make the deficit positive.
                (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
                    envelope centre →
                  0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                    data.dischargeScale envelope centre))
  | .typeBDirectCycle, object =>
      -- Node `[72]`, the closing arm.  `lem:typeB-direct-fan-window-cycles` and
      -- `lem:typeB-two-window-cycles` in the shape their negation produces: an
      -- assigned centre of a Type B support carries one of the four direct
      -- configurations, over the windows of the packing the support is read in.
      -- The configuration is data, so the fact records that one exists.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre ∧
                  Graph.TypeBDirectCycle.DirectCycleConfiguration object
                    data.windowOrder data.LengthOK packing centre)
  | .typeBDirectCycleFree, object =>
      -- Node `[72]`, the surviving arm: `def:direct-cycle-free-closed-pair` at
      -- every assigned centre of every Type B support, over every packing.
      -- Stated positively and universally, for the same reason node `[78]`'s
      -- own fact is: a support and a centre are data, and no fact carries one.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          ∀ centre ∈ piece,
            Graph.IsHighCentre object data.threshold centre →
            Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
              data.LengthOK packing centre)
  | .typeBDisjointAssignment, object =>
      -- Node `[72]`/`[81]`, yes.  (B2) of `def:typeB-bridge-statements` at every
      -- connected assigned Type B support: its assigned centres carry a maximal
      -- disjoint refined ledger.  The ledger is data, so the fact records that
      -- one exists.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          Nonempty (Graph.TypeBRefinedSupport.RefinedSupportAssignment object
            data.threshold data.dischargeScale piece))
  | .typeBOverlapObstruction, object =>
      -- Node `[72]`/`[81]`, no.  `lem:typeB-bridge-to-overlap`: the
      -- disjoint-carrier clause fails on some assigned support, and what that
      -- support then carries is a *minimal* Type B overlap obstruction.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
                data.threshold data.dischargeScale piece))
  | .typeBBridgeMass, object =>
      -- Nodes `[73]`/`[75]`, `[83]`/`[84]`, at the assigned Type B supports of
      -- this residual and at the families drawn from its packed-window
      -- remainder.  Nothing is stated of an arbitrary region.
      ((∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        -- At every connected assigned Type B support of this residual.
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          -- `lem:typeB-bridge-deficit-bound`, display (1), at its assigned
          -- centres.  The envelope is fan data, so it is quantified.
          (∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
            ∀ envelope : Finset object.Vertex,
              Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
                  data.dischargeScale envelope centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (object.degree centre - data.threshold)) ∧
            -- `lem:typeB-bridge-deficit-bound`: `No_-(X) ≤ F·σ(X)`.
            (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
                data.threshold data.dischargeScale →
              piece.card + data.dischargeScale *
                    object.ambientSurplus piece data.threshold ≤
                data.dischargeScale * object.positiveDeficiency piece data.threshold +
                  data.bridgeMassFactor * data.dischargeScale *
                    object.ambientSurplus piece data.threshold)) ∧
        -- `lem:typeB-bridge-with-route8-core`, and at an empty route-8
        -- collection `prop:typeB-bridge-sublinear`, over the canonical
        -- decomposition of this residual's packed-window remainder.
        (∀ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing →
          ∀ route8 : Finset (Graph.SupportComponents.Connected.Component object
              (object.remainderSupport packing)),
            (∀ piece ∈ route8,
              object.ambientSurplus (object.pieceSupport
                (object.remainderSupport packing) piece) data.threshold = 0) →
            (∀ piece ∈ object.canonicalPieces (object.remainderSupport packing),
              piece ∉ route8 →
              Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
                (object.pieceSupport (object.remainderSupport packing) piece)
                data.threshold data.dischargeScale) →
            ∑ piece ∈ object.canonicalPieces (object.remainderSupport packing),
                ((object.pieceSupport (object.remainderSupport packing) piece).card +
                    data.dischargeScale * object.ambientSurplus
                      (object.pieceSupport (object.remainderSupport packing) piece)
                      data.threshold -
                  data.dischargeScale * object.positiveDeficiency
                    (object.pieceSupport (object.remainderSupport packing) piece)
                    data.threshold) ≤
              Graph.TypeBEnvelopeCharge.route8Deficit object
                  (object.remainderSupport packing) data.threshold
                  data.dischargeScale route8 +
                data.bridgeMassFactor * data.dischargeScale *
                  object.degreeSurplus data.threshold) ∧
        -- `def:typeB-residual-mass`, the at-most-twice occurrence convention:
        -- the ordinary assigned role and the grouped decorated envelope role,
        -- both drawn from this residual's remainder.
        ∀ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing →
          ∀ ordinary grouped : Finset object.Vertex,
            ordinary ⊆ object.remainderSupport packing →
            grouped ⊆ object.remainderSupport packing →
            ∀ ordinaryRoute8 : Finset
                (Graph.SupportComponents.Connected.Component object ordinary),
            ∀ groupedRoute8 : Finset
                (Graph.SupportComponents.Connected.Component object grouped),
              (∀ piece ∈ ordinaryRoute8,
                object.ambientSurplus (object.pieceSupport ordinary piece)
                  data.threshold = 0) →
              (∀ piece ∈ groupedRoute8,
                object.ambientSurplus (object.pieceSupport grouped piece)
                  data.threshold = 0) →
              (∀ piece ∈ object.canonicalPieces ordinary, piece ∉ ordinaryRoute8 →
                Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
                  (object.pieceSupport ordinary piece) data.threshold
                  data.dischargeScale) →
              (∀ piece ∈ object.canonicalPieces grouped, piece ∉ groupedRoute8 →
                Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
                  (object.pieceSupport grouped piece) data.threshold
                  data.dischargeScale) →
              ∑ piece ∈ object.canonicalPieces ordinary,
                  ((object.pieceSupport ordinary piece).card +
                      data.dischargeScale * object.ambientSurplus
                        (object.pieceSupport ordinary piece) data.threshold -
                    data.dischargeScale * object.positiveDeficiency
                      (object.pieceSupport ordinary piece) data.threshold) +
                ∑ piece ∈ object.canonicalPieces grouped,
                  ((object.pieceSupport grouped piece).card +
                      data.dischargeScale * object.ambientSurplus
                        (object.pieceSupport grouped piece) data.threshold -
                    data.dischargeScale * object.positiveDeficiency
                      (object.pieceSupport grouped piece) data.threshold) ≤
                Graph.TypeBEnvelopeCharge.route8Deficit object ordinary
                    data.threshold data.dischargeScale ordinaryRoute8 +
                  Graph.TypeBEnvelopeCharge.route8Deficit object grouped
                      data.threshold data.dischargeScale groupedRoute8 +
                    2 * (data.bridgeMassFactor * data.dischargeScale *
                      object.degreeSurplus data.threshold))
  | .typeBExclusionCharge, object =>
      -- Nodes `[76]`/`[85]`, at the connected assigned Type B supports of this
      -- residual.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          -- `(B-ledger)` at this support, and the line it is spent on.
          (Graph.TypeBEnvelopeCharge.augmentedLedger object data.threshold
                  data.dischargeScale piece +
                ((Graph.TypeBRefinedSupport.centres object data.threshold
                  piece).card : Int) =
              ((data.dischargeScale *
                  object.positiveDeficiency piece data.threshold : Nat) : Int) -
                ((data.dischargeScale *
                  object.ambientSurplus piece data.threshold : Nat) : Int) -
                (piece.card : Int) ∧
            (0 ≤ Graph.TypeBEnvelopeCharge.augmentedLedger object data.threshold
                data.dischargeScale piece →
              object.NonNegativeNetCharge piece data.threshold
                data.dischargeScale)) ∧
            -- Step 2, read off B2: the entries, their carriers, their
            -- disjointness and their payment are node `[72]`/`[81]`'s.
            ∃ assignment : Graph.TypeBRefinedSupport.RefinedSupportAssignment
                object data.threshold data.dischargeScale piece,
              ∀ entry : ∀ hub ∈ assignment.demands,
                  Graph.TypeBRefinedSupport.CandidateEntry object data.threshold
                    data.dischargeScale piece hub,
                (∀ (left : object.Vertex) (leftMember : left ∈ assignment.demands)
                  (right : object.Vertex)
                  (rightMember : right ∈ assignment.demands), left ≠ right →
                  Disjoint (entry left leftMember).carriers
                    (entry right rightMember).carriers) →
                (∀ (hub : object.Vertex) (member : hub ∈ assignment.demands),
                  (entry hub member).chosen = ∅) →
                Graph.TypeBEnvelopeCharge.PostLedgerCore object piece assignment
                  entry →
                object.NonNegativeNetCharge piece data.threshold
                  data.dischargeScale)
  | .typeBExcluded, object =>
      -- Nodes `[76]`/`[85]`, yes -- `thm:branch-kill` (b).  The conclusion of
      -- `prop:typeB-bridge-reduction` at every connected assigned Type B
      -- support: `defp(X) − σ(X) ≥ α|V(X)|`.  The node-`[64]` residual denies
      -- it, so the branch that commits this fact is uninhabited.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          object.NonNegativeNetCharge piece data.threshold data.dischargeScale)
  | .typeBExclusionResidual, object =>
      -- Nodes `[76]`/`[85]`, no.  The exact complement of the yes arm's
      -- hypotheses: some assigned Type B support of this residual has a
      -- disjoint refined ledger one of whose entries is not certificate-closed,
      -- or whose post-ledger core does not discharge.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset object.Vertex,
            piece ⊆ object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn object piece ∧
              object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ assignment : Graph.TypeBRefinedSupport.RefinedSupportAssignment
                  object data.threshold data.dischargeScale piece,
                ∃ entry : ∀ hub ∈ assignment.demands,
                    Graph.TypeBRefinedSupport.CandidateEntry object
                      data.threshold data.dischargeScale piece hub,
                  (∀ (left : object.Vertex)
                    (leftMember : left ∈ assignment.demands)
                    (right : object.Vertex)
                    (rightMember : right ∈ assignment.demands), left ≠ right →
                    Disjoint (entry left leftMember).carriers
                      (entry right rightMember).carriers) ∧
                    ¬ ((∀ (hub : object.Vertex)
                          (member : hub ∈ assignment.demands),
                        (entry hub member).chosen = ∅) ∧
                      Graph.TypeBEnvelopeCharge.PostLedgerCore object piece
                        assignment entry))

  | .typeAExitFourPeel, object =>
      -- Node `[101]`, yes: exit `(4)` of `def:typeA-saturated-exits` -- *"a
      -- quotient in the canonical exit-(4) family `𝒬₄(w)` is
      -- target-defective"* -- at an unpeeled routed load, which is
      -- `lem:typeA-exit4-residual-routing`'s exit-`(4)` case together with the
      -- exit-`(4)` witness of `def:typeA-exit4-peeling`.  A support, a
      -- receiver, and the receiver's declared reading are data, so the fact is
      -- read at every one of them at once.
      (∀ piece : Finset object.Vertex, ∀ receiver : object.Vertex,
        ∀ family : Graph.ExitFour.Family
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            receiver (Sym2 object.Vertex),
        ∀ peeled : Finset object.Vertex,
          family.IsPeeling peeled →
          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
              receiver peeled →
            ∃ load ∈
                Graph.ExitFour.unpeeledLoads piece data.threshold receiver
                  peeled,
              family.Witness load)
  | .typeAExitFourNoPeel, object =>
      -- Node `[101]`, no.
      (¬ ∀ piece : Finset object.Vertex, ∀ receiver : object.Vertex,
        ∀ family : Graph.ExitFour.Family
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            receiver (Sym2 object.Vertex),
        ∀ peeled : Finset object.Vertex,
          family.IsPeeling peeled →
          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
              receiver peeled →
            ∃ load ∈
                Graph.ExitFour.unpeeledLoads piece data.threshold receiver
                  peeled,
              family.Witness load)
  | .typeAPeeledCharge, object =>
      -- Node `[102]`: the peeled receiver, retested at `[89]`.  The peeling set
      -- it stops at is `def:typeA-exit4-peeling`'s: every load it lists carries
      -- its own exit-`(4)` witness.
      (∀ piece : Finset object.Vertex, ∀ receiver : object.Vertex,
        ∀ family : Graph.ExitFour.Family
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            receiver (Sym2 object.Vertex),
        ∃ peeled : Finset object.Vertex,
          family.IsPeeling peeled ∧
            ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
              data.dischargeScale receiver peeled)
  | .typeAExitFiveCompression, object =>
      -- Node `[103]`, yes: the compression is realized by a smaller proper
      -- atom, which is `lem:replacement`'s target-complete compression.
      (∃ support : Finset object.Vertex,
        Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitFiveTraceLevel, object =>
      -- Node `[103]`, no: it stays at the trace-basin response level.
      (¬ ∃ support : Finset object.Vertex,
        Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitFour, object =>
      -- Node `[101]`, yes.  A route-8 entry is data, so the fact records that
      -- some data on the object has an entry realizing exit `(4)`.
      (∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        ∃ index ∈ residual.entries, residual.ExitFour index)
  | .typeAExitFourFree, object =>
      -- Node `[101]`, no -- (R2) for exit `(4)`.
      (Graph.Route8.ExitFourFree (Graph.HasCycleWithLength data.LengthOK) object)
  | .typeAExitFive, object =>
      -- Node `[103]`, yes: some indexed entry's internal-forgetting reading is
      -- its core reading, which is alternative (b) of `def:typeA-trace-basin`.
      (∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        ∃ index ∈ residual.entries, ¬ residual.SurvivingTrace index)
  | .typeAExitFiveFree, object =>
      -- Node `[103]`, no -- (R2) for exit `(5)`.
      (Graph.Route8.TraceSurviving
        (Graph.HasCycleWithLength data.LengthOK) object)
  | .typeAExitSix, object =>
      -- Node `[105]`, yes: some indexed entry carries clause (c) of
      -- `def:typeA-trace-basin` -- an equality among its declared coordinates
      -- that becomes target-complete only at a larger connected support.
      (∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        ∃ index ∈ residual.entries,
          residual.Delocalizes
            (Graph.MinimumDegreeAtLeast data.threshold) index)
  | .typeAExitSixFree, object =>
      -- Node `[105]`, no -- (R2) for exit `(6)`.
      (Graph.Route8.DelocalizationFree
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
  | .typeAExitSixProper, object =>
      -- Node `[105]`, the scope test's proper case: `lem:proper-smearing`'s
      -- conclusion at the enlarging support `Z ⊊ G`.
      (∃ support : Finset object.Vertex,
        Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitSixGlobal, object =>
      -- Node `[105]`, the scope test's global case:
      -- `lem:no-silent-global-smearing`'s conclusion at `Z = G`.
      (∃ representative : Graph.FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK object))
  | .route8Residual, object =>
      -- Node `[109]` with `[111]`--`[112]`: the arm is entered with a
      -- *large-budget* route-8 collection.  The collection is data, so the fact
      -- records that one exists; the three readings that depend on it -- the
      -- burden, the large-budget deficit and the registered rate -- are the
      -- statement of this key.  The exit clauses (R2) are *not* here: they are
      -- nodes `[101]` and `[103]`'s own facts.
      (∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        residual.LargeBudget)
  | .route8Free, object =>
      -- Node `[109]`, the complementary arm.
      (¬ ∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        residual.LargeBudget)
  | .route8Burden, object =>
      -- Nodes `[111]`--`[113]`: the same residual with `lem:typeA-route8-burden`
      -- substituted into `def:typeA-large-budget-deficit`, which is the reading
      -- the census of node `[122]` spends.
      (∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        residual.Reduced)
  | .route8CarrierCore, object =>
      -- Nodes `[114]`--`[116]`, `lem:typeA-one-terminal-collapse`.
      (∀ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        ∀ index ∈ residual.entries,
          residual.SurvivingTrace index → 2 ≤ residual.alpha index)
  | .route8Census, object =>
      -- Nodes `[117]`--`[122]`, `prop:typeA-route8-carrier-reduction`: a reduced
      -- large-budget route-8 residual contains the terminal two-carrier package
      -- of `def:typeA-terminal-two-carrier`.
      (∀ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        residual.Reduced → residual.TwoCarrierEntry)
  | .route8Descent, object =>
      -- Node `[123]`.  The first clause is the manuscript's routing: the
      -- remaining ledger forces a two-carrier route-8 entry, which is the
      -- terminal package node `[124]` is entered with.  The second is the
      -- descent's own measure -- peeling an entry strictly decreases the active
      -- set -- which is why the loop back to `[89]` terminates.
      (∀ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        (residual.Reduced → residual.TwoCarrierEntry) ∧
          ∀ active : Finset residual.Index, ∀ index ∈ active,
            (active.erase index).card < active.card)
  | .route8Closed, object =>
      -- Node `[124]`, `thm:typeA-two-carrier-nogo` with
      -- `prop:typeA-route8-closure-from-nogo`: no large-budget route-8
      -- collection exists, which is what closes the arm against node `[109]`'s
      -- own fact.
      (¬ ∃ residual : Graph.Route8.Data
          (Graph.HasCycleWithLength data.LengthOK) object,
        residual.LargeBudget)
  | .sparseSlackSurplus, object =>
      -- `lem:sparse-slack-surplus`: `2m = δn + σ(G)`, the manuscript's
      -- `m = (3/2)n + (1/2)σ(G)` cleared of division.
      (2 * object.edgeCount =
        data.threshold * object.vertexCount +
          object.degreeSurplus data.threshold)
  | .activeSurplusFamily, object =>
      -- `lem:sparse-excess-port-extraction`, and the family statement of
      -- `lem:surviving-active-family`.
      ((object.excessPorts data.threshold).card =
          object.degreeSurplus data.threshold ∧
        ∀ pair : object.Vertex × object.Vertex,
          ∀ member : pair ∈ object.excessPorts data.threshold,
            data.threshold < object.degree pair.1 ∧
              object.degree pair.2 = data.threshold ∧
              (object.surplusPortOfMem member).shoulders.card =
                data.threshold - 1)
  | .sparsePortActivation, object =>
      -- `lem:sparse-port-activation`, clauses (a)--(d).
      (∀ pair : object.Vertex × object.Vertex,
        ∀ member : pair ∈ object.excessPorts data.threshold,
          ∀ left right : object.Vertex,
            (∀ vertex : object.Vertex,
              vertex ∈ (object.surplusPortOfMem member).shoulders ↔
                (vertex = left ∨ vertex = right)) →
            left ≠ right →
            Nonempty (Graph.FiniteObject.SurplusPort.PortReturn
                object pair.1 pair.2 left right) ∧
              (¬ object.graph.Adj left right →
                Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness
                  object data.LengthOK pair.2 left right)) ∧
              (object.graph.Adj left right →
                object.graph.Adj pair.2 left ∧
                  object.graph.Adj left right ∧
                  object.graph.Adj right pair.2))
  | .baselineSpineDemand, object =>
      -- `lem:incremental-skeleton-room` on the manuscript's own envelope, the
      -- same estimate spent at the object's own edge count,
      -- `lem:exact-cubic-baseline-budget`'s two-sided evaluation of `B₀(n)`,
      -- `def:baseline-spine-demand` at every declared coordinate family the
      -- branch may present, and `def:spine-lower-bound-deficits`' ordering of
      -- the three lower-bound packages.
      ((∀ increment : Nat,
          Graph.cubicBaselineEdgeCount object.vertexCount data.threshold +
              increment ≤ 2 * object.vertexCount - 2 →
          (object.vertexCount.choose 2).choose
              (Graph.cubicBaselineEdgeCount object.vertexCount data.threshold +
                increment) ≤
            (object.vertexCount.choose 2).choose
                (Graph.cubicBaselineEdgeCount object.vertexCount
                  data.threshold) *
              object.vertexCount ^ increment) ∧
        (Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
            object.edgeCount →
          Graph.skeletonBudget object ≤
            Graph.cubicBaselineBudget object.vertexCount data.threshold *
              object.vertexCount ^
                (object.edgeCount -
                  Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold)) ∧
        -- `lem:exact-cubic-baseline-budget`, both directions, with the
        -- logarithms cleared: `B₀(n) = (δ/2)n log₂ n + O(n)`.  The lower
        -- direction is stated on the manuscript's own hypothesis that the
        -- baseline stratum is nonempty.
        (Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
            (2 * object.vertexCount) ^
              Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ∧
          (2 * Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.vertexCount.choose 2 →
            (object.vertexCount - 1) ^
                Graph.cubicBaselineEdgeCount object.vertexCount
                  data.threshold ≤
              Graph.cubicBaselineBudget object.vertexCount data.threshold *
                (2 * (data.threshold + 1)) ^
                  Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold)) ∧
        -- `def:baseline-spine-demand` itself, at every family of declared
        -- target coordinates the branch may present and every lower-bound
        -- package it may realize.  `E_spine(n)` is the node's own output
        -- `spineDeficit`, not a constant carried in.
        (∀ Coordinate : Type u, ∀ family : Finset Coordinate,
          ∀ system : Core.TargetRank.QuotientSystem.{u, u + 1} Coordinate
              family,
            ∀ lowerBound : Nat,
              system.Survives ↑family →
              lowerBound ≤ family.card →
              Graph.IsBaselineSpineDemand system object.vertexCount
                data.threshold
                (Graph.spineDeficit object.vertexCount data.threshold
                  lowerBound)) ∧
        -- `def:spine-lower-bound-deficits`: the window-only package, the
        -- high-remainder-entropy package and the forced-curvature package are
        -- increasing at the registered rates, so their deficits decrease.
        (∀ packing remainder scaleCount : Nat,
          Graph.spineDeficit object.vertexCount data.threshold
              (Graph.curvaturePackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator data.curvatureCost) ≤
            Graph.spineDeficit object.vertexCount data.threshold
              (Graph.highEntropyPackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator) ∧
          Graph.spineDeficit object.vertexCount data.threshold
              (Graph.highEntropyPackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator) ≤
            Graph.spineDeficit object.vertexCount data.threshold
              (Graph.windowPackageBound data.windowRate packing scaleCount)))
  | .canonicalPairLedger, object =>
      -- `def:sparse-pair-response`, `def:surplus-blockers` instantiated,
      -- `def:canonical-blocker-ledger` and its no-overcount identity at that
      -- instantiation, `lem:sparse-pair-dependence-exit` with
      -- `lem:mixed-sparse-spine-dependence`,
      -- `prop:sparse-pair-independence-dichotomy`, the two entropy sandwiches
      -- and `cor:sparse-pair-entropy-saturation`.
      ((object.portPairSchedule data.threshold).card =
          (object.degreeSurplus data.threshold).choose 2 ∧
        (∀ Coordinate Chord : Type u,
          ∀ activation :
            Graph.FiniteObject.DemandActivation object Coordinate Chord,
            ((activation.chargedPairs data.threshold).card +
                  (activation.freePairs data.threshold).card =
                (object.portPairSchedule data.threshold).card ∧
              (activation.chargedPairs data.threshold).card =
                Graph.SameTokenBlockerRoles.canonicalBlockerOrder.toFinset.sum
                  (activation.multiplicity data.threshold) ∧
              ∀ pair : Finset (object.Vertex × object.Vertex),
                (∃ kind, activation.Blocks kind pair) ↔
                  (activation.blockers pair).Nonempty) ∧
            (∀ pair : Finset (object.Vertex × object.Vertex),
              ∀ support : Finset object.Vertex,
                activation.pairSupport pair = some support →
                  activation.pairSeed pair ⊆ support ∧
                    Graph.SupportComponents.Connected.ConnectedOn object support ∧
                    (∀ other : Finset object.Vertex,
                      activation.pairSeed pair ⊆ other →
                      Graph.SupportComponents.Connected.ConnectedOn object other →
                        support.card ≤ other.card) ∧
                    ∀ vertex : object.Vertex,
                      vertex ∈
                          Graph.FiniteObject.DemandActivation.pairBoundary object
                            support ↔
                        vertex ∈ support ∧
                          ∃ neighbor, object.graph.Adj vertex neighbor ∧
                            neighbor ∉ support) ∧
            ∀ family : Finset (Finset (object.Vertex × object.Vertex)),
              (activation.pairFamily family).card = family.card) ∧
        (∀ Coordinate : Type u, ∀ family : Finset Coordinate,
          ∀ coordinateSupport : Coordinate → Finset object.Vertex,
            Graph.SurvivesSparseExits
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object →
            (∀ support : Finset object.Vertex,
              ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object support) →
            (∀ attempt :
                Graph.AttemptedQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object family
                  coordinateSupport,
                ¬ Set.InjOn attempt.label ↑family →
                  (∃ left right, attempt.Identifies left right ∧
                      left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
                    (∃ left right, attempt.Identifies left right ∧
                      Graph.Response.TargetDefect
                        (Graph.HasCycleWithLength data.LengthOK) left right)) ∧
              Core.TargetRank.targetRank
                  (Graph.FiniteObject.declaredQuotientSystem
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object family
                    coordinateSupport) =
                family.card) ∧
        (∀ spineCount freeCount deficit : Nat,
          Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
            object.edgeCount →
          2 ^ (spineCount + freeCount) ≤ Graph.skeletonBudget object →
          Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
            2 ^ (spineCount + deficit) →
          2 ^ freeCount ≤
            2 ^ deficit *
              object.vertexCount ^
                (object.edgeCount -
                  Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold)) ∧
        (2 ^ (object.portPairSchedule data.threshold).card ≤
            Graph.skeletonBudget object →
          2 ^ ((object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget object))
  | .capacityTokenLedger, object =>
      -- `lem:primitive-carrier-supply` in both displayed forms, and
      -- `lem:token-ledger-no-overcount` with its totality clause.
      (((object.primitiveCarrier data.threshold).card =
            object.vertexCount + 2 * object.edgeCount +
              object.degreeSurplus data.threshold ∧
          (object.edgeCount + 2 ≤ 2 * object.vertexCount →
            (object.primitiveCarrier data.threshold).card ≤
              6 * object.vertexCount)) ∧
        ∀ Token : Type,
          ∀ tokenDecidableEq : DecidableEq Token,
          ∀ tokens : List Token,
            ∀ Eligible : Token →
                Finset (object.Vertex × object.Vertex) → Prop,
              ∀ decidable : ∀ token pair, Decidable (Eligible token pair),
                (object.chargedPairs data.threshold tokens Eligible
                    decidable).card =
                  (@List.toFinset _ tokenDecidableEq tokens).sum
                    (object.pairMultiplicity data.threshold tokenDecidableEq
                      tokens Eligible decidable) ∧
                ((∀ pair ∈ object.portPairSchedule data.threshold,
                    ∃ token ∈ tokens, Eligible token pair) →
                  object.chargedPairs data.threshold tokens Eligible decidable =
                    object.portPairSchedule data.threshold))
  | .roleFibrePartition, object =>
      -- `def:same-token-blocker-roles`' role-fibre partition.
      Graph.RoleFibrePartitionStatement object data.threshold
  | .fibrePressure, object =>
      -- `lem:capacity-token-high-load` with
      -- `cor:forced-homogeneous-same-token-scale`.
      Graph.FibrePressureStatement object data.threshold
  | .bottleneckClassification, object =>
      -- The three geometric class audits `[140]`, `[142]`, `[143]`.
      Graph.BottleneckClassificationStatement object data.threshold
  | .homogeneousBottleneck, object =>
      -- `cor:homogeneous-same-token-caps-close`.
      Graph.HomogeneousBottleneckStatement object data.threshold
  | .sparseSurplusSurvivor, object =>
      -- `def:named-surplus-exits`: none of the five conclusions occurs.
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
  | .activeSurplusDemands, object =>
      -- `def:active-surplus-demands` with `lem:surviving-active-family`.
      Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold

/-- Audit labels.  They are diagnostics; every routing and lookup decision
compares exact keys. -/
def label : Key → String
  | .selection => "selection"
  | .returnAvoidance => "returnAvoidance"
  | .noProperBaseline => "noProperBaseline"
  | .tightEndpoint => "tightEndpoint"
  | .slackIndependent => "slackIndependent"
  | .uncompressible => "uncompressible"
  | .maximalPacking => "maximalPacking"
  | .localAlgebra => "localAlgebra"
  | .surplusAbove => "surplusAbove"
  | .surplusAtOrBelow => "surplusAtOrBelow"
  | .barrierCap => "barrierCap"
  | .barrierOverflow => "barrierOverflow"
  | .densityCap => "densityCap"
  | .remainderNormalized => "remainderNormalized"
  | .boundaryDemand => "boundaryDemand"
  | .stubSupply => "stubSupply"
  | .wedgeSupply => "wedgeSupply"
  | .curvatureDemandFloor => "curvatureDemandFloor"
  | .curvatureTargetRank => "curvatureTargetRank"
  | .curvatureRankDrop => "curvatureRankDrop"
  | .curvatureFullRank => "curvatureFullRank"
  | .branchDependence => "branchDependence"
  | .contextUniversal => "contextUniversal"
  | .contextDefect => "contextDefect"
  | .atomCompression => "atomCompression"
  | .delocalizedSupport => "delocalizedSupport"
  | .properDelocalization => "properDelocalization"
  | .globalDelocalization => "globalDelocalization"
  | .repairIdentity => "repairIdentity"
  | .globalBarrier => "globalBarrier"
  | .coldCorridorState => "coldCorridorState"
  | .coldSameInterfaceTable => "coldSameInterfaceTable"
  | .coldGermRealized => "coldGermRealized"
  | .coldGermDistinguished => "coldGermDistinguished"
  | .coldGermSilent => "coldGermSilent"
  | .coldFailureCycle => "coldFailureCycle"
  | .coldFailureDefect => "coldFailureDefect"
  | .coldFailureCompression => "coldFailureCompression"
  | .coldFailureHandoff => "coldFailureHandoff"
  | .coldFailureRouting => "coldFailureRouting"
  | .coldHandoffTransfer => "coldHandoffTransfer"
  | .coldGermExtraction => "coldGermExtraction"
  | .coldBranchClosed => "coldBranchClosed"
  | .highCentreNormalForm => "highCentreNormalForm"
  | .typeBHeavyCentre => "typeBHeavyCentre"
  | .typeBDegreeFourCentres => "typeBDegreeFourCentres"
  | .typeBLocalDichotomy => "typeBLocalDichotomy"
  | .fanCertificateCap => "fanCertificateCap"
  | .fanCertificateMarked => "fanCertificateMarked"
  | .fanCertificateResidual => "fanCertificateResidual"
  | .typeBDegreeFourProfile => "typeBDegreeFourProfile"
  | .typeBHybridEntry => "typeBHybridEntry"
  | .typeBDirectCycle => "typeBDirectCycle"
  | .typeBDirectCycleFree => "typeBDirectCycleFree"
  | .typeBDisjointAssignment => "typeBDisjointAssignment"
  | .typeBOverlapObstruction => "typeBOverlapObstruction"
  | .typeBBridgeMass => "typeBBridgeMass"
  | .typeBExclusionCharge => "typeBExclusionCharge"
  | .typeBExcluded => "typeBExcluded"
  | .typeBExclusionResidual => "typeBExclusionResidual"
  | .windowPackageSeparated => "windowPackageSeparated"
  | .windowPackageCollided => "windowPackageCollided"
  | .forcedCurvatureCost => "forcedCurvatureCost"
  | .remainderEntropyHigh => "remainderEntropyHigh"
  | .remainderEntropyLow => "remainderEntropyLow"
  | .entropyPackageDemand => "entropyPackageDemand"
  | .entropyCapActive => "entropyCapActive"
  | .largeBudgetResidual => "largeBudgetResidual"
  | .largeOrderResidual => "largeOrderResidual"
  | .smallOrderResidual => "smallOrderResidual"
  | .netDeficiencyCap => "netDeficiencyCap"
  | .netChargeLocalization => "netChargeLocalization"
  | .netChargeNonNegative => "netChargeNonNegative"
  | .netChargeNegative => "netChargeNegative"
  | .windowJoinPressure => "windowJoinPressure"
  | .negativeSupport => "negativeSupport"
  | .typeALowSurplus => "typeALowSurplus"
  | .typeBHighSurplus => "typeBHighSurplus"
  | .typeAReceiverRouting => "typeAReceiverRouting"
  | .typeASaturatedReceiver => "typeASaturatedReceiver"
  | .typeAUnsaturatedReceivers => "typeAUnsaturatedReceivers"
  | .typeAVisibleEntry => "typeAVisibleEntry"
  | .typeAVisibleFirstExcess => "typeAVisibleFirstExcess"
  | .typeAExitOneReturn => "typeAExitOneReturn"
  | .typeAExitOneFree => "typeAExitOneFree"
  | .typeAExitTwoTheta => "typeAExitTwoTheta"
  | .typeAExitTwoFree => "typeAExitTwoFree"
  | .typeAExitThreeCollision => "typeAExitThreeCollision"
  | .typeAExitThreeFree => "typeAExitThreeFree"
  | .typeAExitFourPeel => "typeAExitFourPeel"
  | .typeAExitFourNoPeel => "typeAExitFourNoPeel"
  | .typeAPeeledCharge => "typeAPeeledCharge"
  | .typeAExitFiveCompression => "typeAExitFiveCompression"
  | .typeAExitFiveTraceLevel => "typeAExitFiveTraceLevel"
  | .typeAExitFour => "typeAExitFour"
  | .typeAExitFourFree => "typeAExitFourFree"
  | .typeAExitFive => "typeAExitFive"
  | .typeAExitFiveFree => "typeAExitFiveFree"
  | .typeAExitSix => "typeAExitSix"
  | .typeAExitSixFree => "typeAExitSixFree"
  | .typeAExitSixProper => "typeAExitSixProper"
  | .typeAExitSixGlobal => "typeAExitSixGlobal"
  | .route8Residual => "route8Residual"
  | .route8Free => "route8Free"
  | .route8Burden => "route8Burden"
  | .route8CarrierCore => "route8CarrierCore"
  | .route8Census => "route8Census"
  | .route8Descent => "route8Descent"
  | .route8Closed => "route8Closed"
  | .sparseSlackSurplus => "sparseSlackSurplus"
  | .activeSurplusFamily => "activeSurplusFamily"
  | .sparsePortActivation => "sparsePortActivation"
  | .baselineSpineDemand => "baselineSpineDemand"
  | .canonicalPairLedger => "canonicalPairLedger"
  | .capacityTokenLedger => "capacityTokenLedger"
  | .roleFibrePartition => "roleFibrePartition"
  | .fibrePressure => "fibrePressure"
  | .bottleneckClassification => "bottleneckClassification"
  | .homogeneousBottleneck => "homogeneousBottleneck"
  | .sparseSurplusSurvivor => "sparseSurplusSurvivor"
  | .activeSurplusDemands => "activeSurplusDemands"

/-! ### Label pins

Every audit label is the constructor's own name.  `label` is checked for
totality by the elaborator and the numbering below is pinned by `idx`, but
nothing forces the two to agree, so each pairing is stated here.  Each is a
constant-time `rfl`, and together they rule out a mistyped or duplicated
label. -/

section LabelPins
example : label .selection = "selection" := rfl
example : label .returnAvoidance = "returnAvoidance" := rfl
example : label .noProperBaseline = "noProperBaseline" := rfl
example : label .tightEndpoint = "tightEndpoint" := rfl
example : label .slackIndependent = "slackIndependent" := rfl
example : label .uncompressible = "uncompressible" := rfl
example : label .maximalPacking = "maximalPacking" := rfl
example : label .localAlgebra = "localAlgebra" := rfl
example : label .surplusAbove = "surplusAbove" := rfl
example : label .surplusAtOrBelow = "surplusAtOrBelow" := rfl
example : label .barrierCap = "barrierCap" := rfl
example : label .barrierOverflow = "barrierOverflow" := rfl
example : label .densityCap = "densityCap" := rfl
example : label .remainderNormalized = "remainderNormalized" := rfl
example : label .boundaryDemand = "boundaryDemand" := rfl
example : label .stubSupply = "stubSupply" := rfl
example : label .wedgeSupply = "wedgeSupply" := rfl
example : label .curvatureDemandFloor = "curvatureDemandFloor" := rfl
example : label .curvatureTargetRank = "curvatureTargetRank" := rfl
example : label .curvatureRankDrop = "curvatureRankDrop" := rfl
example : label .curvatureFullRank = "curvatureFullRank" := rfl
example : label .branchDependence = "branchDependence" := rfl
example : label .contextUniversal = "contextUniversal" := rfl
example : label .contextDefect = "contextDefect" := rfl
example : label .atomCompression = "atomCompression" := rfl
example : label .delocalizedSupport = "delocalizedSupport" := rfl
example : label .properDelocalization = "properDelocalization" := rfl
example : label .globalDelocalization = "globalDelocalization" := rfl
example : label .repairIdentity = "repairIdentity" := rfl
example : label .globalBarrier = "globalBarrier" := rfl
example : label .coldCorridorState = "coldCorridorState" := rfl
example : label .coldSameInterfaceTable = "coldSameInterfaceTable" := rfl
example : label .coldGermRealized = "coldGermRealized" := rfl
example : label .coldGermDistinguished = "coldGermDistinguished" := rfl
example : label .coldGermSilent = "coldGermSilent" := rfl
example : label .coldFailureCycle = "coldFailureCycle" := rfl
example : label .coldFailureDefect = "coldFailureDefect" := rfl
example : label .coldFailureCompression = "coldFailureCompression" := rfl
example : label .coldFailureHandoff = "coldFailureHandoff" := rfl
example : label .coldFailureRouting = "coldFailureRouting" := rfl
example : label .coldHandoffTransfer = "coldHandoffTransfer" := rfl
example : label .coldGermExtraction = "coldGermExtraction" := rfl
example : label .coldBranchClosed = "coldBranchClosed" := rfl
example : label .highCentreNormalForm = "highCentreNormalForm" := rfl
example : label .typeBHeavyCentre = "typeBHeavyCentre" := rfl
example : label .typeBDegreeFourCentres = "typeBDegreeFourCentres" := rfl
example : label .typeBLocalDichotomy = "typeBLocalDichotomy" := rfl
example : label .fanCertificateCap = "fanCertificateCap" := rfl
example : label .fanCertificateMarked = "fanCertificateMarked" := rfl
example : label .fanCertificateResidual = "fanCertificateResidual" := rfl
example : label .typeBDegreeFourProfile = "typeBDegreeFourProfile" := rfl
example : label .typeBHybridEntry = "typeBHybridEntry" := rfl
example : label .typeBDirectCycle = "typeBDirectCycle" := rfl
example : label .typeBDirectCycleFree = "typeBDirectCycleFree" := rfl
example : label .typeBDisjointAssignment = "typeBDisjointAssignment" := rfl
example : label .typeBOverlapObstruction = "typeBOverlapObstruction" := rfl
example : label .typeBBridgeMass = "typeBBridgeMass" := rfl
example : label .typeBExclusionCharge = "typeBExclusionCharge" := rfl
example : label .typeBExcluded = "typeBExcluded" := rfl
example : label .typeBExclusionResidual = "typeBExclusionResidual" := rfl
example : label .windowPackageSeparated = "windowPackageSeparated" := rfl
example : label .windowPackageCollided = "windowPackageCollided" := rfl
example : label .forcedCurvatureCost = "forcedCurvatureCost" := rfl
example : label .remainderEntropyHigh = "remainderEntropyHigh" := rfl
example : label .remainderEntropyLow = "remainderEntropyLow" := rfl
example : label .entropyPackageDemand = "entropyPackageDemand" := rfl
example : label .entropyCapActive = "entropyCapActive" := rfl
example : label .largeBudgetResidual = "largeBudgetResidual" := rfl
example : label .largeOrderResidual = "largeOrderResidual" := rfl
example : label .smallOrderResidual = "smallOrderResidual" := rfl
example : label .netDeficiencyCap = "netDeficiencyCap" := rfl
example : label .netChargeLocalization = "netChargeLocalization" := rfl
example : label .netChargeNonNegative = "netChargeNonNegative" := rfl
example : label .netChargeNegative = "netChargeNegative" := rfl
example : label .windowJoinPressure = "windowJoinPressure" := rfl
example : label .negativeSupport = "negativeSupport" := rfl
example : label .typeALowSurplus = "typeALowSurplus" := rfl
example : label .typeBHighSurplus = "typeBHighSurplus" := rfl
example : label .typeAReceiverRouting = "typeAReceiverRouting" := rfl
example : label .typeASaturatedReceiver = "typeASaturatedReceiver" := rfl
example : label .typeAUnsaturatedReceivers = "typeAUnsaturatedReceivers" := rfl
example : label .typeAVisibleEntry = "typeAVisibleEntry" := rfl
example : label .typeAVisibleFirstExcess = "typeAVisibleFirstExcess" := rfl
example : label .typeAExitOneReturn = "typeAExitOneReturn" := rfl
example : label .typeAExitOneFree = "typeAExitOneFree" := rfl
example : label .typeAExitTwoTheta = "typeAExitTwoTheta" := rfl
example : label .typeAExitTwoFree = "typeAExitTwoFree" := rfl
example : label .typeAExitThreeCollision = "typeAExitThreeCollision" := rfl
example : label .typeAExitThreeFree = "typeAExitThreeFree" := rfl
example : label .typeAExitFourPeel = "typeAExitFourPeel" := rfl
example : label .typeAExitFourNoPeel = "typeAExitFourNoPeel" := rfl
example : label .typeAPeeledCharge = "typeAPeeledCharge" := rfl
example : label .typeAExitFiveCompression = "typeAExitFiveCompression" := rfl
example : label .typeAExitFiveTraceLevel = "typeAExitFiveTraceLevel" := rfl
example : label .typeAExitFour = "typeAExitFour" := rfl
example : label .typeAExitFourFree = "typeAExitFourFree" := rfl
example : label .typeAExitFive = "typeAExitFive" := rfl
example : label .typeAExitFiveFree = "typeAExitFiveFree" := rfl
example : label .typeAExitSix = "typeAExitSix" := rfl
example : label .typeAExitSixFree = "typeAExitSixFree" := rfl
example : label .typeAExitSixProper = "typeAExitSixProper" := rfl
example : label .typeAExitSixGlobal = "typeAExitSixGlobal" := rfl
example : label .route8Residual = "route8Residual" := rfl
example : label .route8Free = "route8Free" := rfl
example : label .route8Burden = "route8Burden" := rfl
example : label .route8CarrierCore = "route8CarrierCore" := rfl
example : label .route8Census = "route8Census" := rfl
example : label .route8Descent = "route8Descent" := rfl
example : label .route8Closed = "route8Closed" := rfl
example : label .sparseSlackSurplus = "sparseSlackSurplus" := rfl
example : label .activeSurplusFamily = "activeSurplusFamily" := rfl
example : label .sparsePortActivation = "sparsePortActivation" := rfl
example : label .baselineSpineDemand = "baselineSpineDemand" := rfl
example : label .canonicalPairLedger = "canonicalPairLedger" := rfl
example : label .capacityTokenLedger = "capacityTokenLedger" := rfl
example : label .roleFibrePartition = "roleFibrePartition" := rfl
example : label .fibrePressure = "fibrePressure" := rfl
example : label .bottleneckClassification = "bottleneckClassification" := rfl
example : label .homogeneousBottleneck = "homogeneousBottleneck" := rfl
example : label .sparseSurplusSurvivor = "sparseSurplusSurvivor" := rfl
example : label .activeSurplusDemands = "activeSurplusDemands" := rfl
end LabelPins

/-- The value schema at a residual: the object-level statement, read at the
residual's own object. -/
def Value (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key)
    (input : Core.Strategy.ProblemInput
      (problem BranchState Presentation presentation data)) : Type :=
  PLift (Holds BranchState Presentation presentation data k input.object)

/-- The audit index of a key.  It is written out rather than taken from
`Key.ctorIdx` so that inserting or reordering a constructor cannot silently
renumber the audit names an earlier run emitted. -/
def idx : Key → Nat
  | .selection => 0
  | .returnAvoidance => 1
  | .noProperBaseline => 2
  | .tightEndpoint => 3
  | .slackIndependent => 4
  | .uncompressible => 5
  | .maximalPacking => 6
  | .localAlgebra => 7
  | .surplusAbove => 8
  | .surplusAtOrBelow => 9
  | .barrierCap => 10
  | .barrierOverflow => 11
  | .densityCap => 12
  | .remainderNormalized => 13
  | .boundaryDemand => 14
  | .stubSupply => 15
  | .wedgeSupply => 16
  | .curvatureDemandFloor => 17
  | .curvatureTargetRank => 18
  | .curvatureRankDrop => 19
  | .curvatureFullRank => 20
  | .branchDependence => 21
  | .contextUniversal => 22
  | .contextDefect => 23
  | .atomCompression => 24
  | .delocalizedSupport => 25
  | .properDelocalization => 26
  | .globalDelocalization => 27
  | .repairIdentity => 28
  | .globalBarrier => 29
  | .coldCorridorState => 30
  | .coldSameInterfaceTable => 31
  | .coldGermRealized => 32
  | .coldGermDistinguished => 33
  | .coldGermSilent => 34
  | .windowPackageSeparated => 35
  | .windowPackageCollided => 36
  | .forcedCurvatureCost => 37
  | .remainderEntropyHigh => 38
  | .remainderEntropyLow => 39
  | .entropyPackageDemand => 40
  | .entropyCapActive => 41
  | .largeBudgetResidual => 42
  | .largeOrderResidual => 43
  | .smallOrderResidual => 44
  | .netDeficiencyCap => 45
  | .netChargeLocalization => 46
  | .netChargeNonNegative => 47
  | .netChargeNegative => 48
  | .windowJoinPressure => 49
  | .negativeSupport => 50
  | .typeALowSurplus => 51
  | .typeBHighSurplus => 52
  | .typeAReceiverRouting => 53
  | .typeASaturatedReceiver => 54
  | .typeAUnsaturatedReceivers => 55
  | .typeAVisibleEntry => 56
  | .typeAVisibleFirstExcess => 57
  | .typeAExitOneReturn => 58
  | .typeAExitOneFree => 59
  | .typeAExitTwoTheta => 60
  | .typeAExitTwoFree => 61
  | .typeAExitThreeCollision => 62
  | .typeAExitThreeFree => 63
  | .coldFailureCycle => 64
  | .coldFailureDefect => 65
  | .coldFailureCompression => 66
  | .coldFailureHandoff => 67
  | .coldFailureRouting => 68
  | .coldHandoffTransfer => 69
  | .coldGermExtraction => 70
  | .coldBranchClosed => 71
  | .highCentreNormalForm => 72
  | .typeBHeavyCentre => 73
  | .typeBDegreeFourCentres => 74
  | .typeBLocalDichotomy => 75
  | .fanCertificateCap => 76
  | .fanCertificateMarked => 77
  | .fanCertificateResidual => 78
  | .typeBDegreeFourProfile => 79
  | .typeBHybridEntry => 80
  | .typeBDirectCycle => 81
  | .typeBDirectCycleFree => 82
  | .typeBDisjointAssignment => 83
  | .typeBOverlapObstruction => 84
  | .typeBBridgeMass => 85
  | .typeBExclusionCharge => 86
  | .typeBExcluded => 87
  | .typeBExclusionResidual => 88
  | .typeAExitFourPeel => 89
  | .typeAExitFourNoPeel => 90
  | .typeAPeeledCharge => 91
  | .typeAExitFiveCompression => 92
  | .typeAExitFiveTraceLevel => 93
  | .typeAExitFour => 94
  | .typeAExitFourFree => 95
  | .typeAExitFive => 96
  | .typeAExitFiveFree => 97
  | .typeAExitSix => 98
  | .typeAExitSixFree => 99
  | .typeAExitSixProper => 100
  | .typeAExitSixGlobal => 101
  | .route8Residual => 102
  | .route8Free => 103
  | .route8Burden => 104
  | .route8CarrierCore => 105
  | .route8Census => 106
  | .route8Descent => 107
  | .route8Closed => 108
  | .sparseSlackSurplus => 109
  | .activeSurplusFamily => 110
  | .sparsePortActivation => 111
  | .baselineSpineDemand => 112
  | .canonicalPairLedger => 113
  | .capacityTokenLedger => 114
  | .roleFibrePartition => 115
  | .fibrePressure => 116
  | .bottleneckClassification => 117
  | .homogeneousBottleneck => 118
  | .sparseSurplusSurvivor => 119
  | .activeSurplusDemands => 120

/-- Left inverse of `idx`.  Writing it out is also what checks the numbering:
two keys sharing an index would make `ofIdx_idx` unprovable. -/
def ofIdx : Nat → Key
  | 0 => .selection
  | 1 => .returnAvoidance
  | 2 => .noProperBaseline
  | 3 => .tightEndpoint
  | 4 => .slackIndependent
  | 5 => .uncompressible
  | 6 => .maximalPacking
  | 7 => .localAlgebra
  | 8 => .surplusAbove
  | 9 => .surplusAtOrBelow
  | 10 => .barrierCap
  | 11 => .barrierOverflow
  | 12 => .densityCap
  | 13 => .remainderNormalized
  | 14 => .boundaryDemand
  | 15 => .stubSupply
  | 16 => .wedgeSupply
  | 17 => .curvatureDemandFloor
  | 18 => .curvatureTargetRank
  | 19 => .curvatureRankDrop
  | 20 => .curvatureFullRank
  | 21 => .branchDependence
  | 22 => .contextUniversal
  | 23 => .contextDefect
  | 24 => .atomCompression
  | 25 => .delocalizedSupport
  | 26 => .properDelocalization
  | 27 => .globalDelocalization
  | 28 => .repairIdentity
  | 29 => .globalBarrier
  | 30 => .coldCorridorState
  | 31 => .coldSameInterfaceTable
  | 32 => .coldGermRealized
  | 33 => .coldGermDistinguished
  | 34 => .coldGermSilent
  | 35 => .windowPackageSeparated
  | 36 => .windowPackageCollided
  | 37 => .forcedCurvatureCost
  | 38 => .remainderEntropyHigh
  | 39 => .remainderEntropyLow
  | 40 => .entropyPackageDemand
  | 41 => .entropyCapActive
  | 42 => .largeBudgetResidual
  | 43 => .largeOrderResidual
  | 44 => .smallOrderResidual
  | 45 => .netDeficiencyCap
  | 46 => .netChargeLocalization
  | 47 => .netChargeNonNegative
  | 48 => .netChargeNegative
  | 49 => .windowJoinPressure
  | 50 => .negativeSupport
  | 51 => .typeALowSurplus
  | 52 => .typeBHighSurplus
  | 53 => .typeAReceiverRouting
  | 54 => .typeASaturatedReceiver
  | 55 => .typeAUnsaturatedReceivers
  | 56 => .typeAVisibleEntry
  | 57 => .typeAVisibleFirstExcess
  | 58 => .typeAExitOneReturn
  | 59 => .typeAExitOneFree
  | 60 => .typeAExitTwoTheta
  | 61 => .typeAExitTwoFree
  | 62 => .typeAExitThreeCollision
  | 63 => .typeAExitThreeFree
  | 64 => .coldFailureCycle
  | 65 => .coldFailureDefect
  | 66 => .coldFailureCompression
  | 67 => .coldFailureHandoff
  | 68 => .coldFailureRouting
  | 69 => .coldHandoffTransfer
  | 70 => .coldGermExtraction
  | 71 => .coldBranchClosed
  | 72 => .highCentreNormalForm
  | 73 => .typeBHeavyCentre
  | 74 => .typeBDegreeFourCentres
  | 75 => .typeBLocalDichotomy
  | 76 => .fanCertificateCap
  | 77 => .fanCertificateMarked
  | 78 => .fanCertificateResidual
  | 79 => .typeBDegreeFourProfile
  | 80 => .typeBHybridEntry
  | 81 => .typeBDirectCycle
  | 82 => .typeBDirectCycleFree
  | 83 => .typeBDisjointAssignment
  | 84 => .typeBOverlapObstruction
  | 85 => .typeBBridgeMass
  | 86 => .typeBExclusionCharge
  | 87 => .typeBExcluded
  | 88 => .typeBExclusionResidual
  | 89 => .typeAExitFourPeel
  | 90 => .typeAExitFourNoPeel
  | 91 => .typeAPeeledCharge
  | 92 => .typeAExitFiveCompression
  | 93 => .typeAExitFiveTraceLevel
  | 94 => .typeAExitFour
  | 95 => .typeAExitFourFree
  | 96 => .typeAExitFive
  | 97 => .typeAExitFiveFree
  | 98 => .typeAExitSix
  | 99 => .typeAExitSixFree
  | 100 => .typeAExitSixProper
  | 101 => .typeAExitSixGlobal
  | 102 => .route8Residual
  | 103 => .route8Free
  | 104 => .route8Burden
  | 105 => .route8CarrierCore
  | 106 => .route8Census
  | 107 => .route8Descent
  | 108 => .route8Closed
  | 109 => .sparseSlackSurplus
  | 110 => .activeSurplusFamily
  | 111 => .sparsePortActivation
  | 112 => .baselineSpineDemand
  | 113 => .canonicalPairLedger
  | 114 => .capacityTokenLedger
  | 115 => .roleFibrePartition
  | 116 => .fibrePressure
  | 117 => .bottleneckClassification
  | 118 => .homogeneousBottleneck
  | 119 => .sparseSurplusSurvivor
  | 120 => .activeSurplusDemands
  | _ => .selection

theorem ofIdx_idx (k : Key) : ofIdx (idx k) = k := by
  cases k <;> rfl

theorem idx_injective : Function.Injective idx :=
  Function.LeftInverse.injective ofIdx_idx

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys.  The name carries the key's audit index as its final
component, so distinctness is inherited from `idx_injective` instead of being
re-derived by a pairwise comparison of the 121 audit labels. -/
def name : Key → Lean.Name
  | .selection => .num (.str `Hypostructure.Graph.Strategy.Spine "selection") 0
  | .returnAvoidance =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "returnAvoidance") 1
  | .noProperBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "noProperBaseline") 2
  | .tightEndpoint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "tightEndpoint") 3
  | .slackIndependent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "slackIndependent") 4
  | .uncompressible =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "uncompressible") 5
  | .maximalPacking =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "maximalPacking") 6
  | .localAlgebra =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "localAlgebra") 7
  | .surplusAbove =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "surplusAbove") 8
  | .surplusAtOrBelow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "surplusAtOrBelow") 9
  | .barrierCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "barrierCap") 10
  | .barrierOverflow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "barrierOverflow") 11
  | .densityCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "densityCap") 12
  | .remainderNormalized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderNormalized") 13
  | .boundaryDemand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "boundaryDemand") 14
  | .stubSupply =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "stubSupply") 15
  | .wedgeSupply =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "wedgeSupply") 16
  | .curvatureDemandFloor =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "curvatureDemandFloor") 17
  | .curvatureTargetRank =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "curvatureTargetRank") 18
  | .curvatureRankDrop =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "curvatureRankDrop") 19
  | .curvatureFullRank =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "curvatureFullRank") 20
  | .branchDependence =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "branchDependence") 21
  | .contextUniversal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "contextUniversal") 22
  | .contextDefect =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "contextDefect") 23
  | .atomCompression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "atomCompression") 24
  | .delocalizedSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "delocalizedSupport") 25
  | .properDelocalization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "properDelocalization") 26
  | .globalDelocalization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "globalDelocalization") 27
  | .repairIdentity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "repairIdentity") 28
  | .globalBarrier =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "globalBarrier") 29
  | .coldCorridorState =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCorridorState") 30
  | .coldSameInterfaceTable =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldSameInterfaceTable") 31
  | .coldGermRealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermRealized") 32
  | .coldGermDistinguished =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermDistinguished") 33
  | .coldGermSilent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermSilent") 34
  | .windowPackageSeparated =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "windowPackageSeparated") 35
  | .windowPackageCollided =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowPackageCollided") 36
  | .forcedCurvatureCost =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "forcedCurvatureCost") 37
  | .remainderEntropyHigh =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderEntropyHigh") 38
  | .remainderEntropyLow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderEntropyLow") 39
  | .entropyPackageDemand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyPackageDemand") 40
  | .entropyCapActive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyCapActive") 41
  | .largeBudgetResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "largeBudgetResidual") 42
  | .largeOrderResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "largeOrderResidual") 43
  | .smallOrderResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "smallOrderResidual") 44
  | .netDeficiencyCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netDeficiencyCap") 45
  | .netChargeLocalization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeLocalization") 46
  | .netChargeNonNegative =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeNonNegative") 47
  | .netChargeNegative =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeNegative") 48
  | .windowJoinPressure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowJoinPressure") 49
  | .negativeSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "negativeSupport") 50
  | .typeALowSurplus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeALowSurplus") 51
  | .typeBHighSurplus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHighSurplus") 52
  | .typeAReceiverRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAReceiverRouting") 53
  | .typeASaturatedReceiver =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedReceiver") 54
  | .typeAUnsaturatedReceivers =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAUnsaturatedReceivers") 55
  | .typeAVisibleEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAVisibleEntry") 56
  | .typeAVisibleFirstExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAVisibleFirstExcess") 57
  | .typeAExitOneReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitOneReturn") 58
  | .typeAExitOneFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitOneFree") 59
  | .typeAExitTwoTheta =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitTwoTheta") 60
  | .typeAExitTwoFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitTwoFree") 61
  | .typeAExitThreeCollision =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitThreeCollision") 62
  | .typeAExitThreeFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitThreeFree") 63
  | .coldFailureCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureCycle") 64
  | .coldFailureDefect =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureDefect") 65
  | .coldFailureCompression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldFailureCompression") 66
  | .coldFailureHandoff =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureHandoff") 67
  | .coldFailureRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureRouting") 68
  | .coldHandoffTransfer =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldHandoffTransfer") 69
  | .coldGermExtraction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermExtraction") 70
  | .coldBranchClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldBranchClosed") 71
  | .highCentreNormalForm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highCentreNormalForm") 72
  | .typeBHeavyCentre =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHeavyCentre") 73
  | .typeBDegreeFourCentres =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDegreeFourCentres") 74
  | .typeBLocalDichotomy =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBLocalDichotomy") 75
  | .fanCertificateCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fanCertificateCap") 76
  | .fanCertificateMarked =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fanCertificateMarked") 77
  | .fanCertificateResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "fanCertificateResidual") 78
  | .typeBDegreeFourProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDegreeFourProfile") 79
  | .typeBHybridEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHybridEntry") 80
  | .typeBDirectCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBDirectCycle") 81
  | .typeBDirectCycleFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBDirectCycleFree") 82
  | .typeBDisjointAssignment =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDisjointAssignment") 83
  | .typeBOverlapObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBOverlapObstruction") 84
  | .typeBBridgeMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBBridgeMass") 85
  | .typeBExclusionCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBExclusionCharge") 86
  | .typeBExcluded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBExcluded") 87
  | .typeBExclusionResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBExclusionResidual") 88
  | .typeAExitFourPeel =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFourPeel") 89
  | .typeAExitFourNoPeel =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFourNoPeel") 90
  | .typeAPeeledCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledCharge") 91
  | .typeAExitFiveCompression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFiveCompression") 92
  | .typeAExitFiveTraceLevel =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFiveTraceLevel") 93
  | .typeAExitFour =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFour") 94
  | .typeAExitFourFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFourFree") 95
  | .typeAExitFive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFive") 96
  | .typeAExitFiveFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFiveFree") 97
  | .typeAExitSix =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSix") 98
  | .typeAExitSixFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSixFree") 99
  | .typeAExitSixProper =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSixProper") 100
  | .typeAExitSixGlobal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSixGlobal") 101
  | .route8Residual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Residual") 102
  | .route8Free =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Free") 103
  | .route8Burden =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Burden") 104
  | .route8CarrierCore =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8CarrierCore") 105
  | .route8Census =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Census") 106
  | .route8Descent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Descent") 107
  | .route8Closed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Closed") 108
  | .sparseSlackSurplus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sparseSlackSurplus") 109
  | .activeSurplusFamily =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "activeSurplusFamily") 110
  | .sparsePortActivation =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sparsePortActivation") 111
  | .baselineSpineDemand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "baselineSpineDemand") 112
  | .canonicalPairLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalPairLedger") 113
  | .capacityTokenLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "capacityTokenLedger") 114
  | .roleFibrePartition =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "roleFibrePartition") 115
  | .fibrePressure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fibrePressure") 116
  | .bottleneckClassification =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "bottleneckClassification") 117
  | .homogeneousBottleneck =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "homogeneousBottleneck") 118
  | .sparseSurplusSurvivor =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sparseSurplusSurvivor") 119
  | .activeSurplusDemands =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "activeSurplusDemands") 120

/-- The written-out names agree with `label` and `idx`.  `name` is spelled out
so that reducing it in a downstream audit proof costs one unfolding rather
than three; this lemma is what ties the spelling back to the two components,
and it is 121 constant-time `rfl`s. -/
theorem name_eq (k : Key) :
    name k
      = .num (.str `Hypostructure.Graph.Strategy.Spine (label k)) (idx k) := by
  cases k <;> rfl

theorem name_injective : Function.Injective name := fun a b same =>
  idx_injective (by
    rw [name_eq a, name_eq b] at same
    injection same)


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
  -- Spine names end in a numeric component, the reserved closure name in a
  -- string component, so they differ without inspecting the key.
  name_ne_closure := fun key h => by
    rw [name_eq key] at h
    exact Lean.Name.noConfusion h
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
