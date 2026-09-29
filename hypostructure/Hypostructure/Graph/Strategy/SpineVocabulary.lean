import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Graph.Statements.Parameters
import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.BranchD
import Hypostructure.Graph.Statements.TypeA
import Hypostructure.Graph.Statements.TypeB
import Hypostructure.Graph.Statements.RouteEightPinned
import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Statements.TypeBSublinearCanonical
import Hypostructure.Graph.Statements.TypeBSublinearGaps
import Hypostructure.Graph.Statements.TypeBSublinearFlow
import Hypostructure.Graph.Statements.SurplusPairRouting
import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.Statements.ColdGerm
import Hypostructure.Graph.Statements.ColdMarkedGerm
import Hypostructure.Graph.Statements.SpineDominantType
import Hypostructure.Graph.Statements.ColdResiduals
import Hypostructure.Graph.Statements.DensityOrder
import Hypostructure.Graph.Statements.Route8RateFailsJoin
import Hypostructure.Graph.Statements.Route8RateFailsFlow
import Hypostructure.Graph.Statements.Route8RateFailsAccounting
import Hypostructure.Graph.Statements.Route8RateFailsRoute
import Hypostructure.Graph.Statements.Route8WindowRPath
import Hypostructure.Graph.Statements.Route8WindowPieceLengths
import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.Statements.SparseExitReadings
import Hypostructure.Graph.Statements.SwitchForcedPaths
import Hypostructure.Graph.Statements.SameTokenPair
import Hypostructure.Graph.Statements.SameTokenSwap
import Hypostructure.Graph.Statements.CycleCounting
import Hypostructure.Graph.Statements.LocalRigidity
import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.Statements.HubLinks
import Hypostructure.Graph.Statements.PairArms
import Hypostructure.Graph.Statements.BlockedFailureG
import Hypostructure.Graph.Statements.BlockedOverlapG
import Hypostructure.Graph.Statements.PairCorrelation
import Hypostructure.Graph.Statements.Route8QuotientSize
import Hypostructure.Graph.Statements.PairHandoffSupport
import Hypostructure.Graph.Statements.PairHandoffFacts
import Hypostructure.Graph.Statements.StubDeficit

/-!
# The minimum-degree cycle spine: fact vocabulary

The entry spine of a minimum-degree cycle problem proves a fixed sequence of
theorems about one selected minimal counterexample.  This module names them as
the closed semantic vocabulary of that residual domain, so each is a fact of
the one canonical `ExactLedger` rather than a payload, summary, or wrapper.

The baseline threshold, target predicate, window order, and finite constants
are supplied by the registered presentation.  A presentation reaching the
two-strand node also certifies that its target predicate is exactly the dyadic
lengths; no row spells an application numeral.
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
structure Data extends Parameters where
  /-- The paper's registered cubic baseline. -/
  threshold_eq_three : threshold = 3
  /-- Stirling's `⌈e⌉` against the registered baseline; see the note above. -/
  three_le_threshold : 3 ≤ threshold
  /-- The paper's target is exactly the dyadic lengths.  The two-strand row
  reads this presentation identity when it turns either computed closing
  length into an accepted ambient cycle. -/
  lengthOK_iff_powerOfTwo : ∀ length,
    LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length
  /-- The registered executable census of the legal-label carrier, restricted
  to the seven sizes displayed by `lem:labels`.  This is a field of the one
  problem presentation, not branch state or a transported proof package. -/
  labelCount : (Graph.WindowCurvature.Labels windowOrder).card = 399
  labelSizeDistribution :
    (Graph.WindowCurvature.sizeDistribution windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2]
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
  /-- The discharge denominator and visible-return overload threshold are the
  paper's literal value four.  This is registered once by the presentation and
  published on the exact ledger with the cubic baseline; local exit rows read
  it from that owned fact rather than taking a caller premise. -/
  dischargeScale_eq_four : dischargeScale = 4
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
  /-- **The join comparison `lem:capacity-token-supply` spends.**

  The manuscript's `|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)` is bounded by
  `|𝔘_sp(G)| + 2n + σ(G)` because `15 ≤ 2·13`: the internal window mass
  `δ·order − 2(order − 1)` per packed window is at most `2·order` per window, and
  `order·p ≤ n` because the packed windows are vertex-disjoint.  Cleared of the
  `−2(order−1)`, that is this comparison between the two registered numbers.

  Registering it here is the analogue of `fanCapSlack` and
  `highCentreDeficitSlack`: it relates the registered baseline to the registered
  window order and nothing else, so it is a property of the presentation rather
  than of any object.  A presentation whose window order is too short for its
  baseline does not reach the capacity-token ledger. -/
  joinSlack : threshold * windowOrder + 2 ≤ 4 * windowOrder
  /-- The registered number is exactly the cardinality of the paper's routed
  seven-coordinate label alphabet. -/
  routingLabelBound_eq :
    routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel
        (Fin threshold → Fin threshold)
        (Graph.WindowCurvature.Label windowOrder))
  /-- The problem's declared same-token role alphabet covers the universal
  coefficient left by the generic quadratic absorption estimate.  This is a
  presentation check: the framework neither writes nor reconstructs a numeric
  lower bound for the problem's role alphabet. -/
  roleSafety :
    Graph.TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound)
  /-- The registered deficit scale covers the explicit binomial loss used by
  node `[129]`'s realizable baseline family. -/
  baselineDeficitSafety :
    Graph.baselineDeficitCoefficient threshold ≤ surplusScale
  /-- The certified table's row carrier names exactly the manuscript's legal
  attachment labels at the registered induced-window order. -/
  windowBarrierLabel : Fin windowBarrier.size →
    Graph.WindowCurvature.Label windowOrder
  windowBarrierLabel_mem : ∀ index,
    windowBarrierLabel index ∈ Graph.WindowCurvature.Labels windowOrder
  windowBarrierLabel_injective : Function.Injective windowBarrierLabel
  windowBarrierLabel_surjective : ∀ label ∈
      Graph.WindowCurvature.Labels windowOrder,
    ∃ index, windowBarrierLabel index = label
  /-- The three relation rows used by every registered barrier pair are the
  manuscript's safety relations, not merely an unrelated Boolean table. -/
  windowBarrier_left_semantic : ∀ row source target,
    (windowBarrier.profile.row
      (windowBarrier.table.counts.leftLength row) source).getLsb target =
      decide (Graph.WindowCurvature.Safe
        (windowBarrier.table.counts.leftLength row)
        (windowBarrierLabel source) (windowBarrierLabel target))
  windowBarrier_right_semantic : ∀ row source target,
    (windowBarrier.profile.row
      (windowBarrier.table.counts.rightLength row) source).getLsb target =
      decide (Graph.WindowCurvature.Safe
        (windowBarrier.table.counts.rightLength row)
        (windowBarrierLabel source) (windowBarrierLabel target))
  windowBarrier_sum_semantic : ∀ row source target,
    (windowBarrier.profile.row
      (windowBarrier.table.counts.leftLength row +
        windowBarrier.table.counts.rightLength row) source).getLsb target =
      decide (Graph.WindowCurvature.Safe
        (windowBarrier.table.counts.leftLength row +
          windowBarrier.table.counts.rightLength row)
        (windowBarrierLabel source) (windowBarrierLabel target))
  /-- The registered rate is exactly the aggregate rate of the public table. -/
  windowRate_eq_barrier :
    windowRate = windowBarrier.binaryRateFloor
  /-- The selected scales are among the object's own: the discard only loses
  scales, it never invents them. -/
  separatedScaleCount_le : ∀ size : Nat, separatedScaleCount size ≤ Nat.log2 size
  /-- The paper uses the full dyadic scale family in its normalized density
  comparison. -/
  separatedScaleCount_eq_log2 : ∀ size : Nat, separatedScaleCount size = Nat.log2 size
  /-- The finite numerical form of the strict inequality `τ_win < 1/4`. -/
  netCapRateSlack :
    Graph.FiniteObject.netCapWindowCost threshold dischargeScale windowOrder * threshold <
      2 * windowRate
  curvatureCost_eq_barrierRow :
    letI := windowBarrier.indexFintype
    curvatureCost =
      Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
        windowBarrier.table curvatureBarrierRow
  entropyDenominator_pos : 0 < entropyDenominator
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
  /-- **The centre-deletion clearing of the same estimate.**

  `lem:typeB-bridge-with-route8-core` assembled by deleting the assigned
  centres and discharging the deleted region with the silence-free staged
  count pays each centre `1 + s·δ` for its own vertex and its transferred
  incidences plus `2s` per surplus unit; at the registered values this is
  `21 ≤ 32`.  Registered exactly as `bridgeMassSlack` is: arithmetic of the
  presentation, discharged once. -/
  bridgeDeletionSlack :
    1 + dischargeScale * threshold + 2 * dischargeScale ≤
      bridgeMassFactor * dischargeScale

/-- The derived alphabet is inhabited because every admitted presentation has
positive baseline degree. -/
@[reducible] def Data.boundaryProfileInhabited (data : Data.{u}) :
    Inhabited data.BoundaryProfile := by
  have positive : 0 < data.threshold := lt_of_lt_of_le (by omega) data.three_le_threshold
  exact ⟨fun _ => ⟨0, positive⟩⟩

/-- The routing alphabet's inhabitedness makes `L_geom ≥ 2`; hence its
homogeneous cap already absorbs the safety coefficient derived by the generic
quadratic estimate. -/
theorem Data.quadraticSafetyScale_le_twiceAdditive (data : Data.{u}) :
    Graph.TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * data.homogeneousCap) := by
  letI := data.boundaryProfileFintype
  letI := data.boundaryProfileInhabited
  let Label := Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
    (Graph.WindowCurvature.Label data.windowOrder)
  letI : Nonempty Label := ⟨
    (⟨Graph.SameTokenBlockerRoles.BlockerKind.sharedDeclaredSupport,
        Graph.SameTokenBlockerRoles.TokenSubtype.boundaryWindow⟩,
      .boundaryWindow, 0, (.openPort, .openPort),
      (default, default), ∅, false)⟩
  have labelPositive : 0 < data.routingLabelBound := by
    rw [data.routingLabelBound_eq]
    exact Fintype.card_pos
  have patternTwo : 2 ≤
      Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound := by
    simp only [Graph.SameTokenBlockerRoles.geometricPatternBound]
    omega
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 *
      (Graph.SameTokenBlockerRoles.sameTokenRoleBound *
        ((Graph.SameTokenBlockerRoles.geometricPatternBound
              data.routingLabelBound - 1) *
          (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
              data.routingLabelBound - 3))))
  have first : 1 ≤ Graph.SameTokenBlockerRoles.geometricPatternBound
      data.routingLabelBound - 1 := by omega
  have second : 1 ≤ 2 * Graph.SameTokenBlockerRoles.geometricPatternBound
      data.routingLabelBound - 3 := by
    omega
  have roleLeCap : Graph.SameTokenBlockerRoles.sameTokenRoleBound ≤
      Graph.SameTokenBlockerRoles.sameTokenRoleBound *
        ((Graph.SameTokenBlockerRoles.geometricPatternBound
              data.routingLabelBound - 1) *
          (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
              data.routingLabelBound - 3)) := by
    simpa [Nat.mul_comm] using
      (Nat.le_mul_of_pos_left
        Graph.SameTokenBlockerRoles.sameTokenRoleBound
        (Nat.mul_pos first second))
  have safety := data.roleSafety
  omega

/-- The registered `C_sp` absorbs the safety coefficient of the generic
quadratic estimate: the homogeneous cap already does (`L_geom ≥ 2`), and
`C_sp` adds only nonnegative deficit and token-supply terms to it. -/
theorem Data.quadraticSafetyScale_le_spineScale (data : Data.{u}) :
    Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale := by
  have registered := data.quadraticSafetyScale_le_twiceAdditive
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
      data.routingLabelBound) at registered
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
      data.routingLabelBound) +
      (2 * data.surplusScale +
        2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
          data.routingLabelBound * (3 * (data.threshold - 1) + 2))
  omega

/-- The registered label count forces the window order to be at least three:
the legal labels of a path on `order` vertices are among its `2^order` subsets,
and `399 > 2^2`. -/
theorem Data.three_le_windowOrder (data : Data.{u}) : 3 ≤ data.windowOrder := by
  by_contra small
  have le : (Graph.WindowCurvature.Labels data.windowOrder).card ≤
      2 ^ data.windowOrder := by
    calc (Graph.WindowCurvature.Labels data.windowOrder).card
        ≤ (Finset.univ : Finset (Graph.WindowCurvature.Label data.windowOrder)).card :=
          Finset.card_le_univ _
      _ = 2 ^ data.windowOrder := by simp [Graph.WindowCurvature.Label]
  rw [data.labelCount] at le
  have : data.windowOrder ≤ 2 := by omega
  have : 2 ^ data.windowOrder ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
  omega

/-- The registered label table also forces enough interior positions for the
two absorbed corridor ends to leave positive restricted branch excess. -/
theorem Data.five_le_windowOrder (data : Data.{u}) : 5 ≤ data.windowOrder := by
  by_contra small
  have le : (Graph.WindowCurvature.Labels data.windowOrder).card ≤
      2 ^ data.windowOrder := by
    calc (Graph.WindowCurvature.Labels data.windowOrder).card
        ≤ (Finset.univ : Finset (Graph.WindowCurvature.Label data.windowOrder)).card :=
          Finset.card_le_univ _
      _ = 2 ^ data.windowOrder := by simp [Graph.WindowCurvature.Label]
  rw [data.labelCount] at le
  have orderLe : data.windowOrder ≤ 4 := by omega
  have powerLe : 2 ^ data.windowOrder ≤ 2 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) orderLe
  norm_num at powerLe
  omega

/-- The semantic facts the entry spine proves.

Each constructor is one manuscript statement.  A key determines exactly one
value schema, so two unrelated facts cannot impersonate one another. -/
inductive Key where
  /-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
  strictly smaller baseline object does not. -/
  | selection
  /-- The presentation laws of G's registered presentation, published once at
  the entry (`PresentationLawsStatement`): the cubic baseline identities, the
  Type B presentation facts (with the dyadic target law), the sparse-surplus
  presentation identities, and the spine laws at G.  Every row reads a
  presentation law from this one fact with `inputs.get`. -/
  | cubicBaseline
  /-- Nodes `[1]`--`[3]` (`def:counterexample`, tex 714, 1370): G meets the
  registered baseline, `δ(G) ≥ δ` (`δ = 3` by `K .cubicBaseline`).  Published
  once at the entry from the selected object's own baseline proof. -/
  | minDegreeBaseline
  /-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
  accepted set at every oriented edge.  This is the return-set form of target
  avoidance, the standing invariant the rest of the spine consumes. -/
  | returnAvoidance
  /-- Node `[6]`, yes arm: some oriented edge carries a Mersenne return, i.e.
  its return-length set meets the shifted accepted set.  This is the exact
  complement of `returnAvoidance` on the same object. -/
  | mersenneReturn
  /-- Node `[8]`: no proper subgraph satisfies the baseline. -/
  | noProperBaseline
  /-- Node `[9]`: every oriented edge has an endpoint exactly at the
  threshold. -/
  | tightEndpoint
  /-- Node `[10]`: vertices strictly above the threshold are pairwise
  nonadjacent. -/
  | slackIndependent
  /-- `lem:cycle-rank`: for the selected graph,
  `β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.  This is the manuscript's
  division-free form of `β(G) ≥ n/2 + 1`. -/
  | cycleRankConstraint
  /-- Node `[13]`, `lem:replacement`, stated about G: no proper support `Z`
  admits a replacement `X'` with G's boundary-degree profile such that
  `glue X' (G − Z)` meets the baseline, is strictly smaller and has no
  power-of-two cycle. -/
  | replacementExclusion
  /-- Node `[14]`: no proper atom admits a nontrivial target-complete
  compression (`cor:uncompressible`). -/
  | uncompressible
  /-- Node `[15]`, yes arm: the object is induced-window-free at the
  registered window order (`G` is `P₁₃`-free). -/
  | windowFree
  /-- Node `[15]`, no arm: the object contains an induced window of the
  registered order (`cor:p13-exists`).  This is the exact complement of
  `windowFree` on the same object. -/
  | windowPresent
  /-- Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family
  of induced windows, and the family is nonempty. -/
  | maximalPacking
  /-- Node `[18]`: `lem:labels`'s exact legal-label census at the registered
  window order.  The adjacent `C_s` and `Ω₂` displays are definitions supplied
  by `WindowCurvature.Safe` and `WindowCurvature.curvatureTwo`. -/
  | localAlgebra
  /-- Node `[19]`, above arm: the degree surplus exceeds the registered scale
  threshold. -/
  | surplusAbove
  /-- Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite
  form. -/
  | surplusAtOrBelow
  /-- Node `[22]`, cap arm: the packing's entropy demand fits inside the
  labelled skeleton budget, which is itself stable under a variable edge
  count. -/
  | barrierCap
  /-- Node `[22]`, overflow arm: the demand exceeds the budget. -/
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
  /-- Node `[31]`, `def:exact-response-profile` at the remainder of every
  maximal packing: the declared raw curvature coordinates are exact, so their
  labelled family has exactly `W₂(R)` entries. -/
  | exactResponseProfile
  /-- Node `[31]`, `def:curvature-target-rank` at the remainder of every
  maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw
  curvature tests and bounds every surviving subfamily. -/
  | curvatureTargetRank
  /-- `lem:target-rank-circuit` at the remainder of every maximal packing:
  every raw test outside a maximal surviving family carries a proper finite
  target-dependence, and absence of proper dependences is full survival. -/
  | targetRankCircuit
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
  That certificate, `branchCertificate? data G` (at the canonical packing and
  node `[19]`'s test), is the one object nodes `[36]`--`[45]` route. -/
  | branchDependence
  /-- Node `[36]`, yes arm: the determination the certificate of `G` makes is
  valid in every context of G (`lem:context-universality` stated about G: the
  readings it identifies agree in `G − Z`).  Decided at G; this is the residual
  node `[38]` consumes. -/
  | contextUniversal
  /-- Node `[36]`, no arm — the terminal `[37]`: some pair of readings of G the
  certificate identifies is separated by `G − Z`.  This is case (i) of
  `lem:curvature-dependence-routing`, a target-defective quotient; empty at G
  (it closes against node `[12]`).  Boundary-profile preservation is already
  part of quotient admissibility. -/
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
  `s = p − 2 + 2β − σ` at every delayed compensation component of the support
  of the certificate of `G`. -/
  | repairIdentity
  /-- Node `[45]`: the global profile barrier `lem:no-silent-global-smearing`
  raises against a whole-graph dependence — the closed clause of
  `def:admissible-rank-quotient` yields a strictly smaller admissible closed
  representative of the certificate's whole-graph quotient. -/
  | globalBarrier
  | coldCorridorState
  | coldSameInterfaceTable
  | coldGermRealized
  | coldGermDistinguished
  | coldGermSilent
  /-- Node `[21]`: `lem:curv-enum`, the certified finite barrier enumeration
  read from the registered table. -/
  | barrierEnumeration
  /-- Nodes `[21]`--`[22]`: `lem:p13-window-package`.  The selected coordinates of
  the multi-scale window package are separated, and each carries the audited
  per-window rate.  This is the arm on which `lem:independent-target-entropy`
  applies; the arm where the coordinates collide is the `O(1)` the manuscript's
  scale count discards. -/
  | windowPackageSeparated
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
  /-- `prop:two-budget` (b): on the low-entropy residual, the radius-two
  rooted-type coordinate lies below the exact finite relabelling threshold. -/
  | localTypeCoordinateRepetitive
  /-- `prop:two-budget` (c): the same literal coordinate is not structurally
  repetitive.  This arm passes unchanged to the large-budget analysis. -/
  | localTypeCoordinateNonrepetitive
  /-- `lem:dominant-type`: the repetitive coordinate has a single rooted
  radius-two type outside only the registered finite `o(n)` allowance. -/
  | dominantRootedType
  /-- The wedge-free subarm after `lem:dominant-type`; the manuscript makes no
  translate-rank claim and passes this arm to the large-budget analysis. -/
  | dominantRootedTypeWedgeFree
  /-- The literal incoming wedge subarm of `lem:translates-independent`: the
  preceding executor proved the dominant rooted type and the decision found an
  internal root wedge in that same type. -/
  | dominantRootedWedgeType
  /-- Nodes `[51]`--`[52]`, `lem:translates-independent`: a dominant rooted
  radius-`r` type with an internal root wedge admits a maximal `2r`-separated
  family of translates.  Its radius-`r` balls are disjoint, the radius-`2r`
  balls cover the dominant centres, and full obstruction rank gives the exact
  finite inequality whose asymptotic form is
  `r_Ω(R) ≥ c_r|R| - o(|R|)`. -/
  | independentObstructionTranslates
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
  /-- Node `[54]`: the independently realized window/remainder code fits in
  the labelled skeleton class.  This is the exact bound contradicted by the
  active arm of `eq:entropy-cap`. -/
  | entropyCapBound
  /-- Node `[53]`, no arm — node `[55]`, Residual C: the joint package still
  fits the skeleton budget, and the branch is the large-budget residual. -/
  | largeBudgetResidual
  /-- Node `[56]`: exact cleared finite form of the large-budget
  net-deficiency cap. -/
  | netDeficiencyCap
  /-- Node `[173]`, `lem:exact-collision-test`, no arm: node `[56]`'s
  collision, decided exactly on the current object, fails at some maximal
  packing — the absorbed-germ residual `[174]`. -/
  | exactCollisionFails
  /-- Node `[174]`, `lem:exact-collision-test`, the consequence of the failed
  collision: the failure witness packing `P` of `[173]` satisfies
  `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`, `A = netChargeCoefficient`,
  the manuscript's `C ≥ (n − 73|𝒫_hot| − 4(σ_W − σ_R))/73` without subtraction:
  the residual carries linearly many cold windows. -/
  | absorbedConfigurationResidual
  /-- Node `[60]`: the large-budget remainder has negative total net charge
  once the paper's explicit sufficiently-large predicate holds. -/
  | netChargeCap
  /-- Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.  The
  canonical support decomposition is exact on all three of the charge's terms,
  so a remainder of negative net charge has a *connected* admissible support of
  negative net charge. -/
  | netChargeLocalization
  /-- Node `[59]`, yes arm: `N₀(R) ≥ 0` for the fixed maximum packing
  whose complement is the manuscript's remainder `R`. -/
  | netChargeNonNegative
  /-- Node `[59]`, no arm: `N₀(R) < 0` for that same selected packing. -/
  | netChargeNegative
  /-- Node `[61]`: `prop:negative-net-charge`.  A connected admissible support
  of the remainder carries negative net charge. -/
  | negativeSupport
  /-- Node `[62]`, no arm — node `[63]`, Type A: the selected negative support
  carries no assigned high-degree surplus. -/
  | typeALowSurplus
  /-- Node `[87]`: the selected Type A support is induced-`P_windowOrder`-free;
  every two of its vertices have an internal path of length at most
  `windowOrder - 2`, and the subcubic breadth-first bound gives
  `1 + threshold * (2^(windowOrder - 2) - 1)` vertices.  At the registered
  `windowOrder = 13`, `threshold = 3`, these are diameter at most `11` and
  cardinality at most `6142`. -/
  | typeABoundedSupport
  /-- Node `[62]`, yes arm — node `[64]`, Type B: the selected negative support
  carries assigned high-degree surplus. -/
  | typeBHighSurplus
  /-- Node `[65]` at the `[64]` entry: the ordinary Type B assigned support.
  `def:canonical-decomp` assigns every surplus unit `d_G(h) − 3` of a high
  centre `h ∈ V_{≥4}(G) ∩ V(R)` to the piece containing `h`, so the Type B
  support's assigned fan centres are its own high centres, and `σ(X) > 0` says
  it has one; the fan of a centre is `N_G(h)`. -/
  | typeBAssignedSupport
  /-- Nodes `[65]`/`[66]`: the common Type B fan support entry
  (`def:typeB-assigned-ledger`): a canonical core with its assigned centres —
  the ordinary support's own high centres at `[65]`, or the decorations of the
  handoff envelope at the dashed input `[66]` — nonempty and all high. Nodes
  `[71]`--`[75]` are stated on it. -/
  | typeBFanEntry
  /-- Node `[68]`, yes arm, on either literal `[65]` input: some assigned centre
  of the canonical support, or an actual centre of an indexed `[177]` handoff
  datum, is *heavy* — degree above the high-centre degree `δ + 1`
  (`d_G(h) > 4` at the manuscript's baseline). -/
  | typeBFanHeavyCentre
  /-- Node `[68]`, no arm, on either literal `[65]` input — the entry of node
  `[78]`: every assigned centre of the canonical support, or a retained witness
  for every indexed `[177]` datum, has degree exactly `δ + 1`
  (`d_G(h) = 4` at the manuscript's baseline). -/
  | typeBFanDegreeFourCentres
  /-- Node `[69]`, `lem:same-center-open-port-compatibility`.  On the active
  object, any two distinct nonadjacent open ports at the same high centre are
  fan-compatible. -/
  | sameCenterOpenPortCompatibility
  /-- Node `[69]` at the `[64]` entry: `cor:heavy-center-local-dichotomy` at
  every heavy fan centre of the ordinary Type B support — a fan-compatible open
  pair, or at least `d_G(h) − 2` triangular ports, hence three. -/
  | typeBFanLocalDichotomy
  /-- Nodes `[78]`--`[79]` at the `[64]` entry: the degree-four fan profile of
  the ordinary Type B support.  Every assigned fan centre sits at `δ + 1`;
  `cor:degree-four-local-activation` gives a fan-compatible open pair or
  `δ − 1` triangular ports (the manuscript's "at least two"); the centre
  surplus is `1`, the cubic-closed count is at most the degree, and the
  closed-neighbour deficit is `s·c − s·δ + (δ + 2)` at the registered discharge
  scale — the manuscript's `D_B = c − 7/4`, never written. -/
  | typeBFanDegreeFourProfile
  /-- Node `[79]`, `def:triangular-fan-core`: the shoulder sets, induced core
  vertex set, and completion-incidence classifications of every nonempty
  triangular-port family at a heavy centre. -/
  | triangularFanCore
  /-- `lem:triangular-shoulder-completion`: the four completion-incidence
  conclusions for every triangular port at a heavy centre. -/
  | triangularShoulderCompletion
  /-- `lem:triangular-port-return`: deleting a triangular port edge leaves a
  simple return through a shoulder; its restored cycle is forbidden, and the
  shoulder tail contains a noncentral completion incidence. -/
  | triangularPortReturn
  /-- `lem:triangular-first-landing`: every completion incidence in a
  triangular fan core is uniquely central, cross-triangular, or outside. -/
  | triangularFirstLanding
  /-- `lem:triangular-cross-shoulder`: two cross edges between distinct
  triangular shoulder pairs force a high shoulder; after that branch is
  routed away, the surviving cross edges have cardinality at most one. -/
  | triangularCrossShoulder
  /-- `def:open-port-suppression`: the literal compatible family and its
  simultaneous delete-and-add graph. -/
  | openPortSuppression
  /-- `lem:open-port-suppression-safe`: every vertex surviving a suppressible
  family of open ports has degree at least three.  Finiteness and simplicity
  are carried by the canonical `FiniteObject` suppression output itself. -/
  | openPortSuppressionSafe
  /-- `lem:single-open-port-suppression-witness`: an open tight port has a
  simple shoulder-to-shoulder path in the vertex-deleted graph whose restored
  length is an accepted dyadic cycle length. -/
  | singleOpenPortSuppressionWitness
  /-- `lem:suppressed-family-critical-cycle`: a nonempty suppressible family
  has an accepted suppressed cycle using added chords, and every such cycle
  expands to a forbidden source-cycle length. -/
  | suppressedFamilyCriticalCycle
  /-- `lem:compatible-pair-fan-closure`: compatible open ports recorded by one
  assigned profile are distinct fan-closed ports. -/
  | compatiblePairFanClosure
  /-- `prop:fan-closed-port-typeB-routing`: two or more fan-closed ports give
  the positive local Type-B deficit bound. -/
  | fanClosedPortTypeBRouting
  /-- `cor:compatible-pair-typeB-routing`: a recorded compatible open pair
  gives the positive local Type-B deficit. -/
  | compatiblePairTypeBRouting
  /-- `prop:triangular-port-typeB-routing`: a degree-`k` heavy triangular
  family of exactly `k - 2` assigned ports gives the stronger positive local
  Type-B deficit bound `(5k - 19) / 4`. -/
  | triangularPortTypeBRouting
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
  /-- Node `[91]`: the `3/7/11` discharging conclusion on every unsaturated
  Type A support, in the exact integral form
  `|V(X)| ≤ s * def⁺(X)`. -/
  | typeAUnsaturatedDischarge
  /-- Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the
  minimal counterexample: every negative zero-surplus canonical piece of a
  maximal packing's remainder carries an exit-`(4)` witness for a routed load,
  an admissible silent-core residual profile, or a produced decorated Type B
  handoff. -/
  | typeAExclusion
  /-- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`
  (`def:typeB-bridge-statements`), in the contrapositive the branch carries:
  every negative positive-surplus canonical piece of a maximal packing's
  remainder carries the B2 disjoint ledger with strictly negative remaining
  scaled core charge — every remaining component the post-ledger Type A
  hygiene carrier of `lem:typeB-postledger-core-hygiene`, with the B2(d)
  grouped decorated envelope coverage — or a minimal Type B overlap
  obstruction among the piece's own high centres. -/
  | typeBBridgeReduction
  /-- `prop:typeB-bridge-sublinear`'s hypotheses, tested: the flat off-centre
  pair at every negative positive-surplus canonical piece and the grouped
  fan-assignment data at the negative zero-surplus handoff pieces. -/
  | typeBSublinearLedger
  /-- The exact negation of the sublinear hypotheses, retained as the tested
  residual state (the manuscript's Part IX bridge-residual continuation). -/
  | typeBSublinearResidual
  /-- The quotient-freeness of the unified census (tex 15360-15364): no
  entry's selected basin carries a nontrivial target-complete response
  quotient.  The yes arm makes every unified entry route-8 or alternative-(a);
  the no arm is alternative (b) at a unified entry. -/
  | route8QuotientFree
  /-- The exact negation: some unified entry realizes alternative (b).
  `thm:main` returns it at `[187]` as the failure of route-8 quotient freeness
  (tex 369-372, 388-390). -/
  | route8QuotientResidual
  /-- `def:typeA-pressure-ledger` at the failed-rate stage: the maximal pinned
  2/3-demand ledger over the unified collection, with its no-overcount counts
  and the canonical demand records of the unpaid target-defect entries. -/
  | route8DemandLedger
  /-- `def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the
  extracted route-8 cores of the Type B bridge pieces (node `[123]`): the exact
  per-entry census of `lem:typeB-bridge-with-route8-core`'s collection `𝒜_X`. -/
  | route8ExtractedEntryCensus
  /-- Nodes `[89]`, `[93]`, `[94]`, `[109]`, `lem:typeA-port-return`: every
  completion port of the selected object carries at least one anchored return.
  `lem:bridgeless` says the port edge is on a cycle, and deleting it from that
  cycle leaves the return.  This is what makes every saturated port test
  nonvacuous: the alternatives at nodes `[95]`--`[107]` quantify over the
  anchored returns of a port, and without this fact "no return of the port has
  property `p`" would be satisfied by a port with no returns at all. -/
  | typeAPortReturn
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
  /-- **The shared entry of nodes `[101]`--`[107]`**, and the hypothesis of
  `lem:typeA-exit4-residual-routing`: *"let `w` be a saturated Type A receiver
  with a peeling set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads
  at `w` realize one of exits (1)--(8)"*.

  Figure 8 draws one segment `[101]`--`[107]` with *two* entries: node `[99]`'s
  no arm, which is `lem:typeA-unpeeled-visible-routing` after exits `(1)`--`(3)`
  have been denied, and node `[94]`, which is
  `lem:typeA-unpeeled-silent-routing`.  `lem:typeA-exit4-residual-routing` is
  the manuscript's own statement that the two combine, and this is its
  hypothesis: the exit segment is asked under it and under nothing else, so the
  segment is one chain of nodes rather than two copies.

  It is a refinement of the residual node `[89]` already committed, not a new
  assumption: at the empty peeling set `L₄(w) = L(w)`, so
  `ExitFour.saturatedAfter_empty` reads it straight off
  `typeASaturatedReceiver`.  No exit-(4) fact is currently produced from this
  entry: the required coordinate-specific response realization is absent. -/
  | typeASaturatedExitEntry
  /-- Node `[108]`, on node `[107]`'s yes arm — exit `(7)` of
  `def:typeA-saturated-exits`: *"a high-degree decorated handoff fan envelope
  is produced"*, at the visible saturated port node `[93]` delivered.  This is
  the Type B handoff exit, and it is the one exit of the list that neither
  closes nor stays in Type A:
  `lem:typeA-exits-discharged` says the branch *"is reclassified as a decorated
  handoff fan envelope and leaves the Type A charge calculation"*.

  The envelope is `def:decorated-fan-envelope`'s `𝔛 = (Y, H)` with `Y` the Type
  A support itself and `H` the surviving first separator of two declared outside
  connector germs through the port — `def:typeA-trace-basin` clause (d), routed
  by `lem:typeA-continuation-routing`, with ambient degree at least `4` by
  `lem:typeA-cubic-switch-absorption` and handed over by
  `lem:typeA-high-degree-handoff`.  This node records only that produced
  envelope.  Node `[65]` proves `lem:decorated-fan-admissibility` from this fact
  and the inherited selection, normalization, and uncompressibility facts on
  the same ledger.  By `rem:typeA-typeB-stratification` no conclusion of
  `lem:typeB-exclusion` is used, and none is available on this cursor. -/
  | typeAExitSevenHandoff
  /-- Node `[65]` on the decorated lane: the exact exit-`(7)` envelope, its
  Type-B centres and assigned first-neighbour supports, and every clause of
  `lem:decorated-fan-admissibility`, all published on the same residual for the
  common Type B continuation. -/
  | typeBDecoratedAssignedSupport
  /-- Node `[107]`, no arm — the entry of node `[109]`: no high-degree decorated
  handoff fan envelope is produced at any visible port of any saturated receiver
  of any Type A support, so exit `(7)` is not the exit this branch realizes and
  the saturated exit list continues at exit `(8)`, the route-8 residual of
  `def:typeA-silent-core-residual`. -/
  | typeAExitSevenFree
  | coldFailureCycle
  /-- `lem:cold-corridor-first-failure` (ii): an (F2) pair of prefixes of one
  of G's corridors is a target-defective quotient. -/
  | coldFailureDefectRoute
  | coldFailureCompression
  | coldFailureRouting
  | coldFirstFailureOccurrence
  | coldExchangeBound
  /-- Node `[146]`, yes: the canonical packing lies below the route-8
  private-carrier threshold. -/
  | coldRoute8Below
  /-- Node `[146]`, no: the same canonical packing is not below that threshold. -/
  | coldRoute8AtOrAbove
  /-- Node `[148]`, yes: the live-hot coordinates exceed the near-cubic
  skeleton allowance. -/
  | coldHotEntropyOverflow
  /-- Node `[148]`, no: the live-hot coordinates fit in that allowance. -/
  | coldHotEntropyCap
  /-- Node `[150]`: the exact cleared cold-mass inequality. -/
  | coldMass
  /-- Node `[151]`: the non-ambient-cubic cold-window loss. -/
  | coldAmbientCubic
  /-- Node `[152]`: the selected cold-skeleton branch-excess inequality. -/
  | coldStubExcess
  /-- Node `[153]`, exact form of "for all sufficiently large `n`": the cold
  mass exceeds the two branch-excess slacks, so the extracted germ family is
  positive (`lem:cold-germ-extraction`). -/
  | coldMassLinear
  /-- Node `[153]`, complementary arm: the cold mass is within the two
  branch-excess slacks; the spine continues to `[24]`'s density cap. -/
  | coldMassBounded
  /-- `lem:bridgeless`: the selected minimal counterexample has no bridge —
  every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`. -/
  | bridgeless
  /-- `def:cold-corridor-first-failure`, the corridor construction: every
  boundary stub of every outside component of the ambient-cubic cold windows
  has its cold return corridor. -/
  | coldReturnCorridors
  /-- Node `[21]`, `lem:p13-window-package` with `def:target-rank` and
  the realization sentence used in `lem:p13-window-package` and `prop:p13-density`,
  "all target-complete window states are realized by labelled near-cubic
  skeletons": the canonical
  multi-scale package of the fixed maximal packing is a family of independently
  target-testable coordinates, i.e. its full package code is realized canonically
  by the labelled skeletons of the current object's class `𝒢_{n,m}`. -/
  | windowPackageRealized
  /-- The complementary arm of the `[21]` realization decision: the fixed
  maximal packing's full package code is *not* realized canonically by the
  labelled skeletons of the current object's class — the residual on which the
  manuscript's `[21]` sentence fails, carried as a branch of its own. -/
  | windowPackageUnrealized
  /-- On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact
  large-budget net-deficiency comparison holds at the fixed maximal packing —
  the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n`
  allowance, i.e. the inequality node `[56]` supplies to `[57]`--`[62]`. -/
  | denseDeficiencyBelow
  /-- Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact
  allowance, on which the net-charge collision does not fire. -/
  | denseDeficiencyAtOrAbove
  /-- Node `[162]`: every return corridor of the dense hot/cold pass is the
  terminal (F5) subcase because its selected shortest path lies in the
  induced-window-free normalized remainder. -/
  | denseColdCorridorsTerminal
  /-- Node `[163]`, `def:neutral-equal-length-germ`: the marked terminal
  corridor piece and the canonical exact-cut-state representative selected for
  it have equal length and edge count, preserve the boundary profile and
  baseline, and have the same target response in every outside context. -/
  | coldNeutralEqualLengthTerminal
  /-- Node `[168]`, the stub structure of the ambient-cubic cold windows: at
  exactly two endpoints carry `δ − 1` external stubs and every other window vertex
  carries `δ − 2`; a genuine symmetric strand pair needs two stubs at each
  attachment vertex, so it can attach only at the endpoints, and at least
  `(order − 2)(δ − 2)` stubs are single-stub interior attachments. -/
  | coldWindowStubStructure
  /-- Node `[163]`, no-arm: no neutral zero-increment germ of the incoming
  extracted family has a graph-realized second strand; its `E` is therefore
  the canonical-replacement case of `[165]`--`[166]`. -/
  | coldCanonicalNeutralConfiguration
  /-- Node `[163]`, yes-arm: a neutral zero-increment germ of the incoming
  extracted family is realized in the ambient graph as a genuine second
  strand, with its exact two-strand numerical configuration. -/
  | coldGenuineSecondStrand
  /-- Node `[167]`, survivor arm: the graph-realized symmetric strand pair is
  in the literal finite survivor list after neither of its two closing lengths
  is dyadic.  Node `[168]` consumes this fact together with the window-stub
  structure and the selected interior half-edge. -/
  | coldTwoStrandSurvivor
  /-- Node `[168]`: the endpoint/interior stub count excludes every surviving
  genuine pair whose retained origin is one of the selected interior
  half-edges. -/
  | coldSymmetricPairExcluded
  /-- `lem:refined-minimality-swap`, size-reducing case (node `[165]`): some
  neutral germ's corridor piece has a canonical representative with strictly
  fewer internal vertices, so the exchange is a strictly smaller counterexample. -/
  | coldCanonicalSwapSmaller
  /-- The exact complement: every neutral germ's canonical representative has
  the same internal size as its corridor piece — the same-size tie-break of node
  `[166]`. -/
  | coldCanonicalSwapSameSize
  /-- Node `[165]`: for every neutral configuration, replacing `Q` by a
  distinct canonical representative `E` gives a baseline,
  target-avoiding graph with the same vertex and edge counts, while `E`
  strictly precedes `Q` in the fixed canonical piece order. -/
  | coldCanonicalReplacementSwap
  /-- Node `[166]`: refined minimality forces every neutral configuration's
  canonical replacement to be the corridor piece itself, `E = Q`. -/
  | coldCanonicalReplacementTrivial
  /-- Node `[169]`, `def:blocked-class`: on the trivial neutral-configuration residual the
  object's own labelled skeleton lies in the blocked class `𝓑(𝒫)` of the fixed
  maximal packing (near-cubic, windows present, no accepted cycle through a
  window), and `card 𝓑(𝒫) ≤ skeletonBudget`. -/
  | blockedClassMember
  /-- Node `[170]`, `lem:scale-additivity`: on the blocked class of the fixed
  packing the paper's relative conditional graph-fibre bound holds at every
  fixed scale.  The fact also retains the local `F_{a,b}+1` state-fibre bound
  (including the distinct absent-completion state) and graph-fibre
  monotonicity; neither auxiliary fact replaces the paper ratio. -/
  | blockedScaleAdditive
  /-- Node `[171]`, `lem:blocked-graphs-compress`: the denominator-cleared
  finite-exposure inequality for the blocked class against the exact
  near-cubic a-priori class. -/
  | blockedCompressionBound
  /-- Node `[171]`, terminal consequence: the registered package saving is at
  most the exact labelled-skeleton budget. -/
  | blockedCompressionCap
  /-- Node `[170]`, the exact complement (`lem:barrier-failure-overlap`): the
  conditional saving fails at a specific window, scale, and barrier row; the
  retained value is the actual oversized conditional fibre, before the overlap
  lemma constructs its support. -/
  | blockedBarrierOverlap
  /-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii): every selected
  branch-excess half-edge outside node `[153]`'s exact subcubic candidate
  class meets a vertex of degree above the threshold, a heavy centre, and is
  decorated handoff fan data for Type B.  The candidate class remains in the
  same ledger for node `[176]`; mixed families are not collapsed. -/
  | absorbedGermFanData
  /-- Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge
  dichotomy — every selected branch-excess half-edge's first-failure support is
  subcubic (a charged candidate germ) or meets a heavy centre whose neighbours
  all sit at the threshold (node `[10]`). -/
  | absorbedGermSplit
  /-- The route-8 rate-failure residual, `rem:route8-carrier-margin` read
  exactly: the cold family of the fixed packing is nonempty, so the failure of
  the private-carrier rate is carried by absorbed cold germs (`[174]`--`[177]`). -/
  | coldFamilyPositive
  /-- The complementary arm: the cold family is empty — every packed window is
  hot at the exact skeleton budget, and the private-carrier rate still fails:
  the exact budget-edge corner of `rem:route8-carrier-margin`. -/
  | coldFamilyEmpty
  /-- Node `[153]`: a positive current-residual bounded-germ family. -/
  | coldGermCandidates
  /-- Node `[153]`, linear arm: the literal disjoint family retained by
  `coldGermCandidates` is nonempty after both surplus losses are paid. -/
  | coldGermFamilyPositive
  | coldSelectedBranchExcess
  | coldAmbientCubicStubExcess
  | coldHandoffTransfer
  | coldPositiveGerm
  | coldGermRouted
  | coldBranchClosed
  /-- Node `[154]`, first binary test of `lem:cold-bounded-germ-trichotomy`
  (G1): some configuration of the extracted active family is hit-realized. -/
  | coldGermSomeRealizing
  /-- Node `[154]`, the exact complement of `coldGermSomeRealizing`. -/
  | coldGermNoneRealizing
  /-- Node `[154]`, second binary test on the no-G1 arm (G2): some configuration
  of the extracted active family is hit-distinguished. -/
  | coldGermSomeDistinguishing
  /-- Node `[154]`, the exact complement of `coldGermSomeDistinguishing`: every
  active configuration is silent (G3 or the equal-length table). -/
  | coldGermNoneDistinguishing
  /-- Node `[67]`, the standing law: every high centre of the object has its
  neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` --
  cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside
  `{h}` for a nonadjacent pair.  Both arms of the degree split run on it. -/
  | highCentreNormalForm
  /-- Node `[70]`: the certificate-marked fan-degree cap.  Every high centre
  carrying a fan-certificate labelling has degree at most the label algebra's
  own packing number -- the manuscript's `d_G(h) ≤ 8`
  (`lem:fan-certificate`, `rem:fan-finite`). -/
  | fanCertificateCap
  /-- Node `[71]`/`[80]`, yes arm: every assigned centre of the Type B support
  carries G's canonical fan-certificate labelling, under the label-packing cap
  (`def:marked-typeB-fan`). -/
  | fanCertificateMarked
  /-- Node `[71]`/`[80]`, no arm: some assigned centre of the Type B support
  carries no fan-certificate labelling (G's canonical labelling is absent).  `def:marked-typeB-fan` calls it a *fan-certificate residual
  center*; it is charged to the Type B bridge-residual mass of
  `def:typeB-residual-mass` and takes no part in the certificate-closed local
  discharging step. -/
  | fanCertificateResidual
  /-- Nodes `[72]`/`[81]`: the hybrid B1 fan ledger.  At every assigned centre
  of the direct-cycle-free, certificate-marked Type B support, on its assigned
  fan envelope, the non-`h` incidences of its cubic-closed
  neighbours are pairwise distinct carriers, they split into the window count
  `I_W` and the non-window count `I_N` of `def:typeB-hybrid-incidence`, their
  half-credit pays the closed-neighbour deficit `D_B`, the non-window half-credit
  covers the remaining demand `D_N`, and two cubic-closed neighbours already make
  `D_B` positive (`lem:typeB-hybrid-incidence-budget`, `lem:typeB-hybrid-B1`,
  `prop:fan-closed-port-typeB-routing`). -/
  | typeBHybridEntry
  /-- Nodes `[72]`/`[81]`, inside the local fan-window ledger: every assigned
  centre of the marked Type B support is direct-cycle-free at `P₀`
  (`lem:typeB-direct-fan-window-cycles`, `def:direct-cycle-free-closed-pair`);
  a direct configuration would be a cycle of accepted length. -/
  | typeBDirectCycleFree
  /-- Node `[72]`, yes arm: the local B1 ledger is complete and B2 holds at the
  Type B support: its certificate-marked assigned centres have a
  pairwise-disjoint choice of candidate entries on the assigned fan envelopes of
  the support. -/
  | typeBB2Choice
  /-- Node `[74]`, B2(a)--(d): the Type B support is B2-paid; its canonical B2
  ledger exists with its exact augmented-ledger refinement, the inherited Type A
  hygiene of every remaining component, and the grouped exit-`(7)` handoff
  coverage used by B2(d). -/
  | typeBDisjointLedger
  /-- Node `[72]`, no arm — the entry of `[73]`: B2's disjoint-carrier clause
  fails at the certificate-marked Type B support, which by
  `lem:typeB-bridge-to-overlap` carries G's canonical minimal Type B overlap
  obstruction of `def:typeB-overlap-obstruction`. -/
  | typeBOverlapObstruction
  /-- Node `[73]`/`[83]`: the canonical minimal obstruction together with all
  five global-to-local reflection clauses.  Auxiliary indexed and same-token
  obstruction carriers are retained unchanged because they enter fan mass
  directly rather than asserting a canonical remainder component. -/
  | typeBGlobalLocalBridge
  /-- Nodes `[75]`/`[84]` on the certificate-residual arm: the support-level
  bound `lem:typeB-bridge-deficit-bound` at the fan-certificate residual
  support. -/
  | fanCertificateResidualMass
  /-- Nodes `[75]`/`[84]` on the B2-failure arm: the support-level bound
  `lem:typeB-bridge-deficit-bound` at the reflected obstructed support. -/
  | typeBOverlapObstructionMass
  /-- Node `[175]`, yes, read at `[177]`: some selected corridor meets a
  high-degree vertex --- `G`'s canonical absorbed half-edge exists. -/
  | typeBAbsorbedHalfEdge
  /-- Node `[175]`, no: every selected corridor is subcubic (no absorbed
  half-edge). -/
  | typeBAbsorbedHalfEdgeAbsent
  /-- Node `[177]`, yes: a counted remainder core exists at the heavy centre
  of `G`'s canonical absorbed half-edge. -/
  | absorbedHandoffCore
  /-- Node `[177]`, no: no counted remainder core at that heavy centre. -/
  | absorbedHandoffCoreAbsent
  /-- Node `[177]`, no arm: the half-edge is charged by the exact (F4) count to
  node `[219]`'s corridor loss (user-approved (F4) repair extension). -/
  | absorbedF4Charge
  /-- Node `[81]`, yes: `c ≤ 1` at every assigned centre, or `c ≥ 2` with the B2
  disjoint choice, at the degree-four Type B support. -/
  | typeBDegreeFourLedger
  /-- Node `[81]`, no → `[83]`: some assigned centre has `c ≥ 2` and B2 fails;
  minimal Type B overlap obstruction. -/
  | typeBDegreeFourOverlap
  /-- Node `[82]`: certificate-closed (`c ≤ 1`, `lem:typeB-exclusion` Step 1)
  or B2-paid with its remaining core carrying the whole deficit, at the
  degree-four Type B support. -/
  | typeBDegreeFourClosed
  /-- Node `[177]`: every selected half-edge outside the subcubic candidates has
  its pinned absorbed Type B support, charged to the surplus of its centre. -/
  | typeBAbsorbedCharge
  /-- Node `[77]`: the Type B entry into route `8`; a negative Type B support
  hands a negative remaining core to route `8` or is a bridge residual charged
  to its surplus. -/
  | typeBRoute8Entry
  /-- Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts
  for certificate residuals, overlap obstructions, and grouped decorated
  envelope residuals. -/
  | typeBBridgeMass
  /-- `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been
  extracted into the Type A ledger, the remaining Type B bridge residual mass is
  paid by the assigned high-centre surplus. -/
  | typeBBridgeSublinear
  /-- Node `[74]`, `prop:typeB-bridge-reduction`: the remaining core of the Type
  B support's canonical B2 ledger carries the whole deficit. -/
  | typeBExcluded
  /-- Node `[76]`/`[85]`: Type B cannot carry the linear deficit outside route
  `8`; the B2-paid support keeps its deficit in its remaining core, and a
  bridge-residual support is charged to its assigned surplus. -/
  | typeBExclusionResidual
  /-- Node `[102]`: the exit-`(4)` witness has been charged to the peeling
  ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load
  condition and dropping the residual load by one. -/
  | typeAExitFourPeeled
  /-- `lem:typeA-exit4-finite-descent` / `lem:typeA-saturated-handoff`: the
  finite exit-`(4)` descent principle read at the exact current saturated
  receiver/peeling state; consumed by node `[123]`'s pressure descent. -/
  | typeAExitFourFiniteDescent
  /-- `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current
  saturated receiver/peeling state. -/
  | typeASaturatedHandoffExitFour
  /-- `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current
  saturated receiver/peeling state; this is the predecessor of exit `(5)`. -/
  | typeASaturatedHandoffExitFourFree
  /-- Node `[102]`, no-loop arm: after the exit-`(4)` peel, the selected
  receiver is no longer saturated at the peeled residual, so its remaining
  receiver charge is nonnegative by `lem:typeA-exit4-peeling-charge`. -/
  | typeAExitFourReceiverDischarged
  /-- Node `[103]`, yes arm: the exact selected saturated-handoff residual
  after no exit `(4)` carries exit `(5)`, a target-complete proper-support
  compression. -/
  | typeAExitFive
  /-- Node `[103]`, no arm: the exact selected saturated-handoff residual
  after no exit `(4)` carries no target-complete proper-support compression,
  so the branch may continue to exit `(6)`. -/
  | typeAExitFiveFree
  /-- Node `[105]`, yes arm: the selected saturated-handoff residual, after
  exits `(4)` and `(5)` have failed, has a response equality that becomes
  target-complete only after adjoining a larger connected support. -/
  | typeAExitSix
  /-- Node `[105]`, no arm: that same selected residual has no exit-`(6)`
  delocalization, so it can continue to exit `(7)`. -/
  | typeAExitSixFree
  /-- Node `[106]`, proper scope: the enlarging support is proper in `G`, so
  `lem:proper-smearing` gives the replacement contradiction. -/
  | typeAExitSixProper
  /-- Node `[106]`, global scope: `lem:no-silent-global-smearing` gives a
  strictly smaller closed representative. -/
  | typeAExitSixGlobal
  /-- Node `[110]`, exit `(8)`: the selected route-8 residual satisfies the
  silent-core residual profile.  This is a semantic fact about the selected
  residual state, not an indexed carrier or basin transport object. -/
  | route8ResidualProfile
  /-- Node `[112]`: the selected route-`8` residual carries the basin-burden
  lower side of `lem:typeA-route8-burden`. -/
  | route8BasinBurden
  /-- Node `[113]`: the same selected route-`8` residual carries the
  large-budget Type A deficit lower side. -/
  | route8LargeBudgetDeficit
  /-- The exact complement of node `[113]`.  The corrected large-budget
  argument must send this arm to the unified target-defect/route-`8` peeling
  ledger; it may not infer the route-`8`-only lower bound from the large-budget
  branch marker. -/
  | route8LargeBudgetDeficitFails
  /-- Node `[114]`: canonical minimal carrier-core facts for every declared
  reading of the selected route-`8` residual. -/
  | route8CarrierCore
  /-- Node `[114]`, `def:typeA-true-route8-residual`: every actual indexed
  entry of the selected route-`8` collection satisfies clauses (R1)--(R4). -/
  | route8TrueResidual
  /-- Node `[114]`, `lem:typeA-carrier-cut-parity`: every surviving target
  event which uses an edge internal to its selected trace basin and an edge
  leaving its ambient piece records at least two distinct incidences from the
  canonical essential carrier core. -/
  | route8CarrierCutParity
  /-- Node `[115]`, yes arm: an actual indexed entry of the selected route-8
  collection has a canonical essential carrier core of cardinality at most
  one. -/
  | route8SmallCoreEntry
  /-- Node `[115]`, no arm: every actual indexed entry of the selected route-8
  collection has a canonical essential carrier core of cardinality at least
  two. -/
  | route8NoSmallCoreEntry
  /-- Node `[116]`: the selected zero/one-core entry realizes exactly one of
  the trace-basin alternatives corresponding to exits `(4)`--`(7)`. -/
  | route8SmallCoreCollapse
  /-- Node `[118]`: a selected two-carrier essential-core entry carries the
  carrier-deletion target-defect witnesses and declared forgotten coordinates
  required by the Q5 clause of exit `(4)`. -/
  | route8CarrierDeletionWitnesses
  /-- Nodes `[119]`--`[120]`: the no-two-carrier branch gives the private
  essential-carrier budget against the selected route-`8` carrier supply. -/
  | route8PrivateCarrierBudget
  /-- Nodes `[111]`--`[113]` and `[120]`: the object-level census of the
  extracted Type A collection `𝒳_A` — the deficit `|R| ≤ N_basin + s·|∂R|`
  (`lem:typeA-route8-burden` in `def:typeA-large-budget-deficit`) and the
  private-carrier rate `((δ+1)s+1)·|∂R| < (δ+1)·|R|` (`τ < 3/13`), at the fixed
  maximal packing. -/
  | route8Census
  /-- Node `[120]`: the private-carrier rate reading of the census alone,
  `((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13` with the
  `o(|R|)` allowance, `rem:route8-carrier-margin`), read from the arm's density
  fact. -/
  | route8Rate
  /-- The complement of the rate reading on an arm whose density fact does
  not decide it (`3/13 ≤ τ`): the manuscript's delicate density interval
  (row 2 of the cold-branch ledger), carried as its own branch. -/
  | route8RateFails
  /-- `thm:branch-kill`'s all-pieces classification: every negative piece of
  the canonical decomposition is silent-first when it has no ambient surplus,
  and is a Type B bridge component when it has positive surplus.  This is not
  node `[111]`. -/
  | route8PiecesClassified
  /-- Node `[123]`, `def:typeA-unified-negative`: the canonical collection of
  exactly the zero-surplus negative supports which produce no decorated Type B
  handoff, together with its cleared total deficit. -/
  | route8UnifiedNegative
  /-- Node `[123]`, `lem:typeA-unified-deficit`: the unified collection carries
  the whole large-budget deficit — `|R| ≤ s·D̃_A + s·|∂R| + 2F·s·T(n)`. -/
  | route8UnifiedDeficit
  /-- Node `[123]`, `def:typeA-unified-entries` with `lem:typeA-unified-carriers`
  and `def:typeA-pressure-ledger`: every unified entry has its selected basin,
  at least two essential incidences, and is a route-8 entry with no exit-(4)
  witness or a target-defect entry through alternative (a) with its witness. -/
  | route8UnifiedEntryCensus
  /-- Node `[123]`, the repaired failed-stage arm: a recorded target-defect
  peel chain, the exact partition of the full ledger into reduced and peeled
  entries, both deficit inequalities, and failure of the sufficient stage
  rate. -/
  | route8StageRateFailed
  /-- Node `[123]`, `def:typeA-pressure-absorbers` with
  `lem:typeA-pressure-absorber-no-overcount`: on every committed maximal
  2/3-demand ledger, a type-(A1)/(A2) absorption of its demand units — fresh
  single-use boundary incidences on the absorbed set and a disjoint type-(A2)
  dependence set — with the subtraction-free display
  `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`. -/
  | route8DemandAbsorption
  /-- The (O2) maximal-absorption consequence on the same demand units. -/
  | route8OpenBoundarySaturated
  /-- The number of actual demand units equals the external demand defect. -/
  | route8DemandUnitCount
  /-- Node `[123]`, `def:typeA-open-window-blocker` with
  `lem:typeA-open-window-blocker-count`: every open demand unit of the
  committed absorption is assigned a packed window through a boundary
  incidence of its component support, and the open demand is exactly the
  window-blocker load partition `𝖯_open = Σ_P B_open(P)`. -/
  | route8WindowBlockers
  /-- The actual corridor/window cycle witnessing a recorded shadow hit. -/
  | windowShadowHitCycle
  /-- Selection excludes every recorded shadow hit on the same object. -/
  | windowShadowHitExcluded
  /-- Node 182: one-entry augmentation exhausts every unpaid entry with
  three private carriers; the no-exit-(4) arm routes to node 124, and the sole
  survivor consists of two-carrier unpaid entries with canonical exit-(4)
  witnesses. -/
  | route8UnpaidExitFourResidual
  /-- Node `[184]`, `lem:typeA-unified-visible-ownership`: on the exact
  post-`[181]` unified entry family, every retained load is visibly owned by
  an actual receiver-entry return.  Equivalently, the silent subfamily has
  cardinality zero. -/
  | route8UnifiedVisibleResidual
  /-- Node `[185]`, `lem:typeA-unified-visible-overload`: every retained
  visible excess entry lies at a receiver with an actually overloaded
  completion port.  The canonical visible-four package is retained, and the
  non-overloaded subfamily has cardinality zero. -/
  | route8UnifiedVisibleOverload
  /-- Node `[186]`, `lem:typeA-unified-joint-balance`: the failed peel rate,
  unified deficit, committed maximal demand ledger, and maximal type-(A1)
  absorption are read simultaneously.  Their exact cardinality identities
  and the four resulting inequalities are retained on the visible-overload
  residual. -/
  | route8JointBalance
  /-- Node `[117]`, yes: some indexed route-8 entry of `𝒳_A` has at most `δ`
  private essential carriers (`prop:typeA-route8-carrier-reduction`). -/
  | route8TwoCarrierEntry
  /-- Node `[117]`, no: every indexed route-8 entry has more than `δ` private
  essential carriers. -/
  | route8NoTwoCarrierEntry
  /-- Node `[118]`, `thm:large-budget-route8-only`'s two-carrier split: the
  selected two-carrier entry is a *true route-8 entry* — its load has no
  exit-`(4)` witness at its own receiver (exits `(1)`--`(7)` absent there,
  `def:typeA-true-route8-residual`). -/
  | route8TrueTwoCarrierEntry
  /-- Node `[123]`, `thm:large-budget-route8-only`'s procedure on the object-level
  census: from the empty peeling, target-defect peels
  (`lem:typeA-pressure-is-exit4-peel`, `lem:typeA-exit4-finite-descent`) reach a
  stage with a true two-carrier entry of the peeled ledger or a stage where the
  stage rate fails (`Graph.Route8Pressure.StageOutcome`). -/
  | route8PeelingDescent
  /-- Node `[123]`, terminal survivor of the unified peeling ledger: an
  unpeeled two-support entry with no exit-`(4)` target-defect witness.  This is
  kept distinct from the pure collection's `route8TrueTwoCarrierEntry`. -/
  | route8UnifiedTrueTwoCarrierEntry
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
  /-- Node `[132]`, exit arm of `lem:sparse-pair-dependence-exit`: the
  dependence of a blocked pair's response coordinates is settled by a sparse
  surplus exit of `def:named-surplus-exits` rather than by a canonical blocker.
  It closes the branch against node `[125]`'s survivor entry at `[133]`. -/
  | sparsePairExit
  /-- Node `[125]`, the named-exit payload of the exit arm: clause (b) stated
  about G at G's canonical witness `sparseTargetDefectWitness` -- the identified
  pair of declared coordinates and their canonical support `Z`, separated by G's
  own surroundings `G − Z`.  Incompatible with `K .sparseTargetDefectEmpty`,
  which closes the exit arm. -/
  | sparseTargetDefectResidual
  /-- Node `[132]`, blocker arm: no sparse surplus exit occurs, and the blocked
  pair of `[130]` at G's canonical activation has its canonical blocker
  `Φ_can(π) = min_≺ 𝖡𝗅𝗄(π)` of `def:canonical-blocker-ledger`.  This is the arm
  the canonical blocker ledger `[134]` is levied on. -/
  | canonicalBlockerRoute
  /-- `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's
  `m ≤ 2n − 2` at its own `δ = 3`.  It is `lem:no-proper-core`'s degeneracy --
  every proper subgraph misses the baseline, so the object less a vertex sitting
  exactly at the baseline is `(δ − 1)`-degenerate -- spent against
  `lem:deletion-critical`'s tight endpoint. -/
  | sparseUpperEnvelope
  /-- Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with
  `lem:primitive-carrier-supply`, `def:capacity-token-ledger` with
  `lem:capacity-token-supply` and `lem:token-ledger-no-overcount`, and
  `def:same-token-patterns`: `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 3(δ−1)n`, the
  manuscript's `≤ 6n`, spent against the sparse upper envelope the same node
  proves; the three-summand token universe `𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W` with
  `|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)` and `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, the
  manuscript's `≤ 8n + σ(G)`, both unconditional; the four-case charge `Θ_cap`
  landing in `𝔗_cap` with its fibre identity `|Π_blk| = Σ_t ℓ_cap(t)` read at the
  whole blocked family; the fibre graph `H_t` with `e(H_t) = ℓ_cap(t)`; and the
  existence of the object's capacity-token ledger at every declared
  presentation. -/
  | capacityTokenLedger
  /-- Node `[137]`, `lem:exact-surplus-pair-charge-partition` with
  `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
  `thm:sharp-surplus-overload-audit` (b)--(c): at the object's capacity-token
  ledger, `C(𝒜₀,2)` decomposes exactly into `Π_free` and the class/token/role
  fibres, the class and subtype loads sum to `|Π_blk| ≥ N_*(G)`, their supplies
  sum to `|𝔗_cap|`, and a class with no role-homogeneous `L`-pattern is capped
  by `Cap_hom(L)S_C`. -/
  | roleFibrePartition
  /-- Nodes `[137]`--`[143]`, `lem:capacity-token-high-load` with
  `cor:forced-homogeneous-same-token-scale`,
  `thm:sharp-classwise-homogeneous-token-budget` (e) and
  `thm:sharp-surplus-overload-audit` (d): the object's *own* capacity-token
  ledger realizes the coupled high-load display `C(s,2) ≤ E + L_max|𝔗_cap|`, a
  role fibre there carries at least a `Q_st`-th of the load and all of the
  forced demand `N_*(G)` up to the token supply, and contains a matching or a
  star of size `ψ` of its own count. -/
  | fibrePressure
  /-- Node `[137]`, `cor:spine-lower-bound-surplus-estimates`: a lower-bound
  package of `def:spine-lower-bound-deficits` that bounds the pair schedule
  bounds the surplus, `σ(G) ≤ 1 + √(2 D_win)`.  This is what the near-cubic
  route `[138]` carries away from the block. -/
  | spineSurplusEstimate
  /-- Node `[137]`, near-cubic arm of
  `prop:single-graph-sparse-pressure-routing` (a): every capacity-token ledger
  of the object respects the geometric caps, so `σ(G) ≤ R_L(n)`.  Routes to
  `[138]`. -/
  | sparsePressureNearCubic
  /-- Node `[137]`, overload arm of
  `prop:single-graph-sparse-pressure-routing` (b) with
  `cor:coupled-single-graph-overload-budget` and
  `cor:quantified-homogeneous-class-overload`: some capacity-token ledger of the
  object has `D_all > 0`, and a role fibre absorbing its share over the
  `Q_st|𝔗_cap|` slots carries a role-homogeneous same-token matching or star.
  `class(t)` routes to `[140]`, `[142]` or `[143]`. -/
  | sparsePressureOverload
  /-- Node `[131]`, yes arm: `prop:sparse-entropy-sandwich`'s entropy count at
  the full pair schedule holds — the mixed spine/pair family's `2^k` code is
  realized among the labelled skeletons of the current object. -/
  | freePairEntropySandwich
  /-- Node `[131]`, complementary arm: the residual on which that count fails
  (the free-pair code is not realized by the skeleton class), carried as a
  branch of its own. -/
  | freePairCodeUnrealized
  /-- Node `[137]`: the exact capacity presentation and node-`[129]` baseline
  realization, assembled through `FactInputs.get` before the entropy split. -/
  | blockedPairEntropySetup
  /-- Node `[137]`, yes arm of the entropy count at every declared capacity
  presentation: `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)` for the ledger's free side. -/
  | blockedPairEntropySandwich
  /-- Node `[137]`, complementary arm: at some declared presentation the free
  side's code is not realized by the skeleton class; carried as a branch. -/
  | blockedPairCodeUnrealized
  /-- Node `[178]`: the route-independent least failed pair extension, with
  the failed pair's canonical connected response support. -/
  | pairOverlapFirstFailure
  /-- Node `[178]`: the exact pair-response conditional fibre, realized joint
  states, realizing orders, obstructions, overlaps, and support unions. -/
  | pairOverlapSystem
  /-- Node `[178]`, factorizing arm: the exact retained pair-response system
  satisfies the manuscript's conditional product and concatenation clauses. -/
  | pairConditionalFactorization
  /-- Node `[182]`: the exact retained residual where one of the paper's
  `[178]`--`[180]` implications is not exhaustive.  This is not relabelled as
  a clause-(e) blocker, sparse exit, or Type B witness. -/
  | pairConditionalFactorizationResidual
  /-- Node `[178]`, `lem:pair-failure-overlap`: a minimal pair-code defect in
  the current conditional fibre whose canonical overlap support is connected. -/
  | pairFailureOverlap
  /-- Node `[179]`: the two literal demands of the failed pair, their
  canonical port returns, the connected `X_π ∪ R_p ∪ R_q` connector, and the
  graph-derived return-length bound used in `D_sp`. -/
  | pairDemandReturns
  /-- Node `[179]`: the exact obstruction satisfies one of the five outcomes
  of `lem:pair-system-realizability`. -/
  | pairSystemRealizability
  /-- Node `[179]`, alternatives (i)--(iv), retained for their literal route;
  (iv) is the first-separator handoff of the obstruction's own overlap support
  at `P₀`. -/
  | pairSystemEarlyOutcome
  /-- Node `[179]`, alternative (v): the graph-realized serial demand system. -/
  | pairSerialDemandSystem
  /-- Node `[180]`: corrected arithmetic or a periodic-response route. -/
  | pairIncrementCovered
  /-- Node `[180]`, periodic-response sparse-exit or Type B route. -/
  | pairIncrementEarlyOutcome
  /-- Node `[180]`, corrected full-modulus serial arithmetic input. -/
  | pairSerialArithmetic
  /-- Node `[180]`, the actual accepted power-of-two cycle. -/
  | pairPowerOfTwoCycle
  /-- Node `[139]`, yes arm: the overloading token of node `[137]` lies in
  `𝔗_W`, so the branch enters the window-incidence audit `[140]`. -/
  | windowClassOverload
  /-- Node `[139]`, no arm: the selected overloading token does not lie in
  `𝔗_W`, so that same witness falls through to node `[141]`. -/
  | windowClassAbsent
  /-- Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch
  enters the remainder-surplus audit `[142]`. -/
  | remainderClassOverload
  /-- Node `[141]`, no arm: the selected overloading token lies in
  `𝔗_prim`, so that same witness enters `[143]`. -/
  | remainderClassAbsent
  /-- Node `[144]`, the tested half of
  `thm:homogeneous-overload-geometric-closure`: no capacity token of the object
  supports a role-homogeneous same-token `L_geom`-matching or `L_geom`-star, at
  the counted routing-label alphabet.  This is the subbranch the manuscript's
  fixed caps `L_W = L_R = L_P = L_geom` hold on.  After the audits it is
  refuted by `K .homogeneousBottleneckPattern` (paper error at `[144]`,
  `not_homogeneousCapsHold_of_pattern`); the arm is kept as the paper draws
  it. -/
  | homogeneousCapsHold
  /-- Node `[144]`, the other arm: the exact complement of the fixed caps.
  Some capacity presentation and ledger of the object has a token supporting a
  role-homogeneous same-token `L_geom`-matching or `L_geom`-star. -/
  | homogeneousCapsFail
  /-- Nodes `[140]`, `[142]`, `[143]`, the geometric audit of the selected
  overload: its token supports a role-homogeneous same-token `L_geom`-matching
  or `L_geom`-star, with every declared same-root connector configuration.
  `lem:same-token-bottleneck-routing` reads it as a sparse surplus exit or as
  decorated Type B handoff fan data. -/
  | homogeneousBottleneckPattern
  /-- Node `[144]`, `lem:same-token-bottleneck-routing` itself: the concrete
  homogeneous pattern in the current object's canonical capacity presentation
  yields a sparse-surplus exit or the common Type B fan-ledger entry. -/
  | bottleneckRouting
  /-- Node `[144]`, the survivor specialization of the preceding fact: the
  sparse-exit arm is impossible, so the same current object is entered directly
  in the Type B fan ledger. -/
  | typeBHandoff
  /-- Node `[144]`, the exact complement of the same-token handoff. -/
  | typeBHandoffFails
  /-- Node `[144a]`, the residual of the paper error at `[144]`: the
  unresolved same-label pattern pair. -/
  | sameTokenPatternUnresolved
  /-- Node `[144]`, `cor:homogeneous-same-token-caps-close` at the counted
  `L_geom` and the ledger's own token supply: every token load is at most
  `M₀ = Cap_hom(L_geom)`, hence `|Π_blk| ≤ M₀|𝔗_cap|`,
  `σ(G) ≤ 1 + 2M₀ + √(2E + 2M₀·scale)`, and the edge-count half
  `m = (3/2)n + O(√n)`. -/
  | homogeneousBottleneck
  /-- Node `[125]`, `def:named-surplus-exits`: the selected object survives the
  five sparse surplus exits.  This is the standing hypothesis every node of the
  block reads, derived from the selection entry rather than assumed. -/
  | sparseSurplusSurvivor
  /-- Node `[125]`, `def:active-surplus-demands` with
  `lem:surviving-active-family`: the active family is the excess-port family,
  it has `σ(G)` members, and every member carries its canonical return path. -/
  | activeSurplusDemands
  /-- Node `[22]`: the canonical hot/cold partition of the maximal packing.
  The witnesses are derived on the incoming residual; they are not supplied as
  routing data. -/
  | hotColdPartition
  /-- Node `[130]`, blocked arm of "blocker-free?": at G's canonical
  activation some scheduled pair has a nonempty blocker set over all six
  clauses of `def:surplus-blockers` (`Π_blk ≠ ∅`). -/
  | dependentPairFamily
  /-- Node `[130]`, blocker-free arm: the exact negation at the same
  activation (`Π_blk = ∅`). -/
  | independentPairFamily
  /-- Node `[131]`, `lem:mixed-sparse-spine-dependence` at G's canonical spine
  family and activation: a non-independent mixed family gives a sparse exit
  or a type-(d)/(e) blocker.  No row consumes it: `[131]`'s count is a
  registered branch test. -/
  | mixedSparseSpineDependence
  /-- Node `[131]`, the two-sided exact cubic baseline budget at the current
  residual's order and registered baseline. -/
  | exactCubicBaselineBudget
  /-- Node `[131]`, the incremental skeleton room above the exact cubic
  baseline and its surplus-slack bound. -/
  | incrementalSkeletonRoom
  /-- `lem:skeleton-dominates` at the current residual's exact order and edge
  count: the fixed-edge labelled skeleton class has exactly the registered
  skeleton budget, and every canonical state map realizes at most that many
  states. -/
  | skeletonDominates
  -- F4 keys
  /-- Node `[131]`, count fails: the exact negation of `freePairEntropySandwich`. -/
  | freePairCountFails
  /-- Node `[137]`, free-side count fails: the exact negation of
  `blockedPairEntropySandwich`. -/
  | blockedPairCountFails
  /-- Node `[132]`, blocker arm: the exact negation of `sparsePairExit`. -/
  | blockedPairNoExit
  /-- Node `[143]` entry: the overloading token is primitive. -/
  | primitiveClassOverload
  /-- Node `[178]`, no factorization: the exact negation of
  `pairConditionalFactorization`. -/
  | pairFactorizationFails
  /-- Node `[179]`, no exhaustive uncrossing: the exact negation of
  `pairSystemRealizability`. -/
  | pairRealizabilityFails
  /-- Node `[179]`, serial arm: the exact negation of `pairSystemEarlyOutcome`. -/
  | pairSystemNoEarlyOutcome
  /-- Node `[180]`, uncovered increment: the exact negation of
  `pairIncrementCovered`. -/
  | pairIncrementFails
  /-- Node `[180]`, arithmetic arm: the exact negation of
  `pairIncrementEarlyOutcome`. -/
  | pairIncrementNoEarlyOutcome
  -- S182 keys (8200–8249): the [182] audit, node [178]--[180] facts stated about G
  /-- Node `[178]`, the correlation mass of G's canonical overlap system: along
  the canonical rank order of the failed prefix, the exact realized-signature
  counts `P_k` (`P_0 = 2^b`, `P_k ≤ P_{k+1} ≤ 2 P_k`, `P_t ≤ |class|`), the
  mass identity `2^{b+t} ≤ |class| + mass`, and the first non-branching index. -/
  | pairCorrelation
  /-- Nodes `[179]`--`[180]`, coverage decided at G: for G's canonical return
  system and serial system, the realizability outcome is the Type B handoff or a
  serial system on those returns; the arithmetic input does not exist; the
  increment outcome is the Type B handoff of the serial returns. -/
  | pairCoverage
  /-- Node `[180]`, the full-modulus arithmetic of G's canonical serial system: its
  canonical Frobenius-filled data does not satisfy all of `FullModulusArithmetic`. -/
  | pairFullModulus
  /-- Node `[179]`, the uncrossing of G's canonical connector routes: the closing
  cycle of disjoint routes, or the two rerouted paths at the first and last common
  vertex, each with a non-accepted closing length. -/
  | pairUncrossing
  -- F1 keys
  /-- Node `[86]`: the Type A support `X₀`, `s·def⁺(X₀) < |V(X₀)|`. -/
  | typeASupport
  /-- Node `[93]`, no arm: no saturated receiver of `X₀` has an overloaded completion port. -/
  | typeANoVisibleEntry
  /-- Node `[101]`, no arm: the entry state of the exit-chain receiver of `X₀` has no exit `(4)`. -/
  | typeAExitFourAbsent
  /-- Node `[106]`, proper scope: the canonical exit-`(6)` delocalization adjoins a proper support. -/
  | typeAExitSixProperScope
  /-- Node `[106]`, whole-graph scope: the canonical exit-`(6)` delocalization adjoins all of `G`. -/
  | typeAExitSixGlobalScope
  -- F3 keys
  /-- Node `[124]`, `lem:typeA-carrier-deletion-exit` on the route-`8` collection `𝒳_A`:
  every two-support entry of `Ξ(𝒳_A)` carries its canonical exit-`(4)` witness. -/
  | route8TwoCarrierExit
  /-- Node `[124]`, `lem:typeA-carrier-deletion-exit` on the unified collection:
  every two-support entry of `Ξ̃` carries its canonical exit-`(4)` witness. -/
  | route8UnifiedTwoCarrierExit
  /-- Node `[123]`, yes: the reduced-rate test passes at the terminal stage of the
  exit-`(4)` descent. -/
  | route8StageRate
  /-- Node `[181]`, (168.1): every unpaid entry of a maximal demand ledger is
  two-support. -/
  | route8UnpaidTwoCarrier
  /-- Node `[181]`, yes: some unpaid entry of a maximal demand ledger has no
  exit-`(4)` witness. -/
  | route8UnpaidWitnessFree
  -- R3 keys (7900–7949): route 8 and Type A stated about G
  /-- Node `[123]`, stated about G (Lean improvement): **the quotient-free arm of
  the unified route-`8` ledger is empty at G** — every essential core is empty
  (`α(ξ) = 0`), so the census's `2 ≤ α(ξ)` leaves no unified entry, the stage
  accounting clears `s·D̃_A`, and `|R| ≤ s·|∂R| + F·s·T(n)`. -/
  | route8UnifiedEmptyAtG
  -- R8Q keys (8150–8199): the route-8 quotient test stated about G
  /-- Node `[348]`, stated about G (Lean improvement): **the quotient test is
  decided at G** — alternative (b) is present at every routed load, so
  quotient freeness fails exactly when the unified entry family is nonempty;
  at every unified entry `α(ξ) = 0`, the quotient is present, the canonical
  representative of G's piece at `B_u` has the size of the piece (a valid
  replacement is not smaller), and the exit-`(5)` datum is absent. -/
  | route8QuotientEntriesAtG
  -- Type B sublinear audit keys (8300–8349)
  /-- G audit of `TypeBSublinearOutcome`, `prop:typeB-bridge-sublinear`: **the
  tested hypotheses in G's canonical form** -- every existential is pinned to a
  canonical object of G, so the hypotheses are exactly the bridge, centre-height,
  handoff and cover arms over G's canonical objects. -/
  | typeBSublinearCanonicalForm
  /-- G audit of `TypeBSublinearOutcome` (Lean improvement): **G's canonical
  absorbed core of a piece lies in the piece**, so the clause `absorbedAt ⊆ piece`
  of the sublinear hypotheses is empty as a failure arm at G. -/
  | groupedAbsorbedCoreSubset
  /-- G audit of `TypeBSublinearOutcome`: **the exact decomposition of the failed
  sublinear hypotheses at G** into a route-`8` bridge piece of positive surplus, a
  failing decorated handoff piece, a non-high grouped centre, or a failed cover
  inequality. -/
  | typeBSublinearFailureArms
  /-- G audit of `TypeBSublinearOutcome` (Lean improvement): **the grouped centres
  of G are high** (a surviving first separator has degree at least `4`), so the
  height clause of the sublinear hypotheses is empty as a failure arm. -/
  | groupedCentresHigh
  /-- G audit of `TypeBSublinearOutcome` (Lean improvement): **the degree clause
  of the handoff clauses is empty at G**: a decorated handoff piece has zero
  ambient surplus, so no vertex of it has internal degree above the baseline. -/
  | handoffDegreeClauseEmpty
  /-- G audit of `TypeBSublinearOutcome`: **G's canonical routing is total on the
  pieces of the remainder** (`K .remainderNormalized`): every flat vertex of a
  canonical piece is routed by `traceReceiver?` to a receiver of the piece. -/
  | pieceRoutingTotal
  /-- G audit of `TypeBSublinearOutcome`: **the incidence payment of the cover
  arm**: the cover inequality fails only if an absorbed vertex of a decorated
  handoff piece is a cubic-closed neighbour of no grouped centre. -/
  | coverPayment
  /-- G audit of `TypeBSublinearOutcome` (gap H05): **a load failure of the
  sublinear test is a saturated receiver of the piece** (the restricted load is a
  sub-count of the routed load). -/
  | loadFailureSaturated
  /-- G audit of `TypeBSublinearOutcome` (gaps H06, H07): **the Hall violator of
  the cover network is a window port**: an unpaid absorbed vertex is adjacent to
  its grouped centre and has another neighbour in the packed windows. -/
  | unpaidAbsorbedWindowPort
  /-- G audit of `TypeBSublinearOutcome` (gap H05): **the ports of a receiver are
  window stubs**: `missingPorts` is the number of incidences leaving the remainder,
  and `def⁺` of a piece is the sum of its receivers' ports. -/
  | receiverPortsAreWindowStubs
  /-- G audit of `TypeBSublinearOutcome` (gap H05): **the structure of a saturated
  receiver**: a trace basin of at least `s · missingPorts` full vertices of the
  piece. -/
  | saturatedReceiverBasin
  /-- G audit of `TypeBSublinearOutcome` (gap H07): **the value of the load
  network**: flat vertices plus receivers are at most `s · Σ missingPorts` when
  every receiver is unsaturated and routing lands outside the excluded set. -/
  | loadFlowValue
  /-- G audit of `TypeBSublinearOutcome` (gap H07): **the value of the cover
  network**: absorbed cardinalities are at most the closed counts plus the unpaid
  count, absorbed cores have at most two vertices. -/
  | coverFlowValue
  /-- G audit of `TypeBSublinearOutcome` (gap B01): **the component size profile
  of the remainder**: pieces partition `R(P₀)`, each has a receiver, and their
  number is at most `def⁺(R(P₀))`. -/
  | pieceSizeProfile
  -- R3b keys (7960–7979): the switch at the separator, constructed from G
  /-- Node `[102]` at G (Lean improvement): **the exit-(4) peel is a switch
  peel** — the canonical witness is a Q4 member whose switch at the separator
  (the two configurations exchange their continuations after `z`) is a proper double-edge
  switch with an accepted cycle through an exchanged edge. -/
  | typeAExitFourSwitchCycle
  /-- Node `[108]` at G: **at the canonical handoff separation the switch at `z`
  has no accepted cycle and the separator has an unused ambient incidence; the
  switched graph is a counterexample of G's size (same vertices, same edge
  count, the baseline)**. -/
  | typeAExitSevenSwitch
  -- F5 keys
  /-- Node `[175]`, no arm: every selected corridor meets a high-degree
  vertex. -/
  | coldNoPositiveGerm
  -- SD keys (final pass)
  /-- Node `[11]`, `lem:degree-profile-fibres`: an admissible quotient of G's
  declared coordinates never identifies two realizations in different
  boundary-degree fibres. -/
  | degreeProfileFibres
  /-- Node `[12]`, `lem:context-universality`: identifications of G's admissible
  quotients are target-complete, and an identification valid only at G's own
  outside context is target-defective. -/
  | targetCompleteContextUniversality
  /-- Node `[16]`, `thm:p13free` on the window-free arm: G has an accepted
  cycle. -/
  | hssTargetCycle
  -- SP keys (fix2)
  /-- Node `[130]`, blocker clause (e) at G's canonical activation: some
  scheduled pair has a type-(e) obstruction. -/
  | pairResponseObstruction
  /-- Node `[130]`, blocker clause (e) absent at G's canonical activation. -/
  | pairNoResponseObstruction
  /-- Node `[130]`, `lem:degree-profile-fibres` at G's pair family. -/
  | pairDegreeProfileFibres
  /-- Node `[130]`, blocker clause (d) at G's canonical activation: some scheduled pair has a type-(d) obstruction. -/
  | pairProfileObstruction
  /-- Node `[130]`, blocker clause (d) absent at G's canonical activation. -/
  | pairNoProfileObstruction
  /-- Node `[144a]`: no reading of G's piece at the pattern support is a replacement representative. -/
  | sameTokenReadingsNotReplacement
  /-- Entry (after `[1]`--`[3]`): **The two-edge switch of G forces a path**: for edges `u₁v₁`, `u₂v₂` of G with distinct ends, `u₁ ≁ u₂` and `deg v₁, deg v₂ ≥ δ + 1`, `G − {u₁v₁, u₂v₂}` has a simple `u₁`–`u₂` path `p` with `|p| + 1` accepted. -/
  | twoSwitchForcedPath
  /-- Entry (after `[9]`/`[10]`): **The vertex split of G at every high centre forces a cycle**: at every `h` with `deg h > δ`, `G ⊔ M_h` (`M_h` the non-adjacent pairs of `N(h)`) has an accepted cycle avoiding `h` and using an edge of `M_h` absent from G. -/
  | highCentreSplitForced
  /-- Entry (after `[1]`--`[3]`): **The cross-vertex switch family of G**: at an edge `u₁v` and a vertex `h' ≠ v` with `deg v, deg h' ≥ δ + 1`, every neighbour `u ≁ u₁` of `h'` has a forced `u₁ → u` path in `G − {u₁v, uh'}` with accepted closing length, and two `2^j − 1` paths from `u₁` into two neighbours of `h'` are never `h'`-free and internally disjoint (the dyadic star). -/
  | crossSwitchFamily
  /-- Entry (after `[5]`/`[6]`): **The same-vertex switch of G forces a path, split exactly**: for non-adjacent neighbours `u₁ ≠ u₂` of `h` with `deg h ≥ δ + 2`, `G − {hu₁, hu₂}` has a simple `u₁`–`u₂` path `p` with `|p| + 1` accepted, and either `p` avoids `h` with `|p| + 2` not accepted, or `p` splits at `h` into two returns `ℓ₁ + ℓ₂ = |p|` with neither `ℓᵢ + 1` accepted. -/
  | sameVertexSwitchForcedPath
  /-- Node `[144]` (after the routing of `lem:same-token-bottleneck-routing`): **The pattern supports of G's canonical routing**: G's canonical routing exists and each pattern support `X_π` (`π ∈ {p, q}`) is `select?(seed(π))`, connected, with two distinct vertices. -/
  | sameTokenPatternSupports
  /-- Node `[144]` (after the routing): **The swaps of G's two pattern readings**: at G's canonical routing, swapping `ret_q` by `ret_p` (and conversely) gives G itself, or loses the baseline at a tight endpoint `w` of a private edge, `deg(w) ≤ δ − 1`. -/
  | sameTokenPatternSwap
  /-- Node `[144a]`: **The exact partition of G's unresolved pattern pair**: at G's canonical routing, supports `X_p = select?(seed(p))`, `X_q = select?(seed(q))` and `Z = select?(X_p ∪ X_q)` (`X_p, X_q ⊆ Z`, `Z` connected): (U1) a boundary vertex with different counts, both `≤ deg b − 1`, retained with a neighbour by one support and adjacent to its seed or cutting it; or equal counts with transfer, context equivalence and equal `a`–`b` path-length spectra, and (U2-free) neither support on `∂Z` (every `∂Z` vertex a connector cut vertex, `N(X_p ∪ X_q) ⊆ Z`) or (U2-shared) a boundary vertex in both supports.  The one-sided region is empty. -/
  | sameTokenPairPartition
  -- Returned residuals (fix3, 3200-3249)
  /-- Node `[153]`, distinct-states arm: G's pinned cut states along each retained cold corridor are pairwise distinct up to the first failure. -/
  | coldCutStatesDistinct
  /-- Node `[153]`, returned residual: G's first equal-state pair on a retained cold corridor, with its separating context and profile separation. -/
  | coldRepeatedStateResidual
  /-- Node `[162]`: the heavy entry of every retained corridor of G is read within `Q_cold` states (a first failure at a heavy centre lies below `Q_cold` on the distinct-states arm); nothing about the length of the corridor beyond it is asserted. -/
  | coldHeavyEntryTerminal
  /-- Node `[54]`, joint arm: `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` at G. -/
  | entropyJointRealization
  /-- Node `[54]`, returned residual: the configuration at G where the joint realization inequality fails. -/
  | allColdEntropyResidual
  -- C6 keys (density order)
  /-- Node `[146]` no with `[158]` yes: the realized package's entropy count against the `[146]`-no lower bound, combined at G (`Graph.DensityOrderBound`). -/
  | realizedDensityOrder
  /-- Node `[146]` no with `[158]` yes, size test yes: `N₀ ≤ n` at the realized cutoff (the rate margin and the baseline included). -/
  | realizedOrderLarge
  /-- Node `[146]` no with `[158]` yes, size test no: G has fewer than `N₀` vertices (exact complement). -/
  | realizedOrderSmall
  /-- Node `[24]` on `[146]` no: the density cap against the `[146]`-no lower bound, combined at G (`Graph.DensityOrderBound`). -/
  | boundedDensityOrder
  /-- G audit `Route8RateFailsOutcome` (idx 8250): the failed private-carrier rate against the exact window join at `P₀`: `e(R,W) + 2(order−1)p + X = δ·order·p + σ_W` and `δ·n + (δs+1)·X ≤ A·p + D·T(n)`, `X` the cross-window incidences. -/
  | route8RateFailsJoin
  /-- G audit `Route8RateFailsOutcome` (idx 8251): the failed private-carrier rate on the connected pieces of G's remainder: `Σ|X_i| = |R|`, `Σ|∂X_i| = |∂R|`, and a piece with `m·δ·|X| ≤ m·(δs+1)·|∂X| + δ·F·s·T(n)`. -/
  | route8RateFailsPiece
  /-- G audit `Route8RateFailsOutcome` (idx 8252): the failed private-carrier rate against the exact window join and the density cap, with the cross-window incidences `X` kept: `2·r·L·(δn + (δs+1)X) ≤ A(L+1)(δn+T) + L·T·(A·S + 2rD)`. -/
  | route8RateFailsCrossBound
  /-- G audit `Route8RateFailsOutcome` (idx 8253, `H07`): the integral stub-to-deficit flow at `R` and its pieces, `def⁺ ≤ |∂X| ≤ def⁺ + σ`, the window stub capacity delivered to the deficit and surplus of `R`, and the failed rate in deficit currency. -/
  | route8RateFailsFlow
  /-- G audit `Route8RateFailsOutcome` (idx 8254, `H06`): the carriers-to-cut injection of the canonical route-8 entries of `P₀`: cores lie in the cut and private cores total at most `|∂R|`. -/
  | route8CarrierInjection
  /-- G audit `Route8RateFailsOutcome` (idx 8255, `H08`): the rate at G's exact `σ(G)` next to the ceiling version: exact rate holds strictly inside the failed ceiling rate, or the exact rate fails. -/
  | route8RateExactSlack
  /-- G audit `Route8RateFailsOutcome` (idx 8256): the stub-deficit identity `e(R,W) + exc(R) = σ(R) + def⁺(R)`, the injection of deficit units into cut incidences, and `def⁺(R) + X + σ(R) + 2(order−1)p = δ·order·p + σ_W + exc(R)`. -/
  | route8StubDeficit
  /-- G audit `Route8RateFailsOutcome` (idx 8257): the deficit reaches the window stub capacity (then `X + σ(R) ≤ σ_W + exc`, `d ≤ βp + σ_W`) or falls short of it (then `σ_W + exc < X + σ(R)`). -/
  | route8DeficitVsStubs
  /-- G audit `Route8RateFailsOutcome` (idx 8258): the route-8 entries against the large-budget deficit test: `N_basin ≥ D_A`, and either the test holds with `|R| + s(X + 2(order−1)p) ≤ N_basin + s(δ·order·p + σ_W) + slack` or `D_A + s|∂R| + slack < |R|`. -/
  | route8EntryLowerBound
  /-- G audit `Route8RateFailsOutcome` (idx 8259): every route-8 census core is empty at G (`α(ξ) = 0`), so an entry is a two-carrier entry as soon as it exists. -/
  | route8CoreEmpty
  /-- G audit `Route8RateFailsOutcome` (idx 8260): the strong rate `s|∂R| + F·s·T < |R|` (then `[113]` yes gives a two-carrier entry without the `3/13` rate) or the thin remainder `|R| ≤ s|∂R| + F·s·T`. -/
  | route8StrongRate
  /-- G audit `Route8RateFailsOutcome` (idx 8261): under the net cap the thin remainder forces `X + T < σ_W + F·T` (windows isolated). -/
  | route8ThinIsolation
  /-- G audit `Route8RateFailsOutcome` (idx 8262): exact stub count per window (`exits_R + exits_W + 2(order−1) = δ·order + σ(P)`), its sums `X` and `|∂R|`, and the attached remainder vertices. -/
  | route8WindowStub
  /-- G audit `Route8RateFailsOutcome` (idx 8263): the thin remainder forces the order below the thin cutoff `N₀'` (`DensityOrderBound` at `A' = δ(order + sβ)`, `D' = δs(1+F)`). -/
  | route8ThinSmall
  /-- G audit `Route8RateFailsOutcome` (idx 8264): two windows of `P₀` joined through `R` by two vertex-disjoint paths at fixed stub positions close a cycle of length `|i−i'|+|j−j'|+|r₁|+|r₂|+4` that is not a power of two. -/
  | route8WindowRPathGap
  /-- G audit `Route8RateFailsOutcome` (idx 8265): the incidences from the windows to vertices above the baseline number at most `(δ+1)·σ(G)`. -/
  | route8HubStubs
  /-- G audit `Route8RateFailsOutcome` (idx 8266): a remainder path joining two stubs of one window closes a cycle of length `|i−i'|+|r|+2` that is not a power of two. -/
  | route8WindowSelfRPathGap
  /-- G audit `Route8RateFailsOutcome` (idx 8267): every canonical piece of the remainder has at least two boundary edges (bridgeless) and `2·#pieces ≤ |∂R|`. -/
  | route8PieceBoundary
  /-- G audit `Route8RateFailsOutcome` (idx 8268): cycle rank of the window-piece stub multigraph: `β·p + σ_W ≤ 2(e(R,W) − (p + #pieces)) + 2p + X`. -/
  | route8WindowPieceRank
  /-- G audit `Route8RateFailsOutcome` (idx 8269): the achievable path lengths of a piece between two stubs are nonempty and bounded by the piece size, and every element of the cycle-length sumsets of `B` (one window one piece, two windows two pieces) avoids the powers of two. -/
  | route8AchievableLengths
  /-- Node `[24]` on `[146]` no, size test yes: `N₀ ≤ n` at the `[24]` cutoff. -/
  | boundedOrderLarge
  /-- Node `[24]` on `[146]` no, size test no: G has fewer than `N₀` vertices (exact complement). -/
  | boundedOrderSmall
  -- TA keys
  /-- Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated at its terminal peeling set. -/
  | typeAPeeledSaturatedReceiver
  /-- Node `[91]` after peeling: `|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|`. -/
  | typeAPeeledUnsaturatedDischarge
  /-- Node `[93]` after peeling, yes arm: the terminal state has an overloaded port. -/
  | typeAPeeledVisibleEntry
  /-- Node `[93]` after peeling, no arm: the terminal state has no overloaded port. -/
  | typeAPeeledNoVisibleEntry
  /-- Node `[94]` after peeling: the residual excess `E₄(w)` is nonempty and silent. -/
  | typeAPeeledSilentExcess
  /-- Node `[95]` after peeling, yes arm: exit `(1)` at the terminal overloaded port. -/
  | typeAPeeledExitOneReturn
  /-- Node `[95]` after peeling, no arm. -/
  | typeAPeeledExitOneFree
  /-- Node `[97]` after peeling, yes arm: exit `(2)` at the terminal overloaded port. -/
  | typeAPeeledExitTwoTheta
  /-- Node `[97]` after peeling, no arm. -/
  | typeAPeeledExitTwoFree
  /-- Node `[99]` after peeling, yes arm: exit `(3)` at the terminal overloaded port. -/
  | typeAPeeledExitThreeCollision
  /-- Node `[99]` after peeling, no arm. -/
  | typeAPeeledExitThreeFree
  /-- Node `[100]`: the exit-`(3)` label collision closes an accepted cycle of `G`. -/
  | typeAExitThreeCycle
  /-- Node `[108]`: the canonical exit-`(7)` separation and envelope of `X₀` at the terminal state. -/
  | typeAExitSevenEnvelope
  -- SC keys
  /-- Node `[176]` on the absorbed-configuration residual
  (`lem:absorbed-germ-fan-data` (i)): on the G2-silent arm, the neutral
  equal-length configuration of G's silent extracted family, an (F5)
  configuration (terminal or repeated-state); the dense-residual terminality of
  node `[162]` is not assumed. -/
  | coldAbsorbedNeutralConfiguration
  /-- Node `[176]` on the arm with no positive germ and no absorbed half-edge:
  G's selected cold branch-excess family is empty and G has no ambient-cubic
  cold window. -/
  | coldSelectedFamilyEmpty
  /-- Node `[157]`, the marked neutral equal-length germ of G measured against the compression clause of a table row: `|Q| ≤ M_cold`, `|E| = |Q|`, the support does not enter G's (F4) registry, and `glue E (G − Z)` has the vertex and edge count of G (not strictly smaller). -/
  | coldMarkedGermUncompressed
  /-- Node `[157]`, F08 at the marked germ: for every path of G of length at least 2 spanning the marked germ's support, the excised object (interior deleted, ends joined) misses the baseline or G has a cycle of length `L + q` with `L` accepted and `L + q` not (`q = |p| - 1`). -/
  | coldMarkedGermStretchExcision
  -- [20a] enrichment keys (6606-)
  /-- Node `[20a]`: **Edge–surplus identity**: `2m = δ·n + σ`. -/
  | edgeSurplusIdentity
  /-- Node `[20a]`: **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`: `σ + 6|H| + lowDarts = 3n`). -/
  | surplusDartIdentity
  /-- Node `[20a]`: **High-degree count**: `|H| ≤ σ`. -/
  | highDegreeCountBound
  /-- Node `[20a]`: **At least one high-degree vertex**: `1 ≤ |H|`. -/
  | highDegreePositive
  /-- Node `[20a]`: **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every high vertex has all its neighbours among the `n − |H|` baseline vertices). -/
  | highDegreeSurplusCapacity
  /-- Node `[20a]`: **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`). -/
  | packingOrderBound
  /-- Node `[20a]`: **`C + 1 ≤ ⌈√n⌉`.** -/
  | ceilSqrtAboveScale
  /-- Node `[20a]`: **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`). -/
  | orderAboveScaleSquare
  /-- Node `[20a]`: **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`. -/
  | sixVertexExtremalEnvelope
  /-- Node `[20a]`: **Exit (e) is excluded at G**: no open-port suppression cycle has an accepted lifted length `|walk| + |chords|`. -/
  | noSuppressionChordViolation
  /-- Node `[20a]`: **Every admissible quotient of G is label-injective** on its family. -/
  | admissibleQuotientsLabelInjective
  /-- Node `[20a]`: **The one-boundary shape**: every support `S` with a single boundary vertex `b`, a second vertex and a vertex outside has `b` with exactly two neighbours in `S` and two outside (`deg b = 4`, a 2+2 cut vertex). -/
  | singleBoundaryShape
  /-- Node `[20a]`: **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its remainder). -/
  | remainderDeficiencyBelowCut
  /-- Node `[20a]`: **The window cut capacity** at `P₀`: `e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`. -/
  | windowCutCapacity
  /-- Node `[20a]`: **G's canonical capacity presentation is the explicit one**: the recorded blocker activation of G's active family on the node-`[19]` packing. -/
  | canonicalCapacityExplicit
  /-- Node `[20a]`: **`|𝔘_sp(G)| = 4n + 2σ`.** -/
  | primitiveCarrierCount
  /-- Node `[20a]`: **The exact token count at the canonical presentation**: `|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`: `|𝔗_cap| = 4n + 3σ + 15ν`). -/
  | canonicalTokenCount
  /-- Node `[20a]`: **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger. -/
  | canonicalBlockedFreePartition
  /-- Node `[20a]`: **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`, `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`. -/
  | canonicalLedgerDeficit
  /-- Node `[20a]`: **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`. -/
  | pairCountDeficit
  /-- Node `[20a]`: **The certification criterion at the canonical presentation**: its canonical certified ledger exists iff `|Π_free| ≤ B`. -/
  | canonicalCertificationCriterion
  /-- Node `[20a]`: **The paper's budget at the canonical spine family fits the certification budget**: `E_paper ≤ B`. -/
  | paperBudgetBound
  /-- Node `[20a]`: **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist. -/
  | paperBudgetCertifies
  /-- Node `[20a]`: **If the free side fits `B`, the blocked side is overloaded**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load `> M₀` and carries an `L_geom` role-homogeneous matching or star. -/
  | canonicalOverloadOfFits
  /-- Node `[20a]`: **If every token carries load `≤ M₀`, the free side exceeds `B`**: `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`. -/
  | canonicalFreeExcessOfCapped
  /-- Strict arm of `[19]` (hoisted from `[20a]`; G-only restatement): **Where G sits in the pair-code chain**: either the `[137]`→`[143]` configuration holds at the canonical objects (blocked pair, `[137]` count, canonical pattern, overload, caps fail), or G's canonical first failure exists and yields the `[182]` residual, or the canonical return system's obstruction handoff together with the Type B fan entry `[65]` (the target defect of the obstruction coordinates is exit (b) stated about G, empty at G). -/
  | pairCodeConfiguration
  /-- Entry prefix (G-only restatement; key name kept for ledger stability): **the witness triples of clause (b) at G**: at every triple `(A, B, Z)` with `Z` the canonical support of `A ∪ B`, `Z` is connected, contains `A` and `B`, and is a minimum connected set containing `A ∪ B`; and no triple satisfies clause (b) (`G − Z` never separates two readings of G). -/
  | specWitnessStructure
  /-- Entry prefix (G-only restatement; key name kept for ledger stability): **the readings of every clause-(b) witness triple of G are negative in G's own surroundings `G − Z`** (the split's positive reading never exists in G). -/
  | everyWitnessSpectrumSplit
  /-- Strict arm of `[19]`: **Where the surplus of G sits**: a vertex of degree `≥ δ + 2`, or two distinct vertices of degree exactly `δ + 1`. -/
  | highSurplusConfiguration
  /-- Strict arm of `[19]`: **The switch at every high/baseline edge `hc`**: the same-vertex switch at `h` (`deg h ≥ δ + 2`) or the two-edge switch with a second high vertex forces a path from `c` whose length plus one is accepted. -/
  | highEndpointSwitch
  -- port-cycles keys (6900–6999)
  /-- Entry prefix (cycle counting): **Neighbourhood pairs of G**: at every vertex `h`, `G[N(h)]` is a matching, `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners. -/
  | neighbourhoodPairCount
  /-- Entry prefix (cycle counting): **Star constraint**: two paths `x → y`, `x → z` of `G − h` to distinct neighbours of `h`, meeting only at `x`, have `|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`). -/
  | starCycleConstraint
  /-- Entry prefix (cycle counting): **Meeting constraint**: two paths `x → y`, `x → z` of `G − h` to distinct neighbours of `h` meet at `t` (depths `P₁`, `Q₁`) with `|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` (`k ≥ 2`). -/
  | meetingCycleConstraint
  /-- Entry prefix (cycle counting): **Pair sums at the high vertices** `H = {d ≠ δ}`: `σ = Σ_H (d_h − 3)`, `5σ ≤ Σ_H C(d_h, 2)`, `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and a heavy centre `σ ≤ |H|(d_h − 3)` unless `σ = 0`. -/
  | highDegreePairSum
  /-- Entry prefix (cycle counting): **Vertex deletions**: at every vertex `h`, `G − h` is connected, or `d_h = 2·#blocks(h)` is even and every component of `G − h` meeting `N(h)` holds exactly two neighbours of `h`. -/
  | vertexDeletionComponents
  /-- Entry prefix (cycle counting): **Cycles through every vertex**: `C(d_h, 2) ≤ #cycles(h)` when `G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h / 2 ≤ #cycles(h)`. -/
  | cyclesThroughVertex
  /-- Entry prefix (cycle counting): **Block paths at the cut vertices**: for `G − h` disconnected, the block `{a, b}` of every neighbour `a`, the lengths of its `a → b` paths, its returns, and the cross splits at `h` with their dyadic residues. -/
  | cutVertexBlockPaths
  /-- Entry prefix (cycle counting): **Double count at the high vertices**: `2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` (per-vertex lower bounds), and `#cycles(G) ≤ 2^m`. -/
  | cycleDoubleCount
  -- port-local keys (7100–7199)
  /-- Entry prefix (local rigidity): **The length-3 fan**: at every vertex `h`, two paths `a p₁ p₂ b`, `a q₁ q₂ c` of length `3` of `G − h` from a neighbour `a` of `h` to distinct neighbours `b ≠ c` of `h` have `p₁ = q₁`, `p₂ ≠ q₂`, `p₂ ≠ c`, `q₂ ≠ b` (distinct first steps would close the 8-cycle `h b p₂ p₁ a q₁ q₂ c`). -/
  | threeRouteFan
  /-- Entry prefix (local rigidity): **The chain `3, 3, 3`**: at every vertex `h`, paths `a p₁ p₂ b`, `b r₁ r₂ c`, `c q₁ q₂ d` of length `3` of `G − h` between neighbours of `h` (`a ≠ c`, `b ≠ d`) have `r₁ = p₂` and `r₂ = q₁`. -/
  | threeRouteChain
  /-- Entry prefix (local rigidity): **Window positions of `P₀`**: every window of `P₀` has a placement; an interior placed vertex carries `d − 2` external neighbours (exactly one when cubic), an end vertex `d − 1`. -/
  | windowPositionStubs
  /-- Entry prefix (local rigidity): **Cross-edge gap**: two vertex-disjoint placed paths of G joined at `(i, j)`, `(i', j')` have `|i − i'| + 2 + |j − j'|` not accepted; at the windows of `P₀`: legal attachment labels, `C₁` safety, the cross-window gap rule, no ladder. -/
  | windowAttachmentGap
  -- port-joint keys (7200–7399; 7200–7216 joint/windows/charge, 7217–7223 hub links, 7224–7232 free side, extended charge, separated pairs; 7233–7237 pair-code arms)
  /-- Entry prefix (joint hubs): **Cubic neighbours**: every cubic vertex of G has a cubic neighbour and at most two hub neighbours; `|L| ≤ Σ_{v∈L} |N(v) ∩ L| = 2e(L)`. -/
  | cubicNeighbourSupply
  /-- Entry prefix (joint hubs): **`5|H| + σ ≤ 2n`** (`H = {d ≠ 3}`). -/
  | hubCountBound
  /-- Entry prefix (joint hubs): **Parity of `L–L` edges on walks**: `#LL + [u∈H] + [v∈H] + |p|` is even on every walk `p : u → v` of G; an odd walk between cubic vertices uses an odd number of `L–L` edges. -/
  | lowEdgeParity
  /-- Entry prefix (joint hubs): **Hub domination and `2|B| + σ ≤ n`** (`B = {d ≥ 5}`): a hub dominates at most two hub-free components of `G[L]` (one if `d ≥ 5`), and each such component is dominated. -/
  | bigHubBound
  /-- Entry prefix (joint hubs): **V-shape caps**: two big hubs share at most `12` V-shape middles (no `C₈`), `|X₂| ≤ 12(|B|² − |B|)`, and `4σ + 93|B| ≤ 2n + 75|B|² + 4|H|`. -/
  | bigHubVShapes
  /-- Entry prefix (joint hubs): **The high-surplus bound**: `24σ + 465|B| ≤ 18n + 375|B|²`, and `8n ≤ 32s + 125s²` at `s = n − σ`. -/
  | highSurplusBound
  /-- Entry prefix (joint hubs): **Length-3 pairs at a hub** whose second neighbourhood is cubic: at most `4d` ordered non-adjacent pairs of `N(h)` are joined by a length-3 path avoiding `h`, and `d(d − 2) ≤ #(pairs with no such path) + 4d`. -/
  | hubLengthThreePairs
  /-- Entry prefix (joint hubs): **Density in excess form**: proper `S` (`|S| ≥ 2`) has `int S + 6 ≤ 4|S|`, i.e. `σ_S ≤ |S| + bd S − 6`; `bd S ≥ 2` for nonempty proper `S`; `S ⊇ N[h]` with its other vertices cubic has slack `≥ |S| − d_h − 1`. -/
  | densityExcess
  /-- Entry prefix (joint hubs): **The remainder slack of `P₀`**: `slack(R) = s + 2ν + 2σ_W − 2e× − 6` (`s = n − σ`), and windows of `P₀` hanging on a set `K` consume `Σ (2 + 2σ_P) ≤ slack(K)`. -/
  | remainderSlack
  /-- Entry prefix (joint hubs): **The hub–window budget at `P₀`**: `24ν + 2ε + I + 6|H| + σ ≤ 3n + 4h_W`, `2|H| + 3h_R + 2ε + I_W ≤ 2ν + r + s`, `Σ_P #LL(P) + 4h_W = 24ν + 2ε`, and `lowDarts − Σ_P #LL(P) = 2ν + 2r + s − 2|H| − 4h_R − 2ε`. -/
  | hubWindowBudget
  /-- Entry prefix (joint hubs): **The windows of `P₀` against the big hubs** (`s = n − σ`, `k = |B|`): `12ν + 31k ≤ 2s + 2|H| + 25k²`, `23ν + 31k ≤ n + 3s + 25k²`, `22ν + 93k + 6h_R + 4ε + 2I_W ≤ 6s + 75k²`. -/
  | windowHubBounds
  /-- Entry prefix (joint hubs): **Paths inside the remainder `R` of `P₀`**: no induced `P13`; hub-free connected bags have `≤ 6142` vertices; a path through `k` hubs has `≤ 6143k + 6142` vertices (`≤ 6143h_R + 6142`), and so does a cycle; long paths close long cycles (`m + 11 ≤ 11L`); span `≤ s` gives `m ≤ 11s`; `R` is `12`-degenerate. -/
  | remainderPathBounds
  /-- Entry prefix (joint hubs): **Window-free geometry of `P₀`**: short induced walks in window-free sets; the hub-pair dichotomy; chords of long window-free paths and their residues (open at a hub, closed by an outside path); one chord per `13` vertices; the outside-return dichotomy; window-free connected sets have `≤ 1 + 2047(3 + σ_K)` vertices; the carrier position. -/
  | windowFreeGeometry
  /-- Entry prefix (joint hubs): **Attachments to induced `P13`s**: a vertex off an induced `P13` of G has at most `7` neighbours on it, and every vertex of an induced `P13` has a neighbour off it. -/
  | inducedPathAttachment
  /-- Strict arm of `[19]`: **The orders the high-surplus closure excludes**: `8n ≤ 32(n − C⌈√n⌉ − 1) + 125(n − C⌈√n⌉ − 1)²`, and `n > C² + C + 1 + t` for every `t` with `125t² + 24t < 8(C² + C + 1)` (`C = C_sp`). -/
  | highSurplusOrder
  /-- Strict arm of `[19]`: **The window structure of G's canonical charge**: window-charged pairs have a coordinate or chord-set canonical blocker and are fully separated; spread coordinate blockers are window-charged; pairs supported in `R` never are; early blockers are charged to vertex tokens; same-hub pairs are early-blocked; no profile obstruction. -/
  | windowChargeKinds
  /-- Strict arm of `[19]`: **Every target-response obstruction of G is a residual target defect** (the replacement and smaller-representative arms are excluded by the replacement exclusion and minimality). -/
  | responseObstructionTargetDefect
  /-- Entry prefix (hub links): **The link structure of the hubs of `R`** at `P₀`: no hub chain of `≥ 13` vertices in `R`; no rainbow five-path of bag links and no strong `P5` among the hubs of `R`; the link graph on `S_R` is `18429`-degenerate (`Σ ≤ 36858 h_R`), the strong link graph `3`-degenerate (`Σ ≤ 6 h_R`); a non-strong pair carries `≤ 3·6142` linked vertices. -/
  | hubLinkStructure
  /-- Entry prefix (hub links): **The hub classes of the cubic vertices** (`A_j = {x ∈ L : |N(x) ∩ H| = j}`): `|A₀| + |A₁| + |A₂| = |L|`, `|A₁| + 2|A₂| = 3|H| + σ`, `|A₂| ≤ C(|H|, 2)`, `|A₂| + n = |A₀| + 4|H| + σ`, `|U| ≤ 3|A₀|`; per hub `d_h ≤ (|H| − 1) + |N(h) ∩ U| + |N(h) ∩ (A₁ ∖ U)|`; `Σ_H |N(h) ∩ U| = |U|`; the centre overload `≤ 2d_c`. -/
  | hubClassCounts
  /-- Entry prefix (hub links): **The slot relation** (no `C₈`): `|A₁| ≤ 3|A₀| + |A₂| + 2(|H|² − |H|) + 2C(|H|, 2)`, `4σ + 21|H| ≤ 3n + 6|H|²`, `4σ + 18|H| ≤ 3n + 6|A₂| + 3|H|²`; at most two matched-link and two link-link vertices per pair of hubs. -/
  | slotRelation
  /-- Entry prefix (hub links): **Closed bag-link classes of the hubs of `R`**: edges leaving the closure of a closed class end in `W`; disjoint classes have disjoint closures; with a window, a nonempty closed class reaches `W`; pairwise disjoint nonempty closed classes number `≤ e(R, W)`. -/
  | closedClasses
  /-- Entry prefix (hub links): **Two-hop links between the hubs of `R`**: the common-neighbour graph on `S_R` is `25`-degenerate (`Σ ≤ 50 h_R`); at every centre the two-hop graph has `≤ 6142` partners per bag, is `12286`-degenerate, `Σ_S ≤ 24572|S|`. -/
  | hubTwoHopLinks
  /-- Entry prefix (hub links): **The slot relation linear in `h_R`**: `|B_W| ≤ 13ν + 4e(R, W)`, the per-class counts off `B_W`, `4σ + 15|H| ≤ 3n + K·h_R + 8|B_W|` and `4σ + 15|H| ≤ 3n + K·h_R + 584ν + 32σ_W` (`K = 1811497284`). -/
  | slotLinear
  /-- Strict arm of `[19]`: **The scale pressure**: `C_sp⌈√n⌉ + 15|H| < 3s + K·h_R + 584ν + 32σ_W`, and `11C_sp⌈√n⌉ + 165|H| + 27156|B| < 1785s + 11K·h_R + 21900|B|² + 352σ_W` (`s = n − σ`, `K = 1811497284`). -/
  | scalePressure
  /-- Strict arm of `[19]`: **The free side of G's canonical capacity charge**: every free pair is two selected ports with disjoint declared supports, disjoint `T`, disjoint returns, distinct centres, no target-response and no chord-set obstruction, and one port triangular or one centre in the other's `T` (`Π_free ⊆ Π_tri ∪ Π_cs`). -/
  | freeSideStructure
  /-- Strict arm of `[19]`: **The free-side count**: `|𝒜₀| = σ`, `s(v) = d(v) − δ`, `|Π_free| ≤ τσ + Λ`, G2 and its capped arm with the count, and for `Δ ≥ max d`: `|Π_free| ≤ σ(τ + 3(Δ − 3))` and (capped, `K ≥ 0`) `n·K ≤ 2σ(τ + 3(Δ − 3))`. -/
  | freeSideCount
  /-- Strict arm of `[19]`: **The free side against the hubs**: `|Π_free| ≤ σ(τ + |H| − 1)` (a hub lies in `T(q)` for at most `|H| − 1` ports), and (capped, `K ≥ 0`) `n·K ≤ 2σ(τ + |H| − 1)`. -/
  | freeSideHubs
  /-- Strict arm of `[19]`: **The extended charge leaves no pair free**: `Π_free^ext = ∅` at G's canonical capacity presentation (clauses (a)–(f) unchanged; centre–shoulder and triangular pairs charged to a port token). -/
  | extFreeEmpty
  /-- Strict arm of `[19]`: **The extended loads**: `C(σ, 2) = Σ_{t∈𝔗} load_ext(t)` and `|𝔗| ≤ 8n + σ`. -/
  | extLoadSum
  /-- Strict arm of `[19]`: **The extended overload**: `c²K + 2M₀(8n + σ − |𝔗|) + 2B ≤ 2 Σ_t (load_ext(t) − M₀)`. -/
  | extOverload
  /-- Strict arm of `[19]`: **An overloaded extended token**: `K > 0` gives a token with `load_ext > M₀` (unconditional at the registered presentation). -/
  | extOverloadedToken
  /-- Strict arm of `[19]`: **The new port loads**: `newLoad(p) ≤ (|H| − 1) + [p triangular]·σ` for every selected port. -/
  | newLoadBound
  /-- Strict arm of `[19]`: **Separated pairs and the congestion trade-off**: a pair with disjoint declared supports and returns has only target-response or chord-set blockers; `C(σ, 2) ≤ Σ_v C(d_D(v), 2) + Σ_v C(d_R(v), 2) + |Sep|`. -/
  | separatedPairs
  /-- Entry prefix (pair arms): **Every selected port endpoint has degree `δ`** (the centre is high and the high vertices are independent). -/
  | portEndDegree
  /-- Strict arm of `[19]`: **Arm A of the pair code → the kind structure of the canonical pattern**: covers `≥ |𝓜| + 1` ports; every pair charged to the overload token with canonical blocker of the role's kind; exactly one of (a) one shared declared vertex, (b) one shared return vertex, (e) target responses with `t ∉ I ∪ P`, (f) fully separated singleton chord blockers (a star at `p₀` or a common shoulder `v`). -/
  | pairArmAPattern
  /-- Strict arm of `[19]`: **Arm A → the canonical overload role is one of ten** (`liveRoles`; no incidence token, no clause (c)/(d) role; `M₀`, `C_sp` unchanged). -/
  | pairArmARoleAlphabet
  /-- Strict arm of `[19]`: **Arm B of the pair code, exactly** (G-only restatement): the overlap system exists and G is in (B1) or (B3) ((B2), exit (b) at the obstruction coordinates, is empty at G); (B1) the `[182]` residual in three exact configurations; (B3) the obstruction handoff's separator (`deg > 3`), envelope and escape; on the realizability failure forward routes in `U` meet backward routes and the demand ends split; at the serial system the ends lie in `U`, centres high, port ends cubic, no route length accepted, and the switch at the left port. -/
  | pairArmB
  -- g-repair R1 keys (7800–7849)
  /-- Node `[125]`, clause (b) of `def:named-surplus-exits` stated about G (Lean improvement: exit (b) is empty at G): **every two readings of G agree in G's own surroundings `G − Z`** (both glued graphs are target-free subgraphs of G), so G's declared sparse family has no target-defective identification.  Published on `[125]`'s exit arm, where it closes the arm against `K .sparseTargetDefectResidual`. -/
  | sparseTargetDefectEmpty
  -- g-repair R5 keys (8000–8049)
  /-- Node `[144a]` (G repair R5, Lean improvement): **the transplants of G's pattern supports `X_q`, `X_p` into `Z = select?(X_p ∪ X_q)`**: each transplant (the `∂Z`-piece with interior `int(Z) ∩ X_·` and `G`'s edges) has (iii) interior at most `int(Z)`, (iv) linkage inclusion in `G[Z]`, (i) the profile of `G[Z]` iff no boundary vertex has a neighbour in `int(Z) ∖ X_·`, (ii) the baseline in `glue X′ (G − Z)` iff every vertex outside `int(Z) ∖ X_·` keeps `δ` neighbours outside it; and (ii) ∧ (iv) give `int(X′) = int(Z)` (minimality). -/
  | sameTokenTransplantSize
  /-- Node `[144a]` (G repair R5, Lean improvement): **the exact failure of the two transplants**: for each of `X_q`, `X_p`, either `int(Z) ⊆ X_·` and there is no exceptional vertex, or G's canonical exceptional vertex (the first vertex kept with fewer than `δ` neighbours outside `int(Z) ∖ X_·`) exists, lies in `Z`, and has a neighbour in `int(Z) ∖ X_·`. -/
  | sameTokenTransplantDeficit
  -- g-audit S144a keys (8100–8149)
  /-- Node `[144a]` (G audit S144a, Lean improvement): **the entry test of `[144a]`, decided at G**: at G's canonical routing, `X_p`, `X_q`, `Z = select?(X_p ∪ X_q)`: the coordinates differ, both readings of G at `Z` are target-free subgraphs of G and agree in `G − Z`; the arm "equal boundary profiles, separated by `G − Z`" is empty. -/
  | sameTokenUnresolvedDecided
  /-- Node `[144a]` (G audit S144a, Lean improvement): **each reading of G at `Z` (edge restriction to `X_p`, `X_q`), exactly**: it drops no edge of `G[Z]` with an interior end (it is G), or it drops one, is lexicographically smaller than G, and fails the baseline (minimality). -/
  | sameTokenReadingsExact
  /-- Node `[144a]` (G audit S144a, Lean improvement): **the rerouted swap `P → Q` at G, in both directions**: G's piece at `Z` with the interior structure of `P` replaced by a copy of that of `Q`, attached through the order-fixed contact bijection: (iii) `|int S| + |int Z ∩ P| = |int Z| + |int Z ∩ Q|`; (i) the profile of `G[Z]` iff every boundary vertex has as many interior neighbours in `Q` as in `P`; (ii) the baseline iff no vertex of G is deficient in any of four roles; (iv) linkage inclusion, or a linkage using a vertex and its copy; minimality gives `|int Z ∩ P| ≤ |int Z ∩ Q|`. -/
  | sameTokenSwap
  /-- Node `[144a]` (G audit S144a, Lean improvement): **the exact failure of the two rerouted swaps**: valid (no deficient vertex, linkage-included, `|int Z ∩ P| ≤ |int Z ∩ Q|`), or G's canonical exceptional vertex exists and is deficient in the rest / copy / boundary role, or a linkage of the swap uses a vertex and its copy; both swaps valid give `|int Z ∩ X_p| = |int Z ∩ X_q|`. -/
  | sameTokenSwapExact
  /-- Node `[144a]` (G audit S144a, Lean improvement): **boundary-free configuration**: if neither support meets `∂Z` and the transplants of `X_q` and `X_p` keep the baseline, then `X_p = X_q = Z`, `∂Z = ∅`, `Z = V(G)`, and every vertex outside a pair seed is a cut vertex of G (Steiner minimality of `select?`, G connected). -/
  | sameTokenU2FreeWhole
  -- g-audit 172a keys (8600–8649)
  /-- Node `[172a]`, on the failure arm of `[170]` (`lem:scale-additivity`), G's own record: **G's own skeleton, the member of `𝓑(𝒫)` given by `K .blockedClassMember`, has a surviving barrier state at every coordinate and lies in both of its own conditional fibres**, so `1 ≤ |S| ≤ |A|` at G's own outside record and prefix at every coordinate. -/
  | blockedOwnRecord
  /-- Node `[172a]`, the aggregate failure of `[170]` quantified: **at the first failing coordinate `F·A_k < W·A_{k+1}` with `A_{k+1} ≤ A_k`, `1 ≤ |𝓑(𝒫)| ≤ A_{k+1}` and `F_{a,b} < W_{a,b}`**, all earlier aggregate tests holding. -/
  | blockedFailureSlack
  /-- Node `[172a]`, the exposure counting of `lem:blocked-graphs-compress` run on a prefix: **at every coordinate whose predecessors all satisfy the aggregate test, `|𝓑(𝒫)|·∏W ≤ |𝒢|·∏F` over the predecessors**. -/
  | blockedPrefixCompression
  /-- Node `[172a]`, the failing set carries the overflow: **with the failing coordinates removed the exposure counting and the certified package rate give `|𝓑(𝒫)|·2^{bits·p}·∏_Φ F ≤ |𝒢_{n,m}|·∏_Φ W`** over the set `Φ` of coordinates whose aggregate test fails. -/
  | blockedFailingSetCarries
  /-- Node `[172a]`, G's overlap support (`def:barrier-overlap-system`): **for G's own skeleton, every completion support has at most `2^j+1` vertices; a present one is a closed walk of length `2^j` through a vertex of the root window which is not a cycle; and the overlap support of every coordinate is connected in G**. -/
  | blockedOverlapSupport
  -- g-audit PairTypeBOutcome keys (8350–8399)
  /-- Nodes `[179]`/`[180]` → `[187]` (G audit): **the Type B support of G's pair-obstruction handoff, exactly**: on G's canonical pair returns the canonical obstruction support is `(Y, H) = ({d_p.2, d_q.2}, {h})` with `h` the canonical first separator of the obstruction's routes; `H` is nonempty and consists of high centres, and the whole support lies in the obstruction's overlap support `U`.  Published with `K .typeBFanEntry` by the `[179]`/`[180]` early rows. -/
  | pairHandoffSupport
  /-- Nodes `[179]`/`[180]` → `[187]` (G audit): **the ambient surplus of that support**: the core ends are cubic port ends (`σ(Y) = 0`), `Y ∩ H = ∅`, and `ω(H) = d_G(h) - δ ≥ 1` for the one centre `h`. -/
  | pairHandoffCharge
  /-- Nodes `[179]` → `[187]` (G audit): **the net charge of that support** (`def:net-charge`): the core has one or two vertices, `(δ-1)|Y| ≤ def⁺(Y) ≤ δ|Y|`, and at the canonical envelope either the net charge is negative or `ω(H) < def⁺(Y)`, i.e. the centre has degree `< 3δ`. -/
  | pairHandoffNetCharge
  /-- Nodes `[179]` → `[187]` (G audit): **flow-cut support of the capacity charge at the handoff centre `h`**: each pair of the obstruction family is charged to the port token of one of its own ports (a high centre); `h` has `d(h) − δ` port tokens; the pairs of the family charged to them are bounded by their new loads. -/
  | pairHandoffHubCharge
  /-- Nodes `[179]` → `[187]` (G audit): **boundaried type of `G[U]`**: the boundary vertices of the overlap support `U`, the degree identity `e(U, G−U) + Σ_U d_U = δ|U| + σ(U)`, `σ(U) ≥ 1`, and the response of every reading of `U` glued into `G − U` (no accepted cycle). -/
  | pairHandoffBoundaryType
  /-- Nodes `[179]` → `[187]` (G audit): **the exposure coordinate the handoff decides**: every coordinate of the obstruction family is critical (the order exposing it last doubles the realized signatures at every earlier level and fails exactly at it), and the canonical members whose response supports contain the first separator `h` and its two next vertices exist. -/
  | pairHandoffCriticalCoordinate
  /-- Nodes `[179]` → `[187]` (G audit): **demand descent of the obstruction**: `2 ≤ |𝒰| ≤ |Π|`, `𝒰` is not realizing, and peeling any one member leaves a realizing family. -/
  | pairObstructionDescent
  /-- Nodes `[179]` → `[187]` (G audit): **the ledger's hub facts at the handoff centre `h`**: the vertex split, the same-vertex switch, the endpoint switch at cubic neighbours, the length-3 fan and the chain `3, 3, 3`, instantiated at the canonical first separator. -/
  | pairHandoffHubForces
  /-- Nodes `[179]` → `[187]` (G audit): **the demand ends of the obstruction lie in `U`**: every port of every pair of the family has its endpoint in the pair's response support (hence in `U`), the endpoint is a cubic port end and the centre is a high vertex. -/
  | pairHandoffDemandEnds
  /-- Nodes `[179]` → `[187]` (G audit): **the hub balance at the handoff**: the net charge (`pairHandoffNetCharge`), the tokens of `h` (`pairHandoffHubCharge`) and the hub facts (`pairHandoffHubForces`) together: at the canonical envelope either the charge is negative, or `d(h) < 3δ`, `h` has fewer than `2δ` tokens and at most `(2δ−1)((|H|−1)+σ)` pairs of the family are charged at `h`. -/
  | pairHandoffHubBalance
  /-- Nodes `[179]` → `[187]` (G audit): **the critical coordinate of the handoff read at G's own signature**: G's own responses are all negative; for the canonical member `π_h` whose support contains `h`, in the order exposing it last (earlier levels double, the last does not), G's own level signature has one or two realized extensions (a fibre of size one is a repetition of G's response at `π_h`). -/
  | pairHandoffFibreAtG
  /-- Terminal `[54]` (`prop:entropy-high-theta`): **the stub-deficit identity at `R₀`**: `e(R₀,W) + exc(R₀) = σ(R₀) + def⁺(R₀)`, `2e(G[R₀]) + e(R₀,W) = δ|R₀| + σ(R₀)`, and the canonical assignment of the `def⁺(R₀)` deficit units to distinct boundary stubs by G's vertex order. -/
  | stubDeficitIdentity
  /-- Terminal `[54]`: **the cycle spectrum of `R₀`**: `G[R₀]` and every induced subgraph of it carry no cycle of an accepted length. -/
  | remainderCycleSpectrum
  /-- Node `[144a]` (G audit S144a, Lean improvement): **the pair seeds are covered by their canonical port paths**: each pair seed `T(p) ∪ Γ(p) ∪ T(p') ∪ Γ(p')` is at most `2δ` vertices and two canonical port paths (a triangular port's shortest return `R_p` in `G − cx`, an induced path; an open port's suppression path `Q_p`), each with its chord facts (every chord has an unaccepted span, every interior cubic vertex has exactly one off-path edge); if every degree-`3` vertex lies in both pair seeds, the degree-`3` vertices are covered by at most four such paths and `4δ` vertices, and `3n ≤ 5(|T| + |P₁| + |P₂|)` (from `5|H| + σ ≤ 2n`). -/
  | sameTokenSeedCover
  /-- Node `[144a]` (G audit S144a, Lean improvement): **the interactions of the canonical port paths**: the pair seeds are `T ∪ supp w₁ ∪ supp w₂` and `T' ∪ supp z₁ ∪ supp z₂` with canonical port walks (simple; every chord, hub and closing cycle length unaccepted; one stub per interior cubic vertex); two vertex-disjoint segments of two of the walks joined by two edges (a rung pair, parallel or crossed) close a cycle of length `|p₂| + |q₂| + 2`, which is not accepted (all six pairs of walks); at every cubic vertex interior to a `P`-walk and a `Q`-walk the two path edges of one and the two of the other share an edge; if every degree-`3` vertex lies in both pair seeds, every neighbour of a hub lies in both. -/
  | sameTokenPathInteractions
  deriving DecidableEq

/-- **The presentation laws of G's registered presentation, published once at
the entry** under the one key `K .cubicBaseline`.  The four components are
disjoint: no law appears in two of them, and no other key publishes any of
them.

1. `CubicBaselineStatement`: `δ = 3`, `s = 4`, `2` is not an accepted length,
   and the window rate is the barrier table's rate;
2. `TypeBPresentationStatement`: the quadrilateral is accepted, the accepted
   lengths are exactly the dyadic ones (the one copy of the target law), and
   the Type B fan, deficit and bridge-mass slacks;
3. `SurplusPresentationStatement`: the sparse-surplus presentation identities;
4. `SpinePresentationLawsStatement`: the HSS closure law at `G` and at `G`'s
   induced subgraphs, the scale family, the net-cap slack and the barrier
   table's label semantics, stated at `G`. -/
noncomputable abbrev PresentationLawsStatement (data : Parameters)
    (label : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (object : Graph.FiniteObject.{u}) : Prop :=
  CubicBaselineStatement data ∧ TypeBPresentationStatement data ∧
    SurplusPresentationStatement data ∧
    SpinePresentationLawsStatement data label object

/-- The value schema of each spine fact, stated of the *object* alone.

Every spine fact is a statement about the selected graph, never about a side
payload carried beside it.  Making that explicit is what lets a fact transport
along a refinement by a rewrite: refinement is object equality.  The finite
label census is stated at every induced window of that selected graph; the
definitions of `C_s` and `Ω₂` live in `WindowCurvatureAlgebra` and are not
restated as additional ledger theorems. -/
def Holds (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Key → Graph.FiniteObject.{u} → Prop
  | .selection, object =>
      SelectionStatement BranchState Presentation presentation data.toParameters object
  | .cubicBaseline, object =>
      PresentationLawsStatement data.toParameters data.windowBarrierLabel object
  | .minDegreeBaseline, object =>
      MinDegreeBaselineStatement data.toParameters object
  | .returnAvoidance, object =>
      ReturnAvoidanceStatement data.toParameters object
  | .mersenneReturn, object =>
      MersenneReturnStatement data.toParameters object
  | .noProperBaseline, object =>
      NoProperBaselineStatement data.toParameters object
  | .tightEndpoint, object =>
      TightEndpointStatement data.toParameters object
  | .slackIndependent, object =>
      SlackIndependentStatement data.toParameters object
  | .cycleRankConstraint, object =>
      CycleRankConstraintStatement object
  | .replacementExclusion, object =>
      ReplacementExclusionStatement data.toParameters object
  | .uncompressible, object =>
      UncompressibleStatement data.toParameters object
  | .windowFree, object =>
      Graph.InducedPathFree object data.windowOrder
  | .windowPresent, object =>
      Graph.HasInducedPath object data.windowOrder
  | .maximalPacking, object =>
      MaximalPackingStatement data.toParameters object
  | .localAlgebra, object =>
      LocalAlgebraStatement data.toParameters object
  | .surplusAbove, object =>
      SurplusAboveStatement data.toParameters object
  | .surplusAtOrBelow, object =>
      SurplusAtOrBelowStatement data.toParameters object
  | .barrierCap, object =>
      -- `lem:p13-window-package`.  The registered rate is a per-window cost
      -- *per dyadic scale* -- that is what `windowRate`'s provenance and
      -- `dyadicScaleCount`'s own docstring both say -- so the package the
      -- packing demands is `rate · (number of scales) · p` bits, the
      -- manuscript's `c₁₃ p₁₃ log₂ n`.  Dropping the scale factor would state a
      -- demand that grows a whole `log₂ n` slower than the manuscript's, and
      -- node `[24]` would then cap nothing.
      BarrierCapStatement data.toParameters object
  | .barrierOverflow, object =>
      BarrierOverflowStatement data.toParameters object
  | .densityCap, object =>
      DensityCapStatement data.toParameters object
  | .remainderNormalized, object =>
      RemainderNormalizedStatement data.toParameters object
  | .boundaryDemand, object =>
      BoundaryDemandStatement data.toParameters object
  | .stubSupply, object =>
      StubSupplyStatement data.toParameters object
  | .wedgeSupply, object =>
      WedgeSupplyStatement data.toParameters object
  | .exactResponseProfile, object =>
      ExactResponseProfileStatement data.toParameters object
  | .curvatureTargetRank, object =>
      CurvatureTargetRankStatement data.toParameters object
  | .targetRankCircuit, object =>
      TargetRankCircuitStatement data.toParameters object
  | .curvatureRankDrop, object =>
      CurvatureRankDropStatement data.toParameters object
  | .curvatureFullRank, object =>
      CurvatureFullRankStatement data.toParameters object
  | .branchDependence, object =>
      BranchDependenceStatement data.toParameters object
  | .contextUniversal, object =>
      ContextUniversalStatement data.toParameters object
  | .contextDefect, object =>
      ContextDefectStatement data.toParameters object
  | .atomCompression, object =>
      AtomCompressionStatement data.toParameters object
  | .delocalizedSupport, object =>
      DelocalizedSupportStatement data.toParameters object
  | .properDelocalization, object =>
      ProperDelocalizationStatement data.toParameters object
  | .globalDelocalization, object =>
      GlobalDelocalizationStatement data.toParameters object
  | .repairIdentity, object =>
      RepairIdentityStatement data.toParameters object
  | .globalBarrier, object =>
      GlobalBarrierStatement data.toParameters object
  | .coldCorridorState, object =>
      -- The ledger retains the actual corridor presentations, state readings,
      -- first repeat, exact table record, and the paper's terminal/repeated
      -- exchange representative.  Consumers recover those witnesses from this
      -- key; they do not supply a fresh `Presentation` or manufacture a row.
      ColdCorridorStateStatement data.toParameters object
  | .coldSameInterfaceTable, object =>
      ColdSameInterfaceTableStatement data.toParameters object
  | .coldGermRealized, object =>
      ColdGermRealizedStatement data.toParameters object
  | .coldGermDistinguished, object =>
      ColdGermDistinguishedStatement data.toParameters object
  | .coldGermSilent, object =>
      ColdGermSilentStatement data.toParameters object
  | .coldFailureCycle, object =>
      -- `lem:cold-corridor-first-failure` (i).  The displayed completion of
      -- clause (F1) -- the window position the entry stub lands on, the stub,
      -- the corridor prefix, the return adjacency, and the window segment
      -- between the two offsets -- is literally a closed walk of the object, so
      -- an accepted one would be an accepted cycle of the selected object.
      -- Node `[1]` says there is none, so (F1) never occurs.
      ColdFailureCycleStatement data.toParameters object
  | .coldFailureDefectRoute, object =>
      ColdFailureDefectRoutesStatement data.toParameters object
  | .coldFailureCompression, object =>
      -- `lem:cold-corridor-first-failure` (iii).  An (F3) pair is a
      -- target-complete compression of the later prefix's own proper support --
      -- same boundary-degree profile, baseline preserved, strictly smaller,
      -- equal response against every outside context -- and node `[14]`'s
      -- `cor:uncompressible` forbids it.  So (F3) never occurs.
      ColdFailureCompressionStatement data.toParameters object
  | .coldFailureRouting, object =>
      ColdFailureRoutingStatement data.toParameters object
  | .coldFirstFailureOccurrence, object =>
      ColdFirstFailureOccurrenceStatement data.toParameters object
  | .coldExchangeBound, object =>
      ColdExchangeBoundStatement data.toParameters object
  | .coldRoute8Below, object =>
      ColdRoute8BelowStatement data.toParameters object
  | .coldRoute8AtOrAbove, object =>
      ColdRoute8AtOrAboveStatement data.toParameters object
  | .coldHotEntropyOverflow, object =>
      ColdHotEntropyOverflowStatement data.toParameters object
  | .coldHotEntropyCap, object =>
      ColdHotEntropyCapStatement data.toParameters object
  | .coldMass, object =>
      ColdMassStatement data.toParameters object
  | .coldAmbientCubic, object =>
      ColdAmbientCubicStatement data.toParameters object
  | .coldStubExcess, object =>
      ColdStubExcessStatement data.toParameters object
  | .coldMassLinear, object =>
      ColdMassLinearStatement data.toParameters object
  | .coldMassBounded, object =>
      ColdMassBoundedStatement data.toParameters object
  | .bridgeless, object =>
      BridgelessStatement object
  | .windowPackageRealized, object =>
      WindowPackageRealizedStatement data.toParameters object
  | .windowPackageUnrealized, object =>
      WindowPackageUnrealizedStatement data.toParameters object
  | .denseDeficiencyBelow, object =>
      DenseDeficiencyBelowStatement data.toParameters object
  | .denseDeficiencyAtOrAbove, object =>
      DenseDeficiencyAtOrAboveStatement data.toParameters object
  | .denseColdCorridorsTerminal, object =>
      DenseColdCorridorsTerminalStatement data.toParameters object
  | .coldNeutralEqualLengthTerminal, object =>
      NeutralEqualLengthTerminalConfigurationStatement data.toParameters object
  | .coldWindowStubStructure, object =>
      ColdWindowStubStructureStatement data.toParameters object
  | .coldCanonicalNeutralConfiguration, object =>
      CanonicalNeutralConfigurationStatement data.toParameters object
  | .coldGenuineSecondStrand, object =>
      GenuineSecondStrandStatement data.toParameters object
  | .coldTwoStrandSurvivor, object =>
      TwoStrandSurvivorStatement data.toParameters object
  | .coldSymmetricPairExcluded, object =>
      ColdSymmetricPairExcludedStatement data.toParameters object
  | .coldCanonicalSwapSmaller, object =>
      ColdCanonicalSwapSmallerStatement data.toParameters object
  | .coldCanonicalSwapSameSize, object =>
      ColdCanonicalSwapSameSizeStatement data.toParameters object
  | .coldCanonicalReplacementSwap, object =>
      CanonicalReplacementSwapStatement data.toParameters object
  | .coldCanonicalReplacementTrivial, object =>
      CanonicalReplacementTrivialStatement data.toParameters object
  | .blockedClassMember, object =>
      BlockedClassMemberStatement data.toParameters object
  | .blockedScaleAdditive, object =>
      BlockedScaleAdditivityStatement data.toParameters object
  | .blockedCompressionBound, object =>
      BlockedCompressionBoundStatement data.toParameters object
  | .blockedCompressionCap, object =>
      BlockedCompressionCapStatement data.toParameters object
  | .blockedBarrierOverlap, object =>
      BlockedBarrierFailureStatement data.toParameters object
  | .absorbedGermFanData, object =>
      AbsorbedGermFanDataStatement data.toParameters object
  | .absorbedGermSplit, object =>
      AbsorbedGermSplitStatement data.toParameters object
  | .coldFamilyPositive, object =>
      ColdFamilyPositiveStatement data.toParameters object
  | .coldFamilyEmpty, object =>
      ColdFamilyEmptyStatement data.toParameters object
  | .coldReturnCorridors, object =>
      -- `def:cold-corridor-first-failure`: the componentwise corridor theorem
      -- together with its exact specialization to every selected cold
      -- branch-excess half-edge whose foot lies in the outside graph.
      ColdReturnCorridorsStatement data.toParameters object
  | .coldGermCandidates, object =>
      ColdGermCandidatesStatement data.toParameters object
  | .coldGermFamilyPositive, object =>
      ColdGermFamilyPositiveStatement data.toParameters object
  | .coldSelectedBranchExcess, object =>
      ColdSelectedBranchExcessStatement data.toParameters object
  | .coldAmbientCubicStubExcess, object =>
      ColdAmbientCubicStubExcessStatement data.toParameters object
  | .barrierEnumeration, _object =>
      BarrierEnumerationStatement data.toParameters
  | .windowPackageSeparated, object =>
      WindowPackageSeparatedStatement data.toParameters object
  | .coldHandoffTransfer, object =>
      -- `lem:cold-germ-extraction`: a candidate prefix is subcubic, or its
      -- first high-degree head is transferred to the already named high-degree
      -- ledger before the disjoint extraction is run.
      ColdFirstHighHandoffStatement data.toParameters object
  | .coldPositiveGerm, object =>
      ColdPositiveGermStatement data.toParameters object
  | .coldGermRouted, object =>
      ColdGermRoutedStatement data.toParameters object
  | .coldGermSomeRealizing, object =>
      ColdGermSomeRealizingStatement data.toParameters object
  | .coldGermNoneRealizing, object =>
      ColdGermNoneRealizingStatement data.toParameters object
  | .coldGermSomeDistinguishing, object =>
      ColdGermSomeDistinguishingStatement data.toParameters object
  | .coldGermNoneDistinguishing, object =>
      ColdGermNoneDistinguishingStatement data.toParameters object
  | .coldBranchClosed, object =>
      ColdBranchClosedStatement data.toParameters object
  | .forcedCurvatureCost, object =>
      ForcedCurvatureCostStatement data.toParameters object
  | .remainderEntropyHigh, object =>
      RemainderEntropyHighStatement data.toParameters object
  | .remainderEntropyLow, object =>
      RemainderEntropyLowStatement data.toParameters object
  | .localTypeCoordinateRepetitive, object =>
      LocalTypeCoordinateRepetitiveStatement data.toParameters object
  | .localTypeCoordinateNonrepetitive, object =>
      LocalTypeCoordinateNonrepetitiveStatement data.toParameters object
  | .dominantRootedType, object =>
      DominantRootedTypeSchema data.toParameters object
  | .dominantRootedTypeWedgeFree, object =>
      DominantRootedTypeWedgeFreeStatement data.toParameters object
  | .dominantRootedWedgeType, object =>
      DominantRootedWedgeTypeStatement data.toParameters object
  | .independentObstructionTranslates, object =>
      IndependentObstructionTranslatesStatement data.toParameters object
  | .entropyPackageDemand, object =>
      EntropyPackageDemandStatement data.toParameters object
  | .entropyCapActive, object =>
      EntropyCapActiveStatement data.toParameters object
  | .entropyCapBound, object =>
      EntropyCapBoundStatement data.toParameters object
  | .largeBudgetResidual, object =>
      -- Residual C.  The high-entropy arm reaches it through the exact
      -- skeleton comparison; the low-entropy arm is routed here unchanged, as `prop:two-budget` prescribes.
      LargeBudgetResidual data.toParameters object
  | .netDeficiencyCap, object =>
      NetDeficiencyCapStatement data.toParameters object
  | .netChargeLocalization, object =>
      NetChargeLocalizationStatement data.toParameters object
  | .netChargeNonNegative, object =>
      NetChargeNonNegativeStatement data.toParameters object
  | .netChargeNegative, object =>
      NetChargeNegativeStatement data.toParameters object
  | .exactCollisionFails, object =>
      ExactCollisionFailsStatement data.toParameters object
  | .absorbedConfigurationResidual, object =>
      AbsorbedConfigurationResidualStatement data.toParameters object
  | .netChargeCap, object =>
      NetChargeCapStatement data.toParameters object
  | .negativeSupport, object =>
      NegativeSupportStatement data.toParameters object
  | .typeALowSurplus, object =>
      TypeALowSurplusStatement data.toParameters object
  | .typeABoundedSupport, object =>
      TypeABoundedSupportStatement data.toParameters object
  | .typeBHighSurplus, object =>
      TypeBHighSurplusStatement data.toParameters object
  | .typeBAssignedSupport, object =>
      TypeBAssignedSupportStatement data.toParameters object
  | .typeBFanEntry, object =>
      TypeBFanEntryStatement data.toParameters object
  | .typeBFanHeavyCentre, object =>
      -- Node `[68]`, yes arm on either literal Type B input: one actual assigned
      -- centre has degree strictly above `δ + 1` (greater than four in EG).
      TypeBFanHeavyCentreStatement data.toParameters object
  | .typeBFanDegreeFourCentres, object =>
      -- Node `[68]`, no arm: every canonical assigned centre, or the chosen
      -- centre for every indexed `[177]` datum, has degree exactly `δ + 1`.
      TypeBFanDegreeFourCentresStatement data.toParameters object
  | .sameCenterOpenPortCompatibility, object =>
      -- Node `[69]`, `lem:same-center-open-port-compatibility`, derived from
      -- the normal form already present on the incoming ledger.
      SameCenterOpenPortCompatibilityStatement data.toParameters object
  | .typeBFanLocalDichotomy, object =>
      -- Node `[69]`, `cor:heavy-center-local-dichotomy`, on the common
      -- assigned-centre carrier selected by `[68]`: either the canonical
      -- support or the indexed decorated handoff from `[177]`.
      TypeBFanLocalDichotomyStatement data.toParameters object
  | .typeBFanDegreeFourProfile, object =>
      -- Nodes `[78]`--`[79]` on either literal Type B carrier.  At every
      -- relevant degree-four centre this is `cor:degree-four-local-activation`
      -- together with the three displayed degree-four fan-profile identities.
      TypeBFanDegreeFourProfileStatement data.toParameters object
  | .triangularFanCore, object =>
      -- Node `[79]`, `def:triangular-fan-core`, on the active object.
      TriangularFanCoreStatement data.toParameters object
  | .triangularShoulderCompletion, object =>
      TriangularShoulderCompletionStatement data.toParameters object
  | .triangularPortReturn, object =>
      TriangularPortReturnStatement data.toParameters object
  | .triangularFirstLanding, object =>
      TriangularFirstLandingStatement data.toParameters object
  | .triangularCrossShoulder, object =>
      TriangularCrossShoulderStatement data.toParameters object
  | .openPortSuppression, object =>
      OpenPortSuppressionStatement data.toParameters object
  | .openPortSuppressionSafe, object =>
      OpenPortSuppressionSafeStatement data.toParameters object
  | .singleOpenPortSuppressionWitness, object =>
      SingleOpenPortSuppressionWitnessStatement data.toParameters object
  | .suppressedFamilyCriticalCycle, object =>
      SuppressedFamilyCriticalCycleStatement data.toParameters object
  | .compatiblePairFanClosure, object =>
      CompatiblePairFanClosureStatement data.toParameters object
  | .fanClosedPortTypeBRouting, object =>
      FanClosedPortTypeBRoutingStatement data.toParameters object
  | .compatiblePairTypeBRouting, object =>
      CompatiblePairTypeBRoutingStatement data.toParameters object
  | .triangularPortTypeBRouting, object =>
      TriangularPortTypeBRoutingStatement data.toParameters object
  | .typeAReceiverRouting, object =>
      TypeAReceiverRoutingStatement data.toParameters object
  | .typeASaturatedReceiver, object =>
      TypeASaturatedReceiverStatement data.toParameters object
  | .typeAUnsaturatedReceivers, object =>
      TypeAUnsaturatedReceiversStatement data.toParameters object
  | .typeAUnsaturatedDischarge, object =>
      TypeAUnsaturatedDischargeStatement data.toParameters object
  | .typeAExclusion, object =>
      TypeAExclusionStatement data.toParameters object
  | .typeBBridgeReduction, object =>
      TypeBBridgeReductionStatement data.toParameters object
  | .typeBSublinearLedger, object =>
      TypeBSublinearHypotheses data.toParameters object
  | .typeBSublinearResidual, object =>
      TypeBSublinearResidualStatement data.toParameters object
  | .route8QuotientFree, object =>
      Route8QuotientFreeStatement data.toParameters object
  | .route8QuotientResidual, object =>
      Route8QuotientResidualStatement data.toParameters object
  | .route8DemandLedger, object =>
      Route8DemandLedgerPinnedStatement data.toParameters object
  | .route8ExtractedEntryCensus, object =>
      Route8ExtractedEntryCensusFact data.toParameters object
  | .typeAPortReturn, object =>
      TypeAPortReturnStatement data.toParameters object
  | .typeAVisibleEntry, object =>
      TypeAVisibleEntryStatement data.toParameters object
  | .typeAVisibleFirstExcess, object =>
      TypeAVisibleFirstExcessStatement data.toParameters object
  | .typeAExitOneReturn, object =>
      TypeAExitOneReturnStatement data.toParameters object
  | .typeAExitOneFree, object =>
      TypeAExitOneFreeStatement data.toParameters object
  | .typeAExitTwoTheta, object =>
      TypeAExitTwoThetaStatement data.toParameters object
  | .typeAExitTwoFree, object =>
      TypeAExitTwoFreeStatement data.toParameters object
  | .typeAExitThreeCollision, object =>
      TypeAExitThreeCollisionStatement data.toParameters object
  | .typeAExitThreeFree, object =>
      TypeAExitThreeFreeStatement data.toParameters object
  | .typeASaturatedExitEntry, object =>
      TypeASaturatedExitEntryStatement data.toParameters object
  | .typeAExitSevenHandoff, object =>
      TypeAExitSevenHandoffStatement data.toParameters object
  | .typeBDecoratedAssignedSupport, object =>
      TypeBDecoratedAssignedSupportStatement data.toParameters object
  | .typeAExitSevenFree, object =>
      TypeAExitSevenFreeStatement data.toParameters object
  | .highCentreNormalForm, object =>
      HighCentreNormalFormStatement data.toParameters object
  | .fanCertificateCap, object =>
      -- Node `[70]`, `lem:fan-certificate`, at the Type B support of the
      -- `[69]`/`[79]` arm fact.  The bound is the label algebra's own
      -- packing number at the registered window order, never a numeral: at the
      -- manuscript's order it evaluates to `8`.  It is conditional on G's
      -- canonical certificate labelling, exactly as in the manuscript.
      TypeBFanCertificateCapStatement data.toParameters object
  | .fanCertificateMarked, object =>
      -- Node `[71]`/`[80]`, yes arm, at G's canonical labelling of every
      -- assigned centre of the Type B support.
      TypeBFanCertificateMarkedStatement data.toParameters object
  | .fanCertificateResidual, object =>
      -- Node `[71]`/`[80]`, no arm: G's canonical labelling is absent at an
      -- assigned centre of the same Type B support.
      TypeBFanCertificateResidualStatement data.toParameters object
  | .typeBHybridEntry, object =>
      -- Nodes `[72]`/`[81]`, B1.  At the assigned centres of the Type B fan
      -- support, because `k ≤ α(D)` is available only at a certificate-marked
      -- fan, on the assigned fan envelope and `W₀ = windowSupport P₀`.
      TypeBFanHybridEntryStatement data.toParameters object
  | .typeBDirectCycleFree, object =>
      -- Nodes `[72]`/`[81]`: the direct fan-window cycles are excluded inside
      -- the local fan-window ledger, at the marked Type B support.
      TypeBFanDirectCycleFreeStatement data.toParameters object
  | .typeBB2Choice, object =>
      -- Node `[72]`, yes: B1 and B2 at the Type B support `(Y_X, H_X)`, the
      -- candidate entries evaluated on the assigned fan envelopes of the
      -- support, at G's canonical `[71]` labelling.
      TypeBB2ChoiceStatement data.toParameters object
  | .typeBDisjointLedger, object =>
      TypeBDisjointLedgerStatement data.toParameters object
  | .typeBOverlapObstruction, object =>
      -- Node `[72]`, no.  `lem:typeB-bridge-to-overlap`: the disjoint-carrier
      -- clause fails at the marked Type B support, which then carries G's
      -- canonical *minimal* Type B overlap obstruction among its centres.
      TypeBB2ObstructionStatement data.toParameters object
  | .typeBGlobalLocalBridge, object =>
      TypeBGlobalLocalBridgeStatement data.toParameters object
  | .fanCertificateResidualMass, object =>
      -- Node `[75]`/`[84]`: the fan-certificate residual support's negative
      -- part is charged to its assigned surplus
      -- (`lem:typeB-bridge-deficit-bound`).
      TypeBFanCertificateResidualMassStatement data.toParameters object
  | .typeBOverlapObstructionMass, object =>
      TypeBOverlapObstructionMassStatement data.toParameters object
  | .typeBAbsorbedHalfEdge, object =>
      TypeBAbsorbedHalfEdgeStatement data.toParameters object
  | .typeBAbsorbedHalfEdgeAbsent, object =>
      TypeBAbsorbedHalfEdgeAbsentStatement data.toParameters object
  | .absorbedHandoffCore, object =>
      AbsorbedHandoffCoreStatement data.toParameters object
  | .absorbedHandoffCoreAbsent, object =>
      AbsorbedHandoffCoreAbsentStatement data.toParameters object
  | .absorbedF4Charge, object =>
      AbsorbedF4ChargeStatement data.toParameters object
  | .typeBDegreeFourLedger, object =>
      TypeBDegreeFourLedgerStatement data.toParameters object
  | .typeBDegreeFourOverlap, object =>
      TypeBDegreeFourOverlapStatement data.toParameters object
  | .typeBDegreeFourClosed, object =>
      TypeBDegreeFourClosedStatement data.toParameters object
  | .typeBAbsorbedCharge, object =>
      TypeBAbsorbedChargeStatement data.toParameters object
  | .typeBRoute8Entry, object =>
      TypeBRoute8EntryStatement data.toParameters object
  | .typeBBridgeMass, object =>
      TypeBBridgeMassStatement data.toParameters object
  | .typeBBridgeSublinear, object =>
      TypeBBridgeSublinearStatement data.toParameters object
  | .typeBExcluded, object =>
      TypeBExcludedStatement data.toParameters object
  | .typeBExclusionResidual, object =>
      TypeBExclusionResidualStatement data.toParameters object
  | .typeAExitFourPeeled, object =>
      TypeAExitFourPeeledStatement data.toParameters object
  | .typeAExitFourFiniteDescent, object =>
      -- `lem:typeA-exit4-finite-descent`: the finite descent principle at the
      -- exact selected receiver and current peeling set (the terminal
      -- predicates are instantiated by the rows that use it, node `[123]`).
      TypeAExitFourFiniteDescentFact data.toParameters object
  | .typeASaturatedHandoffExitFour, object =>
      TypeASaturatedHandoffExitFourStatement data.toParameters object
  | .typeASaturatedHandoffExitFourFree, object =>
      TypeASaturatedHandoffExitFourFreeStatement data.toParameters object
  | .typeAExitFourReceiverDischarged, object =>
      TypeAExitFourReceiverDischargedStatement data.toParameters object
  | .typeAExitFive, object =>
      TypeAExitFiveStatement data.toParameters object
  | .typeAExitFiveFree, object =>
      TypeAExitFiveFreeStatement data.toParameters object
  | .typeAExitSix, object =>
      TypeAExitSixStatement data.toParameters object
  | .typeAExitSixFree, object =>
      TypeAExitSixFreeStatement data.toParameters object
  | .typeAExitSixProper, object =>
      TypeAExitSixProperStatement data.toParameters object
  | .typeAExitSixGlobal, object =>
      TypeAExitSixGlobalStatement data.toParameters object
  | .route8ResidualProfile, object =>
      -- Node `[110]`: the selected route-8 residual satisfies the
      -- silent-core residual profile, without creating a secondary carrier.
      SilentCoreResidualProfile data.toParameters object
  | .route8BasinBurden, object =>
      -- Node `[112]`: the selected route-8 residual carries the basin-burden
      -- lower side of `lem:typeA-route8-burden`.
      Route8BasinBurden data.toParameters object
  | .route8LargeBudgetDeficit, object =>
      -- Node `[113]`: the exact cleared lower bound on `D_A(𝒳_A)` for the
      -- selected route-8 collection.
      Route8LargeBudgetDeficit data.toParameters object
  | .route8LargeBudgetDeficitFails, object =>
      Route8LargeBudgetDeficitFailsStatement data.toParameters object
  | .route8CarrierCore, object =>
      -- Node `[114]`: the canonical minimal carrier-core theorem package,
      -- available on the selected route-8 residual.
      Route8CarrierCore data.toParameters object
  | .route8TrueResidual, object =>
      -- Node `[114]`, `def:typeA-true-route8-residual`: clauses (R1)--(R4)
      -- for every actual indexed entry of the selected route-8 collection.
      Route8TrueResidual data.toParameters object
  | .route8CarrierCutParity, object =>
      -- Node `[114]`, `lem:typeA-carrier-cut-parity`: the exact conditional
      -- cut-parity statement on every surviving mixed event.
      Route8CarrierCutParity data.toParameters object
  | .route8SmallCoreEntry, object =>
      -- Node `[115]`, yes arm: the selected route-8 collection contains a
      -- literal indexed entry with `alpha ≤ 1`.
      Route8SmallCoreEntry data.toParameters object
  | .route8NoSmallCoreEntry, object =>
      -- Node `[115]`, no arm: all literal indexed entries have `alpha ≥ 2`.
      Route8NoSmallCoreEntry data.toParameters object
  | .route8SmallCoreCollapse, object =>
      -- Node `[116]`: the selected small entry realizes an exact exit
      -- `(4)`--`(7)` trace-basin alternative.
      Route8SmallCoreCollapse data.toParameters object
  | .route8CarrierDeletionWitnesses, object =>
      -- Node `[118]`: carrier-deletion target-defect witnesses for every
      -- selected two-carrier essential-core entry.
      Route8CarrierDeletionWitnesses data.toParameters object
  | .route8PrivateCarrierBudget, object =>
      -- Nodes `[119]`--`[120]`: no two-carrier entry gives the
      -- private-carrier budget on the selected route-8 residual.
      Route8PrivateCarrierBudgetStatement data.toParameters object
  | .route8Census, object =>
      Route8CensusStatement data.toParameters object
  | .route8Rate, object =>
      Route8RateStatement data.toParameters object
  | .route8RateFails, object =>
      Route8RateFailsStatement data.toParameters object
  | .route8PiecesClassified, object =>
      Route8PiecesClassifiedStatement data.toParameters object
  | .route8UnifiedNegative, object =>
      -- `def:typeA-unified-negative`: only the exact canonical collection and
      -- its cleared defining sum; all quantitative and entry facts are later.
      Route8UnifiedNegative data.toParameters object
  | .route8UnifiedDeficit, object =>
      Route8UnifiedDeficitFact data.toParameters object
  | .route8UnifiedEntryCensus, object =>
      Route8UnifiedEntryCensusFact data.toParameters object
  | .route8StageRateFailed, object =>
      Route8StageRateFailedFact data.toParameters object
  | .route8OpenBoundarySaturated, object =>
      Route8OpenBoundarySaturatedStatement data.toParameters object
  | .route8DemandUnitCount, object =>
      Route8DemandUnitCountStatement data.toParameters object
  | .route8DemandAbsorption, object =>
      Route8DemandAbsorptionStatement data.toParameters object
  | .windowShadowHitCycle, object =>
      WindowShadowHitCycleStatement data.toParameters object
  | .windowShadowHitExcluded, object =>
      WindowShadowHitExcludedStatement data.toParameters object
  | .route8WindowBlockers, object =>
      Route8WindowBlockersStatement data.toParameters object
  | .route8UnpaidExitFourResidual, object =>
      Route8UnpaidExitFourResidualStatement data.toParameters object
  | .route8UnifiedVisibleResidual, object =>
      Route8UnifiedVisibleResidualStatement data.toParameters object
  | .route8UnifiedVisibleOverload, object =>
      Route8UnifiedVisibleOverloadStatement data.toParameters object
  | .route8JointBalance, object =>
      Route8JointBalanceStatement data.toParameters object
  | .route8TwoCarrierEntry, object =>
      Route8TwoCarrierEntryStatement data.toParameters object
  | .route8NoTwoCarrierEntry, object =>
      Route8NoTwoCarrierEntryStatement data.toParameters object
  | .route8TrueTwoCarrierEntry, object =>
      Route8TrueTwoCarrierEntryStatement data.toParameters object
  | .route8PeelingDescent, object =>
      Route8PeelingDescentStatement data.toParameters object
  | .route8UnifiedTrueTwoCarrierEntry, object =>
      Route8UnifiedTrueTwoCarrierEntryStatement data.toParameters object
  | .sparseSlackSurplus, object =>
      SparseSlackSurplusStatement data.toParameters object
  | .activeSurplusFamily, object =>
      ActiveSurplusFamilyStatement data.toParameters object
  | .sparsePortActivation, object =>
      SparsePortActivationStatement data.toParameters object
  | .baselineSpineDemand, object =>
      BaselineSpineDemandStatement data.toParameters object
  | .canonicalPairLedger, object =>
      CanonicalPairLedgerStatement data.toParameters object
  | .sparsePairExit, object =>
      SparsePairExitStatement data.toParameters object
  | .sparseTargetDefectResidual, object =>
      SparseTargetDefectResidualStatement data.toParameters object
  | .canonicalBlockerRoute, object =>
      CanonicalBlockerRouteStatement data.toParameters object
  | .dependentPairFamily, object =>
      DependentPairFamilyStatement data.toParameters object
  | .independentPairFamily, object =>
      IndependentPairFamilyStatement data.toParameters object
  | .mixedSparseSpineDependence, object =>
      MixedSparseSpineDependenceStatement data.toParameters object
  | .exactCubicBaselineBudget, object =>
      ExactCubicBaselineBudgetStatement data.toParameters object
  | .incrementalSkeletonRoom, object =>
      IncrementalSkeletonRoomStatement data.toParameters object
  | .skeletonDominates, object =>
      SkeletonDominatesStatement object
  | .sparseUpperEnvelope, object =>
      SparseUpperEnvelopeStatement data.toParameters object
  | .capacityTokenLedger, object =>
      CapacityTokenLedgerStatement data.toParameters object
  | .roleFibrePartition, object =>
      RoleFibrePartitionSchema data.toParameters object
  | .fibrePressure, object =>
      FibrePressureSchema data.toParameters object
  | .spineSurplusEstimate, object =>
      SpineSurplusEstimateStatement data.toParameters object
  | .sparsePressureNearCubic, object =>
      SparsePressureNearCubicStatement data.toParameters object
  | .sparsePressureOverload, object =>
      SparsePressureOverloadSchema data.toParameters object
  | .freePairEntropySandwich, object =>
      FreePairEntropySandwichStatement data.toParameters object
  | .freePairCodeUnrealized, object =>
      FreePairCodeUnrealizedStatement data.toParameters object
  | .blockedPairEntropySetup, object =>
      BlockedPairEntropySetupStatement data.toParameters object
  | .blockedPairEntropySandwich, object =>
      BlockedPairEntropySandwichStatement data.toParameters object
  | .blockedPairCodeUnrealized, object =>
      BlockedPairCodeUnrealizedStatement data.toParameters object
  | .pairOverlapFirstFailure, object =>
      PairOverlapFirstFailureStatement data.toParameters object
  | .pairOverlapSystem, object =>
      PairOverlapSystemStatement data.toParameters object
  | .pairConditionalFactorization, object =>
      PairConditionalFactorizationStatement data.toParameters object
  | .pairConditionalFactorizationResidual, object =>
      PairConditionalFactorizationResidualStatement data.toParameters object
  | .pairFailureOverlap, object =>
      PairFailureOverlapStatement data.toParameters object
  | .pairDemandReturns, object =>
      PairDemandReturnsStatement data.toParameters object
  | .pairSystemRealizability, object =>
      PairSystemRealizabilityStatement data.toParameters object
  | .pairSystemEarlyOutcome, object =>
      PairSystemEarlyOutcomeStatement data.toParameters object
  | .pairSerialDemandSystem, object =>
      PairSerialDemandSystemStatement data.toParameters object
  | .pairIncrementCovered, object =>
      PairIncrementCoveredStatement data.toParameters object
  | .pairIncrementEarlyOutcome, object =>
      PairIncrementEarlyOutcomeStatement data.toParameters object
  | .pairSerialArithmetic, object =>
      PairSerialArithmeticStatement data.toParameters object
  | .pairPowerOfTwoCycle, object =>
      PairPowerOfTwoCycleStatement data.toParameters object
  | .windowClassOverload, object =>
      WindowClassOverloadStatement data.toParameters object
  | .windowClassAbsent, object =>
      WindowClassAbsentStatement data.toParameters object
  | .remainderClassOverload, object =>
      RemainderClassOverloadStatement data.toParameters object
  | .remainderClassAbsent, object =>
      RemainderClassAbsentStatement data.toParameters object
  | .homogeneousCapsHold, object =>
      HomogeneousCapsHoldStatement data.toParameters object
  | .homogeneousCapsFail, object =>
      HomogeneousCapsFailStatement data.toParameters object
  | .homogeneousBottleneckPattern, object =>
      HomogeneousBottleneckPatternSchema data.toParameters object
  | .bottleneckRouting, object =>
      BottleneckRoutingStatement data.toParameters object
  | .typeBHandoff, object =>
      -- The direct Type B handoff on the survivor branch, with exactly the
      -- core/envelope clauses proved at `[144]` and no imported Type-A state.
      SameTokenTypeBHandoffStatement data.toParameters object
  | .typeBHandoffFails, object =>
      TypeBHandoffFailsStatement data.toParameters object
  | .sameTokenPatternUnresolved, object =>
      SameTokenPatternPairUnresolvedStatement data.toParameters object
  | .homogeneousBottleneck, object =>
      HomogeneousBottleneckStatement data.toParameters object
  | .sparseSurplusSurvivor, object =>
      SparseSurplusSurvivorStatement data.toParameters object
  | .activeSurplusDemands, object =>
      ActiveSurplusDemandsStatement data.toParameters object
  | .hotColdPartition, object =>
      HotColdWindowStatement data.toParameters object
  -- F4 keys
  | .freePairCountFails, object =>
      FreePairCountFailsStatement data.toParameters object
  | .blockedPairCountFails, object =>
      BlockedPairCountFailsStatement data.toParameters object
  | .blockedPairNoExit, object =>
      BlockedPairNoExitStatement data.toParameters object
  | .primitiveClassOverload, object =>
      PrimitiveClassOverloadStatement data.toParameters object
  | .pairFactorizationFails, object =>
      PairFactorizationFailsStatement data.toParameters object
  | .pairRealizabilityFails, object =>
      PairRealizabilityFailsStatement data.toParameters object
  | .pairSystemNoEarlyOutcome, object =>
      PairSystemNoEarlyOutcomeStatement data.toParameters object
  | .pairIncrementFails, object =>
      PairIncrementFailsStatement data.toParameters object
  | .pairIncrementNoEarlyOutcome, object =>
      PairIncrementNoEarlyOutcomeStatement data.toParameters object
  -- S182 keys
  | .pairCorrelation, object =>
      PairCorrelationStatement data.toParameters object
  | .pairCoverage, object =>
      PairCoverageStatement data.toParameters object
  | .pairFullModulus, object =>
      PairFullModulusStatement data.toParameters object
  | .pairUncrossing, object =>
      PairUncrossingStatement data.toParameters object
  -- F1 keys
  | .typeASupport, object =>
      TypeASupportStatement data.toParameters object
  | .typeANoVisibleEntry, object =>
      TypeANoVisibleEntryStatement data.toParameters object
  | .typeAExitFourAbsent, object =>
      TypeAExitFourAbsentStatement data.toParameters object
  | .typeAExitSixProperScope, object =>
      TypeAExitSixProperScopeStatement data.toParameters object
  | .typeAExitSixGlobalScope, object =>
      TypeAExitSixGlobalScopeStatement data.toParameters object
  -- F3 keys
  | .route8TwoCarrierExit, object =>
      Route8SurvivorTwoCarrierExitStatement data.toParameters object
  | .route8UnifiedTwoCarrierExit, object =>
      Route8UnifiedTwoCarrierExitStatement data.toParameters object
  | .route8StageRate, object =>
      Route8StageRateStatement data.toParameters object
  | .route8UnpaidTwoCarrier, object =>
      Route8UnpaidTwoCarrierStatement data.toParameters object
  | .route8UnpaidWitnessFree, object =>
      Route8UnpaidWitnessFreeStatement data.toParameters object
  -- R3 keys
  | .route8UnifiedEmptyAtG, object =>
      Route8UnifiedEmptyAtGStatement data.toParameters object
  -- R8Q keys
  | .route8QuotientEntriesAtG, object =>
      Route8QuotientEntriesAtGStatement data.toParameters object
  | .typeBSublinearCanonicalForm, object =>
      TypeBSublinearCanonicalFormStatement data.toParameters object
  | .groupedAbsorbedCoreSubset, object =>
      GroupedAbsorbedCoreSubsetStatement data.toParameters object
  | .typeBSublinearFailureArms, object =>
      TypeBSublinearFailureArmsStatement data.toParameters object
  | .groupedCentresHigh, object =>
      GroupedCentresHighStatement data.toParameters object
  | .handoffDegreeClauseEmpty, object =>
      HandoffDegreeClauseEmptyStatement data.toParameters object
  | .pieceRoutingTotal, object =>
      PieceRoutingTotalStatement data.toParameters object
  | .coverPayment, object =>
      CoverPaymentStatement data.toParameters object
  | .loadFailureSaturated, object =>
      LoadFailureSaturatedStatement data.toParameters object
  | .unpaidAbsorbedWindowPort, object =>
      UnpaidAbsorbedWindowPortStatement data.toParameters object
  | .receiverPortsAreWindowStubs, object =>
      ReceiverPortsAreWindowStubsStatement data.toParameters object
  | .saturatedReceiverBasin, object =>
      SaturatedReceiverBasinStatement data.toParameters object
  | .loadFlowValue, object =>
      LoadFlowValueStatement data.toParameters object
  | .coverFlowValue, object =>
      CoverFlowValueStatement data.toParameters object
  | .pieceSizeProfile, object =>
      PieceSizeProfileStatement data.toParameters object
  -- R3b keys
  | .typeAExitFourSwitchCycle, object =>
      TypeAExitFourSwitchCycleStatement data.toParameters object
  | .typeAExitSevenSwitch, object =>
      TypeAExitSevenSwitchStatement data.toParameters object
  -- F5 keys
  | .coldNoPositiveGerm, object =>
      ColdNoPositiveGermStatement data.toParameters object
  -- SD keys (final pass)
  | .degreeProfileFibres, object =>
      DegreeProfileFibresStatement data.toParameters object
  | .targetCompleteContextUniversality, object =>
      TargetCompleteContextUniversalityStatement data.toParameters object
  | .hssTargetCycle, object =>
      HssTargetCycleStatement data.toParameters object
  -- SP keys (fix2)
  | .pairResponseObstruction, object =>
      PairResponseObstructionStatement data.toParameters object
  | .pairNoResponseObstruction, object =>
      PairNoResponseObstructionStatement data.toParameters object
  | .pairDegreeProfileFibres, object =>
      PairDegreeProfileFibresStatement data.toParameters object
  | .pairProfileObstruction, object =>
      PairProfileObstructionStatement data.toParameters object
  | .pairNoProfileObstruction, object =>
      PairNoProfileObstructionStatement data.toParameters object
  | .sameTokenReadingsNotReplacement, object =>
      SameTokenReadingsNotReplacementStatement data.toParameters object
  | .twoSwitchForcedPath, object =>
      TwoSwitchForcedPathStatement data.toParameters object
  | .highCentreSplitForced, object =>
      HighCentreSplitForcedStatement data.toParameters object
  | .crossSwitchFamily, object =>
      CrossSwitchFamilyStatement data.toParameters object
  | .sameVertexSwitchForcedPath, object =>
      SameVertexSwitchForcedPathStatement data.toParameters object
  | .sameTokenPatternSupports, object =>
      SameTokenPatternSupportsStatement data.toParameters object
  | .sameTokenPatternSwap, object =>
      SameTokenPatternSwapStatement data.toParameters object
  | .sameTokenPairPartition, object =>
      SameTokenPairPartitionStatement data.toParameters object
  | .coldCutStatesDistinct, object =>
      ColdCutStatesDistinctStatement data.toParameters object
  | .coldRepeatedStateResidual, object =>
      ColdRepeatedStateResidualStatement data.toParameters object
  | .coldHeavyEntryTerminal, object =>
      ColdHeavyEntryTerminalStatement data.toParameters object
  | .entropyJointRealization, object =>
      EntropyJointRealizationStatement data.toParameters object
  | .allColdEntropyResidual, object =>
      AllColdEntropyResidualStatement data.toParameters object
  -- C6 keys (density order)
  | .realizedDensityOrder, object =>
      RealizedDensityOrderStatement data.toParameters object
  | .realizedOrderLarge, object =>
      RealizedOrderLargeStatement data.toParameters object
  | .realizedOrderSmall, object =>
      RealizedOrderSmallStatement data.toParameters object
  | .boundedDensityOrder, object =>
      BoundedDensityOrderStatement data.toParameters object
  | .route8RateFailsJoin, object =>
      Route8RateFailsJoinStatement data.toParameters object
  | .route8RateFailsPiece, object =>
      Route8RateFailsPieceStatement data.toParameters object
  | .route8RateFailsCrossBound, object =>
      Route8RateFailsCrossBoundStatement data.toParameters object
  | .route8RateFailsFlow, object =>
      Route8RateFailsFlowStatement data.toParameters object
  | .route8CarrierInjection, object =>
      Route8CarrierInjectionStatement data.toParameters object
  | .route8RateExactSlack, object =>
      Route8RateExactSlackStatement data.toParameters object
  | .route8StubDeficit, object =>
      Route8StubDeficitStatement data.toParameters object
  | .route8DeficitVsStubs, object =>
      Route8DeficitVsStubsStatement data.toParameters object
  | .route8EntryLowerBound, object =>
      Route8EntryLowerBoundStatement data.toParameters object
  | .route8CoreEmpty, object =>
      Route8CoreEmptyStatement data.toParameters object
  | .route8StrongRate, object =>
      Route8StrongRateStatement data.toParameters object
  | .route8ThinIsolation, object =>
      Route8ThinIsolationStatement data.toParameters object
  | .route8WindowStub, object =>
      Route8WindowStubStatement data.toParameters object
  | .route8ThinSmall, object =>
      Route8ThinSmallStatement data.toParameters object
  | .route8WindowRPathGap, object =>
      Route8WindowRPathGapStatement data.toParameters object
  | .route8HubStubs, object =>
      Route8HubStubsStatement data.toParameters object
  | .route8WindowSelfRPathGap, object =>
      Route8WindowSelfRPathGapStatement data.toParameters object
  | .route8PieceBoundary, object =>
      Route8PieceBoundaryStatement data.toParameters object
  | .route8WindowPieceRank, object =>
      Route8WindowPieceRankStatement data.toParameters object
  | .route8AchievableLengths, object =>
      Route8AchievableLengthsStatement data.toParameters object
  | .boundedOrderLarge, object =>
      BoundedOrderLargeStatement data.toParameters object
  | .boundedOrderSmall, object =>
      BoundedOrderSmallStatement data.toParameters object
  -- [20a] enrichment keys
  | .edgeSurplusIdentity, object =>
      EdgeSurplusIdentityStatement data.toParameters object
  | .surplusDartIdentity, object =>
      SurplusDartIdentityStatement data.toParameters object
  | .highDegreeCountBound, object =>
      HighDegreeCountBoundStatement data.toParameters object
  | .highDegreePositive, object =>
      HighDegreePositiveStatement data.toParameters object
  | .highDegreeSurplusCapacity, object =>
      HighDegreeSurplusCapacityStatement data.toParameters object
  | .packingOrderBound, object =>
      PackingOrderBoundStatement data.toParameters object
  | .ceilSqrtAboveScale, object =>
      CeilSqrtAboveScaleStatement data.toParameters object
  | .orderAboveScaleSquare, object =>
      OrderAboveScaleSquareStatement data.toParameters object
  | .sixVertexExtremalEnvelope, object =>
      SixVertexExtremalEnvelopeStatement object
  | .noSuppressionChordViolation, object =>
      NoSuppressionChordViolationStatement data.toParameters object
  | .admissibleQuotientsLabelInjective, object =>
      AdmissibleQuotientsLabelInjectiveStatement data.toParameters object
  | .singleBoundaryShape, object =>
      SingleBoundaryShapeStatement object
  | .remainderDeficiencyBelowCut, object =>
      RemainderDeficiencyBelowCutStatement data.toParameters object
  | .windowCutCapacity, object =>
      WindowCutCapacityStatement data.toParameters object
  | .canonicalCapacityExplicit, object =>
      CanonicalCapacityExplicitStatement data.toParameters object
  | .primitiveCarrierCount, object =>
      PrimitiveCarrierCountStatement data.toParameters object
  | .canonicalTokenCount, object =>
      CanonicalTokenCountStatement data.toParameters object
  | .canonicalBlockedFreePartition, object =>
      CanonicalBlockedFreePartitionStatement data.toParameters object
  | .canonicalLedgerDeficit, object =>
      CanonicalLedgerDeficitStatement data.toParameters object
  | .pairCountDeficit, object =>
      PairCountDeficitStatement data.toParameters object
  | .canonicalCertificationCriterion, object =>
      CanonicalCertificationCriterionStatement data.toParameters object
  | .paperBudgetBound, object =>
      PaperBudgetBoundStatement data.toParameters object
  | .paperBudgetCertifies, object =>
      PaperBudgetCertifiesStatement data.toParameters object
  | .canonicalOverloadOfFits, object =>
      CanonicalOverloadOfFitsStatement data.toParameters object
  | .canonicalFreeExcessOfCapped, object =>
      CanonicalFreeExcessOfCappedStatement data.toParameters object
  | .pairCodeConfiguration, object =>
      PairCodeConfigurationStatement data.toParameters object
  | .specWitnessStructure, object =>
      SpecWitnessStructureStatement data.toParameters object
  | .everyWitnessSpectrumSplit, object =>
      EveryWitnessSpectrumSplitStatement data.toParameters object
  | .highSurplusConfiguration, object =>
      HighSurplusConfigurationStatement data.toParameters object
  | .highEndpointSwitch, object =>
      HighEndpointSwitchStatement data.toParameters object
  -- port-cycles keys
  | .neighbourhoodPairCount, object =>
      NeighbourhoodPairCountStatement object
  | .starCycleConstraint, object =>
      StarCycleConstraintStatement object
  | .meetingCycleConstraint, object =>
      MeetingCycleConstraintStatement object
  | .highDegreePairSum, object =>
      HighDegreePairSumStatement data.toParameters object
  | .vertexDeletionComponents, object =>
      VertexDeletionComponentsStatement object
  | .cyclesThroughVertex, object =>
      CyclesThroughVertexStatement object
  | .cutVertexBlockPaths, object =>
      CutVertexBlockPathsStatement object
  | .cycleDoubleCount, object =>
      CycleDoubleCountStatement data.toParameters object
  -- port-local keys
  | .threeRouteFan, object =>
      ThreeRouteFanStatement object
  | .threeRouteChain, object =>
      ThreeRouteChainStatement object
  | .windowPositionStubs, object =>
      WindowPositionStubsStatement data.toParameters object
  | .windowAttachmentGap, object =>
      WindowAttachmentGapStatement data.toParameters object
  -- port-joint keys
  | .cubicNeighbourSupply, object =>
      CubicNeighbourSupplyStatement object
  | .hubCountBound, object =>
      HubCountBoundStatement object
  | .lowEdgeParity, object =>
      LowEdgeParityStatement object
  | .bigHubBound, object =>
      BigHubBoundStatement object
  | .bigHubVShapes, object =>
      BigHubVShapesStatement object
  | .highSurplusBound, object =>
      HighSurplusBoundStatement object
  | .hubLengthThreePairs, object =>
      HubLengthThreePairsStatement object
  | .densityExcess, object =>
      DensityExcessStatement object
  | .remainderSlack, object =>
      RemainderSlackStatement data.toParameters object
  | .hubWindowBudget, object =>
      HubWindowBudgetStatement data.toParameters object
  | .windowHubBounds, object =>
      WindowHubBoundsStatement data.toParameters object
  | .remainderPathBounds, object =>
      RemainderPathBoundsStatement data.toParameters object
  | .windowFreeGeometry, object =>
      WindowFreeGeometryStatement data.toParameters object
  | .inducedPathAttachment, object =>
      InducedPathAttachmentStatement object
  | .highSurplusOrder, object =>
      HighSurplusOrderStatement data.toParameters object
  | .windowChargeKinds, object =>
      WindowChargeKindsStatement data.toParameters object
  | .responseObstructionTargetDefect, object =>
      ResponseObstructionTargetDefectStatement data.toParameters object
  | .hubLinkStructure, object =>
      HubLinkStructureStatement data.toParameters object
  | .hubClassCounts, object =>
      HubClassCountsStatement object
  | .slotRelation, object =>
      SlotRelationStatement object
  | .closedClasses, object =>
      ClosedClassesStatement data.toParameters object
  | .hubTwoHopLinks, object =>
      HubTwoHopLinksStatement data.toParameters object
  | .slotLinear, object =>
      SlotLinearStatement data.toParameters object
  | .scalePressure, object =>
      ScalePressureStatement data.toParameters object
  | .freeSideStructure, object =>
      FreeSideStructureStatement data.toParameters object
  | .freeSideCount, object =>
      FreeSideCountStatement data.toParameters object
  | .freeSideHubs, object =>
      FreeSideHubsStatement data.toParameters object
  | .extFreeEmpty, object =>
      ExtFreeEmptyStatement data.toParameters object
  | .extLoadSum, object =>
      ExtLoadSumStatement data.toParameters object
  | .extOverload, object =>
      ExtOverloadStatement data.toParameters object
  | .extOverloadedToken, object =>
      ExtOverloadedTokenStatement data.toParameters object
  | .newLoadBound, object =>
      NewLoadBoundStatement data.toParameters object
  | .separatedPairs, object =>
      SeparatedPairsStatement data.toParameters object
  | .portEndDegree, object =>
      PortEndDegreeStatement data.toParameters object
  | .pairArmAPattern, object =>
      PairArmAPatternStatement data.toParameters object
  | .pairArmARoleAlphabet, object =>
      PairArmARoleAlphabetStatement data.toParameters object
  | .pairArmB, object =>
      PairArmBStatement data.toParameters object
  -- g-repair R1 keys
  | .sparseTargetDefectEmpty, object =>
      SparseTargetDefectEmptyStatement data.toParameters object
  -- g-repair R5 keys
  | .sameTokenTransplantSize, object =>
      SameTokenTransplantSizeStatement data.toParameters object
  | .sameTokenTransplantDeficit, object =>
      SameTokenTransplantDeficitStatement data.toParameters object
  -- g-audit S144a keys
  | .sameTokenUnresolvedDecided, object =>
      SameTokenUnresolvedDecidedStatement data.toParameters object
  | .sameTokenReadingsExact, object =>
      SameTokenReadingsExactStatement data.toParameters object
  | .sameTokenSwap, object =>
      SameTokenSwapStatement data.toParameters object
  | .sameTokenSwapExact, object =>
      SameTokenSwapExactStatement data.toParameters object
  | .sameTokenU2FreeWhole, object =>
      SameTokenU2FreeWholeStatement data.toParameters object
  -- g-audit 172a keys
  | .blockedOwnRecord, object =>
      BlockedOwnRecordStatement data.toParameters object
  | .blockedFailureSlack, object =>
      BlockedFailureSlackStatement data.toParameters object
  | .blockedPrefixCompression, object =>
      BlockedPrefixCompressionStatement data.toParameters object
  | .blockedFailingSetCarries, object =>
      BlockedFailingSetCarriesStatement data.toParameters object
  | .blockedOverlapSupport, object =>
      BlockedOverlapSupportStatement data.toParameters object
  | .pairHandoffSupport, object =>
      PairHandoffSupportStatement data.toParameters object
  | .pairHandoffCharge, object =>
      PairHandoffChargeStatement data.toParameters object
  | .pairHandoffNetCharge, object =>
      PairHandoffNetChargeStatement data.toParameters object
  | .pairHandoffHubCharge, object =>
      PairHandoffHubChargeStatement data.toParameters object
  | .pairHandoffBoundaryType, object =>
      PairHandoffBoundaryTypeStatement data.toParameters object
  | .pairHandoffCriticalCoordinate, object =>
      PairHandoffCriticalCoordinateStatement data.toParameters object
  | .pairObstructionDescent, object =>
      PairObstructionDescentStatement data.toParameters object
  | .pairHandoffHubForces, object =>
      PairHandoffHubForcesStatement data.toParameters object
  | .pairHandoffDemandEnds, object =>
      PairHandoffDemandEndsStatement data.toParameters object
  | .pairHandoffHubBalance, object =>
      PairHandoffHubBalanceStatement data.toParameters object
  | .pairHandoffFibreAtG, object =>
      PairHandoffFibreAtGStatement data.toParameters object
  | .stubDeficitIdentity, object =>
      StubDeficitIdentityStatement data.toParameters object
  | .remainderCycleSpectrum, object =>
      RemainderCycleSpectrumStatement data.toParameters object
  | .sameTokenSeedCover, object =>
      SameTokenSeedCoverStatement data.toParameters object
  | .sameTokenPathInteractions, object =>
      SameTokenPathInteractionsStatement data.toParameters object
  -- TA keys
  | .typeAPeeledSaturatedReceiver, object =>
      TypeAPeeledSaturatedReceiverStatement data.toParameters object
  | .typeAPeeledUnsaturatedDischarge, object =>
      TypeAPeeledUnsaturatedDischargeStatement data.toParameters object
  | .typeAPeeledVisibleEntry, object =>
      TypeAPeeledVisibleEntryStatement data.toParameters object
  | .typeAPeeledNoVisibleEntry, object =>
      TypeAPeeledNoVisibleEntryStatement data.toParameters object
  | .typeAPeeledSilentExcess, object =>
      TypeAPeeledSilentExcessStatement data.toParameters object
  | .typeAPeeledExitOneReturn, object =>
      TypeAPeeledExitOneReturnStatement data.toParameters object
  | .typeAPeeledExitOneFree, object =>
      TypeAPeeledExitOneFreeStatement data.toParameters object
  | .typeAPeeledExitTwoTheta, object =>
      TypeAPeeledExitTwoThetaStatement data.toParameters object
  | .typeAPeeledExitTwoFree, object =>
      TypeAPeeledExitTwoFreeStatement data.toParameters object
  | .typeAPeeledExitThreeCollision, object =>
      TypeAPeeledExitThreeCollisionStatement data.toParameters object
  | .typeAPeeledExitThreeFree, object =>
      TypeAPeeledExitThreeFreeStatement data.toParameters object
  | .typeAExitThreeCycle, object =>
      TypeAExitThreeCycleStatement data.toParameters object
  | .typeAExitSevenEnvelope, object =>
      TypeAExitSevenEnvelopeStatement data.toParameters object
  | .coldAbsorbedNeutralConfiguration, object =>
      NeutralConfigurationStatement data.toParameters object
  | .coldSelectedFamilyEmpty, object =>
      ColdSelectedFamilyEmptyStatement data.toParameters object
  | .coldMarkedGermUncompressed, object =>
      ColdMarkedGermUncompressedStatement data.toParameters object
  | .coldMarkedGermStretchExcision, object =>
      ColdMarkedGermStretchExcisionStatement data.toParameters object

/-- Audit labels.  They are diagnostics; every routing and lookup decision
compares exact keys. -/
def label : Key → String
  | .route8DemandUnitCount => "route8DemandUnitCount"
  | .route8OpenBoundarySaturated => "route8OpenBoundarySaturated"
  | .windowShadowHitExcluded => "windowShadowHitExcluded"
  | .windowShadowHitCycle => "windowShadowHitCycle"
  | .selection => "selection"
  | .cubicBaseline => "cubicBaseline"
  | .minDegreeBaseline => "minDegreeBaseline"
  | .returnAvoidance => "returnAvoidance"
  | .mersenneReturn => "mersenneReturn"
  | .noProperBaseline => "noProperBaseline"
  | .tightEndpoint => "tightEndpoint"
  | .slackIndependent => "slackIndependent"
  | .cycleRankConstraint => "cycleRankConstraint"
  | .replacementExclusion => "replacementExclusion"
  | .uncompressible => "uncompressible"
  | .windowFree => "windowFree"
  | .windowPresent => "windowPresent"
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
  | .exactResponseProfile => "exactResponseProfile"
  | .curvatureTargetRank => "curvatureTargetRank"
  | .targetRankCircuit => "targetRankCircuit"
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
  | .barrierEnumeration => "barrierEnumeration"
  | .windowPackageSeparated => "windowPackageSeparated"
  | .forcedCurvatureCost => "forcedCurvatureCost"
  | .remainderEntropyHigh => "remainderEntropyHigh"
  | .remainderEntropyLow => "remainderEntropyLow"
  | .localTypeCoordinateRepetitive => "localTypeCoordinateRepetitive"
  | .localTypeCoordinateNonrepetitive => "localTypeCoordinateNonrepetitive"
  | .dominantRootedType => "dominantRootedType"
  | .dominantRootedTypeWedgeFree => "dominantRootedTypeWedgeFree"
  | .dominantRootedWedgeType => "dominantRootedWedgeType"
  | .independentObstructionTranslates => "independentObstructionTranslates"
  | .entropyPackageDemand => "entropyPackageDemand"
  | .entropyCapActive => "entropyCapActive"
  | .entropyCapBound => "entropyCapBound"
  | .largeBudgetResidual => "largeBudgetResidual"
  | .netDeficiencyCap => "netDeficiencyCap"
  | .exactCollisionFails => "exactCollisionFails"
  | .absorbedConfigurationResidual => "absorbedConfigurationResidual"
  | .netChargeCap => "netChargeCap"
  | .netChargeLocalization => "netChargeLocalization"
  | .netChargeNonNegative => "netChargeNonNegative"
  | .netChargeNegative => "netChargeNegative"
  | .negativeSupport => "negativeSupport"
  | .typeALowSurplus => "typeALowSurplus"
  | .typeABoundedSupport => "typeABoundedSupport"
  | .typeBHighSurplus => "typeBHighSurplus"
  | .typeBAssignedSupport => "typeBAssignedSupport"
  | .typeBFanEntry => "typeBFanEntry"
  | .typeBFanHeavyCentre => "typeBFanHeavyCentre"
  | .typeBFanDegreeFourCentres => "typeBFanDegreeFourCentres"
  | .sameCenterOpenPortCompatibility => "sameCenterOpenPortCompatibility"
  | .typeBFanLocalDichotomy => "typeBFanLocalDichotomy"
  | .typeBFanDegreeFourProfile => "typeBFanDegreeFourProfile"
  | .triangularFanCore => "triangularFanCore"
  | .triangularShoulderCompletion => "triangularShoulderCompletion"
  | .triangularPortReturn => "triangularPortReturn"
  | .triangularFirstLanding => "triangularFirstLanding"
  | .triangularCrossShoulder => "triangularCrossShoulder"
  | .openPortSuppression => "openPortSuppression"
  | .openPortSuppressionSafe => "openPortSuppressionSafe"
  | .singleOpenPortSuppressionWitness => "singleOpenPortSuppressionWitness"
  | .suppressedFamilyCriticalCycle => "suppressedFamilyCriticalCycle"
  | .compatiblePairFanClosure => "compatiblePairFanClosure"
  | .fanClosedPortTypeBRouting => "fanClosedPortTypeBRouting"
  | .compatiblePairTypeBRouting => "compatiblePairTypeBRouting"
  | .triangularPortTypeBRouting => "triangularPortTypeBRouting"
  | .typeAReceiverRouting => "typeAReceiverRouting"
  | .typeASaturatedReceiver => "typeASaturatedReceiver"
  | .typeAUnsaturatedReceivers => "typeAUnsaturatedReceivers"
  | .typeAUnsaturatedDischarge => "typeAUnsaturatedDischarge"
  | .typeAExclusion => "typeAExclusion"
  | .typeBBridgeReduction => "typeBBridgeReduction"
  | .typeBSublinearLedger => "typeBSublinearLedger"
  | .typeBSublinearResidual => "typeBSublinearResidual"
  | .route8QuotientFree => "route8QuotientFree"
  | .route8QuotientResidual => "route8QuotientResidual"
  | .route8DemandLedger => "route8DemandLedger"
  | .route8ExtractedEntryCensus => "route8ExtractedEntryCensus"
  | .typeAPortReturn => "typeAPortReturn"
  | .typeAVisibleEntry => "typeAVisibleEntry"
  | .typeAVisibleFirstExcess => "typeAVisibleFirstExcess"
  | .typeAExitOneReturn => "typeAExitOneReturn"
  | .typeAExitOneFree => "typeAExitOneFree"
  | .typeAExitTwoTheta => "typeAExitTwoTheta"
  | .typeAExitTwoFree => "typeAExitTwoFree"
  | .typeAExitThreeCollision => "typeAExitThreeCollision"
  | .typeAExitThreeFree => "typeAExitThreeFree"
  | .typeASaturatedExitEntry => "typeASaturatedExitEntry"
  | .typeAExitSevenHandoff => "typeAExitSevenHandoff"
  | .typeBDecoratedAssignedSupport => "typeBDecoratedAssignedSupport"
  | .typeAExitSevenFree => "typeAExitSevenFree"
  | .coldFailureCycle => "coldFailureCycle"
  | .coldFailureDefectRoute => "coldFailureDefectRoute"
  | .coldFailureCompression => "coldFailureCompression"
  | .coldFailureRouting => "coldFailureRouting"
  | .coldFirstFailureOccurrence => "coldFirstFailureOccurrence"
  | .coldExchangeBound => "coldExchangeBound"
  | .coldRoute8Below => "coldRoute8Below"
  | .coldRoute8AtOrAbove => "coldRoute8AtOrAbove"
  | .coldHotEntropyOverflow => "coldHotEntropyOverflow"
  | .coldHotEntropyCap => "coldHotEntropyCap"
  | .coldMass => "coldMass"
  | .coldAmbientCubic => "coldAmbientCubic"
  | .coldStubExcess => "coldStubExcess"
  | .coldMassLinear => "coldMassLinear"
  | .coldMassBounded => "coldMassBounded"
  | .bridgeless => "bridgeless"
  | .coldReturnCorridors => "coldReturnCorridors"
  | .windowPackageRealized => "windowPackageRealized"
  | .windowPackageUnrealized => "windowPackageUnrealized"
  | .denseDeficiencyBelow => "denseDeficiencyBelow"
  | .denseDeficiencyAtOrAbove => "denseDeficiencyAtOrAbove"
  | .denseColdCorridorsTerminal => "denseColdCorridorsTerminal"
  | .coldNeutralEqualLengthTerminal => "coldNeutralEqualLengthTerminal"
  | .coldWindowStubStructure => "coldWindowStubStructure"
  | .coldCanonicalNeutralConfiguration => "coldCanonicalNeutralConfiguration"
  | .coldGenuineSecondStrand => "coldGenuineSecondStrand"
  | .coldTwoStrandSurvivor => "coldTwoStrandSurvivor"
  | .coldSymmetricPairExcluded => "coldSymmetricPairExcluded"
  | .coldCanonicalSwapSmaller => "coldCanonicalSwapSmaller"
  | .coldCanonicalSwapSameSize => "coldCanonicalSwapSameSize"
  | .coldCanonicalReplacementSwap => "coldCanonicalReplacementSwap"
  | .coldCanonicalReplacementTrivial => "coldCanonicalReplacementTrivial"
  | .blockedClassMember => "blockedClassMember"
  | .blockedScaleAdditive => "blockedScaleAdditive"
  | .blockedCompressionBound => "blockedCompressionBound"
  | .blockedCompressionCap => "blockedCompressionCap"
  | .blockedBarrierOverlap => "blockedBarrierOverlap"
  | .absorbedGermFanData => "absorbedGermFanData"
  | .absorbedGermSplit => "absorbedGermSplit"
  | .coldFamilyPositive => "coldFamilyPositive"
  | .coldFamilyEmpty => "coldFamilyEmpty"
  | .coldGermCandidates => "coldGermCandidates"
  | .coldGermFamilyPositive => "coldGermFamilyPositive"
  | .coldSelectedBranchExcess => "coldSelectedBranchExcess"
  | .coldAmbientCubicStubExcess => "coldAmbientCubicStubExcess"
  | .coldHandoffTransfer => "coldHandoffTransfer"
  | .coldPositiveGerm => "coldPositiveGerm"
  | .coldGermRouted => "coldGermRouted"
  | .coldBranchClosed => "coldBranchClosed"
  | .coldGermSomeRealizing => "coldGermSomeRealizing"
  | .coldGermNoneRealizing => "coldGermNoneRealizing"
  | .coldGermSomeDistinguishing => "coldGermSomeDistinguishing"
  | .coldGermNoneDistinguishing => "coldGermNoneDistinguishing"
  | .highCentreNormalForm => "highCentreNormalForm"
  | .fanCertificateCap => "fanCertificateCap"
  | .fanCertificateMarked => "fanCertificateMarked"
  | .fanCertificateResidual => "fanCertificateResidual"
  | .typeBHybridEntry => "typeBHybridEntry"
  | .typeBDirectCycleFree => "typeBDirectCycleFree"
  | .typeBB2Choice => "typeBB2Choice"
  | .typeBDisjointLedger => "typeBDisjointLedger"
  | .typeBOverlapObstruction => "typeBOverlapObstruction"
  | .typeBGlobalLocalBridge => "typeBGlobalLocalBridge"
  | .fanCertificateResidualMass => "fanCertificateResidualMass"
  | .typeBOverlapObstructionMass => "typeBOverlapObstructionMass"
  | .typeBAbsorbedHalfEdge => "typeBAbsorbedHalfEdge"
  | .typeBAbsorbedHalfEdgeAbsent => "typeBAbsorbedHalfEdgeAbsent"
  | .absorbedHandoffCore => "absorbedHandoffCore"
  | .absorbedHandoffCoreAbsent => "absorbedHandoffCoreAbsent"
  | .absorbedF4Charge => "absorbedF4Charge"
  | .typeBDegreeFourLedger => "typeBDegreeFourLedger"
  | .typeBDegreeFourOverlap => "typeBDegreeFourOverlap"
  | .typeBDegreeFourClosed => "typeBDegreeFourClosed"
  | .typeBAbsorbedCharge => "typeBAbsorbedCharge"
  | .typeBRoute8Entry => "typeBRoute8Entry"
  | .typeBBridgeMass => "typeBBridgeMass"
  | .typeBBridgeSublinear => "typeBBridgeSublinear"
  | .typeBExcluded => "typeBExcluded"
  | .typeBExclusionResidual => "typeBExclusionResidual"
  | .typeAExitFourPeeled => "typeAExitFourPeeled"
  | .typeAExitFourFiniteDescent => "typeAExitFourFiniteDescent"
  | .typeASaturatedHandoffExitFour => "typeASaturatedHandoffExitFour"
  | .typeASaturatedHandoffExitFourFree =>
      "typeASaturatedHandoffExitFourFree"
  | .typeAExitFourReceiverDischarged => "typeAExitFourReceiverDischarged"
  | .typeAExitFive => "typeAExitFive"
  | .typeAExitFiveFree => "typeAExitFiveFree"
  | .typeAExitSix => "typeAExitSix"
  | .typeAExitSixFree => "typeAExitSixFree"
  | .typeAExitSixProper => "typeAExitSixProper"
  | .typeAExitSixGlobal => "typeAExitSixGlobal"
  | .route8ResidualProfile => "route8ResidualProfile"
  | .route8BasinBurden => "route8BasinBurden"
  | .route8LargeBudgetDeficit => "route8LargeBudgetDeficit"
  | .route8LargeBudgetDeficitFails => "route8LargeBudgetDeficitFails"
  | .route8CarrierCore => "route8CarrierCore"
  | .route8TrueResidual => "route8TrueResidual"
  | .route8CarrierCutParity => "route8CarrierCutParity"
  | .route8SmallCoreEntry => "route8SmallCoreEntry"
  | .route8NoSmallCoreEntry => "route8NoSmallCoreEntry"
  | .route8SmallCoreCollapse => "route8SmallCoreCollapse"
  | .route8CarrierDeletionWitnesses => "route8CarrierDeletionWitnesses"
  | .route8PrivateCarrierBudget => "route8PrivateCarrierBudget"
  | .route8Census => "route8Census"
  | .route8Rate => "route8Rate"
  | .route8RateFails => "route8RateFails"
  | .route8PiecesClassified => "route8PiecesClassified"
  | .route8UnifiedNegative => "route8UnifiedNegative"
  | .route8UnifiedDeficit => "route8UnifiedDeficit"
  | .route8UnifiedEntryCensus => "route8UnifiedEntryCensus"
  | .route8StageRateFailed => "route8StageRateFailed"
  | .route8DemandAbsorption => "route8DemandAbsorption"
  | .route8WindowBlockers => "route8WindowBlockers"
  | .route8UnpaidExitFourResidual => "route8UnpaidExitFourResidual"
  | .route8UnifiedVisibleResidual => "route8UnifiedVisibleResidual"
  | .route8UnifiedVisibleOverload => "route8UnifiedVisibleOverload"
  | .route8JointBalance => "route8JointBalance"
  | .route8TwoCarrierEntry => "route8TwoCarrierEntry"
  | .route8NoTwoCarrierEntry => "route8NoTwoCarrierEntry"
  | .route8TrueTwoCarrierEntry => "route8TrueTwoCarrierEntry"
  | .route8PeelingDescent => "route8PeelingDescent"
  | .route8UnifiedTrueTwoCarrierEntry => "route8UnifiedTrueTwoCarrierEntry"
  | .sparseSlackSurplus => "sparseSlackSurplus"
  | .activeSurplusFamily => "activeSurplusFamily"
  | .sparsePortActivation => "sparsePortActivation"
  | .baselineSpineDemand => "baselineSpineDemand"
  | .canonicalPairLedger => "canonicalPairLedger"
  | .sparsePairExit => "sparsePairExit"
  | .sparseTargetDefectResidual => "sparseTargetDefectResidual"
  | .canonicalBlockerRoute => "canonicalBlockerRoute"
  | .sparseUpperEnvelope => "sparseUpperEnvelope"
  | .capacityTokenLedger => "capacityTokenLedger"
  | .roleFibrePartition => "roleFibrePartition"
  | .fibrePressure => "fibrePressure"
  | .spineSurplusEstimate => "spineSurplusEstimate"
  | .sparsePressureNearCubic => "sparsePressureNearCubic"
  | .sparsePressureOverload => "sparsePressureOverload"
  | .freePairEntropySandwich => "freePairEntropySandwich"
  | .freePairCodeUnrealized => "freePairCodeUnrealized"
  | .blockedPairEntropySetup => "blockedPairEntropySetup"
  | .blockedPairEntropySandwich => "blockedPairEntropySandwich"
  | .blockedPairCodeUnrealized => "blockedPairCodeUnrealized"
  | .pairOverlapFirstFailure => "pairOverlapFirstFailure"
  | .pairOverlapSystem => "pairOverlapSystem"
  | .pairConditionalFactorization => "pairConditionalFactorization"
  | .pairConditionalFactorizationResidual =>
      "pairConditionalFactorizationResidual"
  | .pairFailureOverlap => "pairFailureOverlap"
  | .pairDemandReturns => "pairDemandReturns"
  | .pairSystemRealizability => "pairSystemRealizability"
  | .pairSystemEarlyOutcome => "pairSystemEarlyOutcome"
  | .pairSerialDemandSystem => "pairSerialDemandSystem"
  | .pairIncrementCovered => "pairIncrementCovered"
  | .pairIncrementEarlyOutcome => "pairIncrementEarlyOutcome"
  | .pairSerialArithmetic => "pairSerialArithmetic"
  | .pairPowerOfTwoCycle => "pairPowerOfTwoCycle"
  | .windowClassOverload => "windowClassOverload"
  | .windowClassAbsent => "windowClassAbsent"
  | .remainderClassOverload => "remainderClassOverload"
  | .remainderClassAbsent => "remainderClassAbsent"
  | .homogeneousCapsHold => "homogeneousCapsHold"
  | .homogeneousCapsFail => "homogeneousCapsFail"
  | .homogeneousBottleneckPattern => "homogeneousBottleneckPattern"
  | .bottleneckRouting => "bottleneckRouting"
  | .typeBHandoff => "typeBHandoff"
  | .typeBHandoffFails => "typeBHandoffFails"
  | .sameTokenPatternUnresolved => "sameTokenPatternUnresolved"
  | .homogeneousBottleneck => "homogeneousBottleneck"
  | .sparseSurplusSurvivor => "sparseSurplusSurvivor"
  | .activeSurplusDemands => "activeSurplusDemands"
  | .hotColdPartition => "hotColdPartition"
  | .dependentPairFamily => "dependentPairFamily"
  | .independentPairFamily => "independentPairFamily"
  | .mixedSparseSpineDependence => "mixedSparseSpineDependence"
  | .exactCubicBaselineBudget => "exactCubicBaselineBudget"
  | .incrementalSkeletonRoom => "incrementalSkeletonRoom"
  | .skeletonDominates => "skeletonDominates"
  -- F4 keys
  | .freePairCountFails => "freePairCountFails"
  | .blockedPairCountFails => "blockedPairCountFails"
  | .blockedPairNoExit => "blockedPairNoExit"
  | .primitiveClassOverload => "primitiveClassOverload"
  | .pairFactorizationFails => "pairFactorizationFails"
  | .pairRealizabilityFails => "pairRealizabilityFails"
  | .pairSystemNoEarlyOutcome => "pairSystemNoEarlyOutcome"
  | .pairIncrementFails => "pairIncrementFails"
  | .pairIncrementNoEarlyOutcome => "pairIncrementNoEarlyOutcome"
  | .pairCorrelation => "pairCorrelation"
  | .pairCoverage => "pairCoverage"
  | .pairFullModulus => "pairFullModulus"
  | .pairUncrossing => "pairUncrossing"
  -- SP keys
  -- F1 keys
  | .typeASupport => "typeASupport"
  | .typeANoVisibleEntry => "typeANoVisibleEntry"
  | .typeAExitFourAbsent => "typeAExitFourAbsent"
  | .typeAExitSixProperScope => "typeAExitSixProperScope"
  | .typeAExitSixGlobalScope => "typeAExitSixGlobalScope"
  -- F3 keys
  | .route8TwoCarrierExit => "route8TwoCarrierExit"
  | .route8UnifiedTwoCarrierExit => "route8UnifiedTwoCarrierExit"
  | .route8StageRate => "route8StageRate"
  | .route8UnpaidTwoCarrier => "route8UnpaidTwoCarrier"
  | .route8UnpaidWitnessFree => "route8UnpaidWitnessFree"
  -- R3 keys
  | .route8UnifiedEmptyAtG => "route8UnifiedEmptyAtG"
  -- R8Q keys
  | .route8QuotientEntriesAtG => "route8QuotientEntriesAtG"
  | .typeBSublinearCanonicalForm => "typeBSublinearCanonicalForm"
  | .groupedAbsorbedCoreSubset => "groupedAbsorbedCoreSubset"
  | .typeBSublinearFailureArms => "typeBSublinearFailureArms"
  | .groupedCentresHigh => "groupedCentresHigh"
  | .handoffDegreeClauseEmpty => "handoffDegreeClauseEmpty"
  | .pieceRoutingTotal => "pieceRoutingTotal"
  | .coverPayment => "coverPayment"
  | .loadFailureSaturated => "loadFailureSaturated"
  | .unpaidAbsorbedWindowPort => "unpaidAbsorbedWindowPort"
  | .receiverPortsAreWindowStubs => "receiverPortsAreWindowStubs"
  | .saturatedReceiverBasin => "saturatedReceiverBasin"
  | .loadFlowValue => "loadFlowValue"
  | .coverFlowValue => "coverFlowValue"
  | .pieceSizeProfile => "pieceSizeProfile"
  -- R3b keys
  | .typeAExitFourSwitchCycle => "typeAExitFourSwitchCycle"
  | .typeAExitSevenSwitch => "typeAExitSevenSwitch"
  -- F5 keys
  | .coldNoPositiveGerm => "coldNoPositiveGerm"
  -- SD keys (final pass)
  | .degreeProfileFibres => "degreeProfileFibres"
  | .targetCompleteContextUniversality => "targetCompleteContextUniversality"
  | .hssTargetCycle => "hssTargetCycle"
  -- SP keys (fix2)
  | .pairResponseObstruction => "pairResponseObstruction"
  | .pairNoResponseObstruction => "pairNoResponseObstruction"
  | .pairDegreeProfileFibres => "pairDegreeProfileFibres"
  | .pairProfileObstruction => "pairProfileObstruction"
  | .pairNoProfileObstruction => "pairNoProfileObstruction"
  | .sameTokenReadingsNotReplacement => "sameTokenReadingsNotReplacement"
  | .twoSwitchForcedPath => "twoSwitchForcedPath"
  | .highCentreSplitForced => "highCentreSplitForced"
  | .crossSwitchFamily => "crossSwitchFamily"
  | .sameVertexSwitchForcedPath => "sameVertexSwitchForcedPath"
  | .sameTokenPatternSupports => "sameTokenPatternSupports"
  | .sameTokenPatternSwap => "sameTokenPatternSwap"
  | .sameTokenPairPartition => "sameTokenPairPartition"
  | .coldCutStatesDistinct => "coldCutStatesDistinct"
  | .coldRepeatedStateResidual => "coldRepeatedStateResidual"
  | .coldHeavyEntryTerminal => "coldHeavyEntryTerminal"
  | .entropyJointRealization => "entropyJointRealization"
  | .allColdEntropyResidual => "allColdEntropyResidual"
  -- C6 keys (density order)
  | .realizedDensityOrder => "realizedDensityOrder"
  | .realizedOrderLarge => "realizedOrderLarge"
  | .realizedOrderSmall => "realizedOrderSmall"
  | .boundedDensityOrder => "boundedDensityOrder"
  | .route8RateFailsJoin => "route8RateFailsJoin"
  | .route8RateFailsPiece => "route8RateFailsPiece"
  | .route8RateFailsCrossBound => "route8RateFailsCrossBound"
  | .route8RateFailsFlow => "route8RateFailsFlow"
  | .route8CarrierInjection => "route8CarrierInjection"
  | .route8RateExactSlack => "route8RateExactSlack"
  | .route8StubDeficit => "route8StubDeficit"
  | .route8DeficitVsStubs => "route8DeficitVsStubs"
  | .route8EntryLowerBound => "route8EntryLowerBound"
  | .route8CoreEmpty => "route8CoreEmpty"
  | .route8StrongRate => "route8StrongRate"
  | .route8ThinIsolation => "route8ThinIsolation"
  | .route8WindowStub => "route8WindowStub"
  | .route8ThinSmall => "route8ThinSmall"
  | .route8WindowRPathGap => "route8WindowRPathGap"
  | .route8HubStubs => "route8HubStubs"
  | .route8WindowSelfRPathGap => "route8WindowSelfRPathGap"
  | .route8PieceBoundary => "route8PieceBoundary"
  | .route8WindowPieceRank => "route8WindowPieceRank"
  | .route8AchievableLengths => "route8AchievableLengths"
  | .boundedOrderLarge => "boundedOrderLarge"
  | .boundedOrderSmall => "boundedOrderSmall"
  -- [20a] enrichment keys
  | .edgeSurplusIdentity => "edgeSurplusIdentity"
  | .surplusDartIdentity => "surplusDartIdentity"
  | .highDegreeCountBound => "highDegreeCountBound"
  | .highDegreePositive => "highDegreePositive"
  | .highDegreeSurplusCapacity => "highDegreeSurplusCapacity"
  | .packingOrderBound => "packingOrderBound"
  | .ceilSqrtAboveScale => "ceilSqrtAboveScale"
  | .orderAboveScaleSquare => "orderAboveScaleSquare"
  | .sixVertexExtremalEnvelope => "sixVertexExtremalEnvelope"
  | .noSuppressionChordViolation => "noSuppressionChordViolation"
  | .admissibleQuotientsLabelInjective => "admissibleQuotientsLabelInjective"
  | .singleBoundaryShape => "singleBoundaryShape"
  | .remainderDeficiencyBelowCut => "remainderDeficiencyBelowCut"
  | .windowCutCapacity => "windowCutCapacity"
  | .canonicalCapacityExplicit => "canonicalCapacityExplicit"
  | .primitiveCarrierCount => "primitiveCarrierCount"
  | .canonicalTokenCount => "canonicalTokenCount"
  | .canonicalBlockedFreePartition => "canonicalBlockedFreePartition"
  | .canonicalLedgerDeficit => "canonicalLedgerDeficit"
  | .pairCountDeficit => "pairCountDeficit"
  | .canonicalCertificationCriterion => "canonicalCertificationCriterion"
  | .paperBudgetBound => "paperBudgetBound"
  | .paperBudgetCertifies => "paperBudgetCertifies"
  | .canonicalOverloadOfFits => "canonicalOverloadOfFits"
  | .canonicalFreeExcessOfCapped => "canonicalFreeExcessOfCapped"
  | .pairCodeConfiguration => "pairCodeConfiguration"
  | .specWitnessStructure => "specWitnessStructure"
  | .everyWitnessSpectrumSplit => "everyWitnessSpectrumSplit"
  | .highSurplusConfiguration => "highSurplusConfiguration"
  | .highEndpointSwitch => "highEndpointSwitch"
  -- port-cycles keys
  | .neighbourhoodPairCount => "neighbourhoodPairCount"
  | .starCycleConstraint => "starCycleConstraint"
  | .meetingCycleConstraint => "meetingCycleConstraint"
  | .highDegreePairSum => "highDegreePairSum"
  | .vertexDeletionComponents => "vertexDeletionComponents"
  | .cyclesThroughVertex => "cyclesThroughVertex"
  | .cutVertexBlockPaths => "cutVertexBlockPaths"
  | .cycleDoubleCount => "cycleDoubleCount"
  -- port-local keys
  | .threeRouteFan => "threeRouteFan"
  | .threeRouteChain => "threeRouteChain"
  | .windowPositionStubs => "windowPositionStubs"
  | .windowAttachmentGap => "windowAttachmentGap"
  -- port-joint keys
  | .cubicNeighbourSupply => "cubicNeighbourSupply"
  | .hubCountBound => "hubCountBound"
  | .lowEdgeParity => "lowEdgeParity"
  | .bigHubBound => "bigHubBound"
  | .bigHubVShapes => "bigHubVShapes"
  | .highSurplusBound => "highSurplusBound"
  | .hubLengthThreePairs => "hubLengthThreePairs"
  | .densityExcess => "densityExcess"
  | .remainderSlack => "remainderSlack"
  | .hubWindowBudget => "hubWindowBudget"
  | .windowHubBounds => "windowHubBounds"
  | .remainderPathBounds => "remainderPathBounds"
  | .windowFreeGeometry => "windowFreeGeometry"
  | .inducedPathAttachment => "inducedPathAttachment"
  | .highSurplusOrder => "highSurplusOrder"
  | .windowChargeKinds => "windowChargeKinds"
  | .responseObstructionTargetDefect => "responseObstructionTargetDefect"
  | .hubLinkStructure => "hubLinkStructure"
  | .hubClassCounts => "hubClassCounts"
  | .slotRelation => "slotRelation"
  | .closedClasses => "closedClasses"
  | .hubTwoHopLinks => "hubTwoHopLinks"
  | .slotLinear => "slotLinear"
  | .scalePressure => "scalePressure"
  | .freeSideStructure => "freeSideStructure"
  | .freeSideCount => "freeSideCount"
  | .freeSideHubs => "freeSideHubs"
  | .extFreeEmpty => "extFreeEmpty"
  | .extLoadSum => "extLoadSum"
  | .extOverload => "extOverload"
  | .extOverloadedToken => "extOverloadedToken"
  | .newLoadBound => "newLoadBound"
  | .separatedPairs => "separatedPairs"
  | .portEndDegree => "portEndDegree"
  | .pairArmAPattern => "pairArmAPattern"
  | .pairArmARoleAlphabet => "pairArmARoleAlphabet"
  | .pairArmB => "pairArmB"
  | .sparseTargetDefectEmpty => "sparseTargetDefectEmpty"
  | .sameTokenTransplantSize => "sameTokenTransplantSize"
  | .sameTokenTransplantDeficit => "sameTokenTransplantDeficit"
  | .sameTokenUnresolvedDecided => "sameTokenUnresolvedDecided"
  | .sameTokenReadingsExact => "sameTokenReadingsExact"
  | .sameTokenSwap => "sameTokenSwap"
  | .sameTokenSwapExact => "sameTokenSwapExact"
  | .sameTokenU2FreeWhole => "sameTokenU2FreeWhole"
  -- g-audit 172a keys
  | .blockedOwnRecord => "blockedOwnRecord"
  | .blockedFailureSlack => "blockedFailureSlack"
  | .blockedPrefixCompression => "blockedPrefixCompression"
  | .blockedFailingSetCarries => "blockedFailingSetCarries"
  | .blockedOverlapSupport => "blockedOverlapSupport"
  | .pairHandoffSupport => "pairHandoffSupport"
  | .pairHandoffCharge => "pairHandoffCharge"
  | .pairHandoffNetCharge => "pairHandoffNetCharge"
  | .pairHandoffHubCharge => "pairHandoffHubCharge"
  | .pairHandoffBoundaryType => "pairHandoffBoundaryType"
  | .pairHandoffCriticalCoordinate => "pairHandoffCriticalCoordinate"
  | .pairObstructionDescent => "pairObstructionDescent"
  | .pairHandoffHubForces => "pairHandoffHubForces"
  | .pairHandoffDemandEnds => "pairHandoffDemandEnds"
  | .pairHandoffHubBalance => "pairHandoffHubBalance"
  | .pairHandoffFibreAtG => "pairHandoffFibreAtG"
  | .stubDeficitIdentity => "stubDeficitIdentity"
  | .remainderCycleSpectrum => "remainderCycleSpectrum"
  | .sameTokenSeedCover => "sameTokenSeedCover"
  | .sameTokenPathInteractions => "sameTokenPathInteractions"
  -- TA keys
  | .typeAPeeledSaturatedReceiver => "typeAPeeledSaturatedReceiver"
  | .typeAPeeledUnsaturatedDischarge => "typeAPeeledUnsaturatedDischarge"
  | .typeAPeeledVisibleEntry => "typeAPeeledVisibleEntry"
  | .typeAPeeledNoVisibleEntry => "typeAPeeledNoVisibleEntry"
  | .typeAPeeledSilentExcess => "typeAPeeledSilentExcess"
  | .typeAPeeledExitOneReturn => "typeAPeeledExitOneReturn"
  | .typeAPeeledExitOneFree => "typeAPeeledExitOneFree"
  | .typeAPeeledExitTwoTheta => "typeAPeeledExitTwoTheta"
  | .typeAPeeledExitTwoFree => "typeAPeeledExitTwoFree"
  | .typeAPeeledExitThreeCollision => "typeAPeeledExitThreeCollision"
  | .typeAPeeledExitThreeFree => "typeAPeeledExitThreeFree"
  | .typeAExitThreeCycle => "typeAExitThreeCycle"
  | .typeAExitSevenEnvelope => "typeAExitSevenEnvelope"
  | .coldAbsorbedNeutralConfiguration => "coldAbsorbedNeutralConfiguration"
  | .coldSelectedFamilyEmpty => "coldSelectedFamilyEmpty"
  | .coldMarkedGermUncompressed => "coldMarkedGermUncompressed"
  | .coldMarkedGermStretchExcision => "coldMarkedGermStretchExcision"

/-! ### Label pins

Every audit label is the constructor's own name.  `label` is checked for
totality by the elaborator and the numbering below is pinned by `idx`, but
nothing forces the two to agree, so each pairing is stated here.  Each is a
constant-time `rfl`, and together they rule out a mistyped or duplicated
label. -/

section LabelPins
example : label .route8DemandUnitCount = "route8DemandUnitCount" := rfl
example : label .route8OpenBoundarySaturated = "route8OpenBoundarySaturated" := rfl
example : label .windowShadowHitExcluded = "windowShadowHitExcluded" := rfl
example : label .windowShadowHitCycle = "windowShadowHitCycle" := rfl
example : label .selection = "selection" := rfl
example : label .minDegreeBaseline = "minDegreeBaseline" := rfl
example : label .returnAvoidance = "returnAvoidance" := rfl
example : label .noProperBaseline = "noProperBaseline" := rfl
example : label .tightEndpoint = "tightEndpoint" := rfl
example : label .slackIndependent = "slackIndependent" := rfl
example : label .cycleRankConstraint = "cycleRankConstraint" := rfl
example : label .replacementExclusion = "replacementExclusion" := rfl
example : label .uncompressible = "uncompressible" := rfl
example : label .mersenneReturn = "mersenneReturn" := rfl
example : label .windowFree = "windowFree" := rfl
example : label .windowPresent = "windowPresent" := rfl
example : label .maximalPacking = "maximalPacking" := rfl
example : label .localAlgebra = "localAlgebra" := rfl
example : label .surplusAbove = "surplusAbove" := rfl
example : label .surplusAtOrBelow = "surplusAtOrBelow" := rfl
example : label .barrierCap = "barrierCap" := rfl
example : label .barrierOverflow = "barrierOverflow" := rfl
example : label .hotColdPartition = "hotColdPartition" := rfl
example : label .densityCap = "densityCap" := rfl
example : label .remainderNormalized = "remainderNormalized" := rfl
example : label .boundaryDemand = "boundaryDemand" := rfl
example : label .stubSupply = "stubSupply" := rfl
example : label .wedgeSupply = "wedgeSupply" := rfl
example : label .curvatureTargetRank = "curvatureTargetRank" := rfl
example : label .targetRankCircuit = "targetRankCircuit" := rfl
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
example : label .windowPackageSeparated = "windowPackageSeparated" := rfl
example : label .forcedCurvatureCost = "forcedCurvatureCost" := rfl
example : label .remainderEntropyHigh = "remainderEntropyHigh" := rfl
example : label .remainderEntropyLow = "remainderEntropyLow" := rfl
example : label .localTypeCoordinateRepetitive =
    "localTypeCoordinateRepetitive" := rfl
example : label .localTypeCoordinateNonrepetitive =
    "localTypeCoordinateNonrepetitive" := rfl
example : label .dominantRootedType = "dominantRootedType" := rfl
example : label .dominantRootedTypeWedgeFree =
    "dominantRootedTypeWedgeFree" := rfl
example : label .dominantRootedWedgeType = "dominantRootedWedgeType" := rfl
example : label .independentObstructionTranslates =
    "independentObstructionTranslates" := rfl
example : label .entropyPackageDemand = "entropyPackageDemand" := rfl
example : label .entropyCapActive = "entropyCapActive" := rfl
example : label .entropyCapBound = "entropyCapBound" := rfl
example : label .largeBudgetResidual = "largeBudgetResidual" := rfl
example : label .netDeficiencyCap = "netDeficiencyCap" := rfl
example : label .exactCollisionFails = "exactCollisionFails" := rfl
example : label .absorbedConfigurationResidual = "absorbedConfigurationResidual" := rfl
example : label .absorbedGermFanData = "absorbedGermFanData" := rfl
example : label .absorbedGermSplit = "absorbedGermSplit" := rfl
example : label .coldFamilyPositive = "coldFamilyPositive" := rfl
example : label .coldFamilyEmpty = "coldFamilyEmpty" := rfl
example : label .netChargeCap = "netChargeCap" := rfl
example : label .netChargeLocalization = "netChargeLocalization" := rfl
example : label .netChargeNonNegative = "netChargeNonNegative" := rfl
example : label .netChargeNegative = "netChargeNegative" := rfl
example : label .negativeSupport = "negativeSupport" := rfl
example : label .typeALowSurplus = "typeALowSurplus" := rfl
example : label .typeABoundedSupport = "typeABoundedSupport" := rfl
example : label .typeBHighSurplus = "typeBHighSurplus" := rfl
example : label .typeBAssignedSupport = "typeBAssignedSupport" := rfl
example : label .typeBFanEntry = "typeBFanEntry" := rfl
example : label .typeBFanHeavyCentre = "typeBFanHeavyCentre" := rfl
example : label .typeBFanDegreeFourCentres = "typeBFanDegreeFourCentres" := rfl
example : label .sameCenterOpenPortCompatibility =
    "sameCenterOpenPortCompatibility" := rfl
example : label .typeBFanLocalDichotomy = "typeBFanLocalDichotomy" := rfl
example : label .typeBFanDegreeFourProfile = "typeBFanDegreeFourProfile" := rfl
example : label .triangularFanCore = "triangularFanCore" := rfl
example : label .triangularShoulderCompletion =
    "triangularShoulderCompletion" := rfl
example : label .triangularPortReturn = "triangularPortReturn" := rfl
example : label .triangularFirstLanding = "triangularFirstLanding" := rfl
example : label .triangularCrossShoulder = "triangularCrossShoulder" := rfl
example : label .openPortSuppression = "openPortSuppression" := rfl
example : label .openPortSuppressionSafe = "openPortSuppressionSafe" := rfl
example : label .singleOpenPortSuppressionWitness =
    "singleOpenPortSuppressionWitness" := rfl
example : label .suppressedFamilyCriticalCycle =
    "suppressedFamilyCriticalCycle" := rfl
example : label .compatiblePairFanClosure = "compatiblePairFanClosure" := rfl
example : label .fanClosedPortTypeBRouting = "fanClosedPortTypeBRouting" := rfl
example : label .compatiblePairTypeBRouting = "compatiblePairTypeBRouting" := rfl
example : label .triangularPortTypeBRouting =
    "triangularPortTypeBRouting" := rfl
example : label .typeAReceiverRouting = "typeAReceiverRouting" := rfl
example : label .typeASaturatedReceiver = "typeASaturatedReceiver" := rfl
example : label .typeAUnsaturatedReceivers = "typeAUnsaturatedReceivers" := rfl
example : label .typeAUnsaturatedDischarge = "typeAUnsaturatedDischarge" := rfl
example : label .typeAExclusion = "typeAExclusion" := rfl
example : label .typeBBridgeReduction = "typeBBridgeReduction" := rfl
example : label .typeBSublinearLedger = "typeBSublinearLedger" := rfl
example : label .typeBSublinearResidual = "typeBSublinearResidual" := rfl
example : label .route8QuotientFree = "route8QuotientFree" := rfl
example : label .route8QuotientResidual = "route8QuotientResidual" := rfl
example : label .route8DemandLedger = "route8DemandLedger" := rfl
example : label .route8ExtractedEntryCensus = "route8ExtractedEntryCensus" :=
  rfl
example : label .typeAPortReturn = "typeAPortReturn" := rfl
example : label .typeAVisibleEntry = "typeAVisibleEntry" := rfl
example : label .typeAVisibleFirstExcess = "typeAVisibleFirstExcess" := rfl
example : label .typeAExitOneReturn = "typeAExitOneReturn" := rfl
example : label .typeAExitOneFree = "typeAExitOneFree" := rfl
example : label .typeAExitTwoTheta = "typeAExitTwoTheta" := rfl
example : label .typeAExitTwoFree = "typeAExitTwoFree" := rfl
example : label .typeAExitThreeCollision = "typeAExitThreeCollision" := rfl
example : label .typeAExitThreeFree = "typeAExitThreeFree" := rfl
example : label .typeASaturatedExitEntry = "typeASaturatedExitEntry" := rfl
example : label .typeAExitSevenHandoff = "typeAExitSevenHandoff" := rfl
example : label .typeAExitSevenFree = "typeAExitSevenFree" := rfl
example : label .coldFailureCycle = "coldFailureCycle" := rfl
example : label .coldFailureDefectRoute = "coldFailureDefectRoute" := rfl
example : label .coldFailureCompression = "coldFailureCompression" := rfl
example : label .coldFailureRouting = "coldFailureRouting" := rfl
example : label .coldFirstFailureOccurrence = "coldFirstFailureOccurrence" := rfl
example : label .coldExchangeBound = "coldExchangeBound" := rfl
example : label .coldGermFamilyPositive = "coldGermFamilyPositive" := rfl
example : label .coldMassLinear = "coldMassLinear" := rfl
example : label .coldMassBounded = "coldMassBounded" := rfl
example : label .bridgeless = "bridgeless" := rfl
example : label .coldReturnCorridors = "coldReturnCorridors" := rfl
example : label .coldNeutralEqualLengthTerminal =
    "coldNeutralEqualLengthTerminal" := rfl
example : label .windowPackageRealized = "windowPackageRealized" := rfl
example : label .windowPackageUnrealized = "windowPackageUnrealized" := rfl
example : label .denseDeficiencyBelow = "denseDeficiencyBelow" := rfl
example : label .denseDeficiencyAtOrAbove = "denseDeficiencyAtOrAbove" := rfl
example : label .coldWindowStubStructure = "coldWindowStubStructure" := rfl
example : label .coldCanonicalNeutralConfiguration = "coldCanonicalNeutralConfiguration" := rfl
example : label .coldGenuineSecondStrand = "coldGenuineSecondStrand" := rfl
example : label .coldTwoStrandSurvivor = "coldTwoStrandSurvivor" := rfl
example : label .coldSymmetricPairExcluded = "coldSymmetricPairExcluded" := rfl
example : label .coldCanonicalSwapSmaller = "coldCanonicalSwapSmaller" := rfl
example : label .coldCanonicalSwapSameSize = "coldCanonicalSwapSameSize" := rfl
example : label .coldCanonicalReplacementSwap =
    "coldCanonicalReplacementSwap" := rfl
example : label .coldCanonicalReplacementTrivial =
    "coldCanonicalReplacementTrivial" := rfl
example : label .blockedClassMember = "blockedClassMember" := rfl
example : label .blockedScaleAdditive = "blockedScaleAdditive" := rfl
example : label .blockedCompressionBound = "blockedCompressionBound" := rfl
example : label .blockedCompressionCap = "blockedCompressionCap" := rfl
example : label .blockedBarrierOverlap = "blockedBarrierOverlap" := rfl
example : label .coldHandoffTransfer = "coldHandoffTransfer" := rfl
example : label .coldPositiveGerm = "coldPositiveGerm" := rfl
example : label .coldGermRouted = "coldGermRouted" := rfl
example : label .coldBranchClosed = "coldBranchClosed" := rfl
example : label .coldGermSomeRealizing = "coldGermSomeRealizing" := rfl
example : label .coldGermNoneRealizing = "coldGermNoneRealizing" := rfl
example : label .coldGermSomeDistinguishing = "coldGermSomeDistinguishing" := rfl
example : label .coldGermNoneDistinguishing = "coldGermNoneDistinguishing" := rfl
example : label .highCentreNormalForm = "highCentreNormalForm" := rfl
example : label .fanCertificateCap = "fanCertificateCap" := rfl
example : label .fanCertificateMarked = "fanCertificateMarked" := rfl
example : label .fanCertificateResidual = "fanCertificateResidual" := rfl
example : label .typeBHybridEntry = "typeBHybridEntry" := rfl
example : label .typeBDirectCycleFree = "typeBDirectCycleFree" := rfl
example : label .typeBB2Choice = "typeBB2Choice" := rfl
example : label .typeBDisjointLedger = "typeBDisjointLedger" := rfl
example : label .typeBOverlapObstruction = "typeBOverlapObstruction" := rfl
example : label .typeBGlobalLocalBridge = "typeBGlobalLocalBridge" := rfl
example : label .fanCertificateResidualMass = "fanCertificateResidualMass" := rfl
example : label .typeBOverlapObstructionMass = "typeBOverlapObstructionMass" := rfl
example : label .typeBAbsorbedHalfEdge = "typeBAbsorbedHalfEdge" := rfl
example : label .typeBAbsorbedHalfEdgeAbsent = "typeBAbsorbedHalfEdgeAbsent" := rfl
example : label .absorbedHandoffCore = "absorbedHandoffCore" := rfl
example : label .absorbedHandoffCoreAbsent = "absorbedHandoffCoreAbsent" := rfl
example : label .absorbedF4Charge = "absorbedF4Charge" := rfl
example : label .typeBDegreeFourLedger = "typeBDegreeFourLedger" := rfl
example : label .typeBDegreeFourOverlap = "typeBDegreeFourOverlap" := rfl
example : label .typeBDegreeFourClosed = "typeBDegreeFourClosed" := rfl
example : label .typeBAbsorbedCharge = "typeBAbsorbedCharge" := rfl
example : label .typeBRoute8Entry = "typeBRoute8Entry" := rfl
example : label .typeBBridgeMass = "typeBBridgeMass" := rfl
example : label .typeBBridgeSublinear = "typeBBridgeSublinear" := rfl
example : label .typeBExcluded = "typeBExcluded" := rfl
example : label .typeBExclusionResidual = "typeBExclusionResidual" := rfl
example : label .typeAExitFourPeeled = "typeAExitFourPeeled" := rfl
example : label .typeAExitFourFiniteDescent =
    "typeAExitFourFiniteDescent" := rfl
example : label .typeASaturatedHandoffExitFour =
    "typeASaturatedHandoffExitFour" := rfl
example : label .typeASaturatedHandoffExitFourFree =
    "typeASaturatedHandoffExitFourFree" := rfl
example : label .typeAExitFourReceiverDischarged =
    "typeAExitFourReceiverDischarged" := rfl
example : label .typeAExitFive = "typeAExitFive" := rfl
example : label .typeAExitFiveFree = "typeAExitFiveFree" := rfl
example : label .typeAExitSix = "typeAExitSix" := rfl
example : label .typeAExitSixFree = "typeAExitSixFree" := rfl
example : label .typeAExitSixProper = "typeAExitSixProper" := rfl
example : label .typeAExitSixGlobal = "typeAExitSixGlobal" := rfl
example : label .route8ResidualProfile = "route8ResidualProfile" := rfl
example : label .route8BasinBurden = "route8BasinBurden" := rfl
example : label .route8LargeBudgetDeficit = "route8LargeBudgetDeficit" := rfl
example : label .route8LargeBudgetDeficitFails =
    "route8LargeBudgetDeficitFails" := rfl
example : label .route8CarrierCore = "route8CarrierCore" := rfl
example : label .route8TrueResidual = "route8TrueResidual" := rfl
example : label .route8CarrierCutParity = "route8CarrierCutParity" := rfl
example : label .route8SmallCoreEntry = "route8SmallCoreEntry" := rfl
example : label .route8NoSmallCoreEntry = "route8NoSmallCoreEntry" := rfl
example : label .route8SmallCoreCollapse =
    "route8SmallCoreCollapse" := rfl
example : label .route8CarrierDeletionWitnesses =
    "route8CarrierDeletionWitnesses" := rfl
example : label .route8PrivateCarrierBudget =
    "route8PrivateCarrierBudget" := rfl
example : label .route8Census = "route8Census" := rfl
example : label .route8Rate = "route8Rate" := rfl
example : label .route8RateFails = "route8RateFails" := rfl
example : label .route8PiecesClassified = "route8PiecesClassified" := rfl
example : label .route8UnifiedNegative = "route8UnifiedNegative" := rfl
example : label .route8UnifiedDeficit = "route8UnifiedDeficit" := rfl
example : label .route8UnifiedEntryCensus = "route8UnifiedEntryCensus" := rfl
example : label .route8StageRateFailed = "route8StageRateFailed" := rfl
example : label .route8DemandAbsorption = "route8DemandAbsorption" := rfl
example : label .route8WindowBlockers = "route8WindowBlockers" := rfl
example : label .route8UnpaidExitFourResidual =
    "route8UnpaidExitFourResidual" := rfl
example : label .route8UnifiedVisibleResidual =
    "route8UnifiedVisibleResidual" := rfl
example : label .route8UnifiedVisibleOverload =
    "route8UnifiedVisibleOverload" := rfl
example : label .route8JointBalance = "route8JointBalance" := rfl
example : label .route8TwoCarrierEntry = "route8TwoCarrierEntry" := rfl
example : label .route8NoTwoCarrierEntry = "route8NoTwoCarrierEntry" := rfl
example : label .route8TrueTwoCarrierEntry = "route8TrueTwoCarrierEntry" := rfl
example : label .route8PeelingDescent = "route8PeelingDescent" := rfl
example : label .route8UnifiedTrueTwoCarrierEntry =
    "route8UnifiedTrueTwoCarrierEntry" := rfl
example : label .sparseSlackSurplus = "sparseSlackSurplus" := rfl
example : label .activeSurplusFamily = "activeSurplusFamily" := rfl
example : label .sparsePortActivation = "sparsePortActivation" := rfl
example : label .baselineSpineDemand = "baselineSpineDemand" := rfl
example : label .canonicalPairLedger = "canonicalPairLedger" := rfl
example : label .sparsePairExit = "sparsePairExit" := rfl
example : label .sparseTargetDefectResidual =
    "sparseTargetDefectResidual" := rfl
example : label .canonicalBlockerRoute = "canonicalBlockerRoute" := rfl
example : label .sparseUpperEnvelope = "sparseUpperEnvelope" := rfl
example : label .capacityTokenLedger = "capacityTokenLedger" := rfl
example : label .roleFibrePartition = "roleFibrePartition" := rfl
example : label .fibrePressure = "fibrePressure" := rfl
example : label .spineSurplusEstimate = "spineSurplusEstimate" := rfl
example : label .sparsePressureNearCubic = "sparsePressureNearCubic" := rfl
example : label .sparsePressureOverload = "sparsePressureOverload" := rfl
example : label .freePairEntropySandwich = "freePairEntropySandwich" := rfl
example : label .freePairCodeUnrealized = "freePairCodeUnrealized" := rfl
example : label .blockedPairEntropySetup = "blockedPairEntropySetup" := rfl
example : label .blockedPairEntropySandwich = "blockedPairEntropySandwich" := rfl
example : label .blockedPairCodeUnrealized = "blockedPairCodeUnrealized" := rfl
example : label .pairOverlapFirstFailure = "pairOverlapFirstFailure" := rfl
example : label .pairOverlapSystem = "pairOverlapSystem" := rfl
example : label .pairConditionalFactorization =
    "pairConditionalFactorization" := rfl
example : label .pairConditionalFactorizationResidual =
    "pairConditionalFactorizationResidual" := rfl
example : label .pairFailureOverlap = "pairFailureOverlap" := rfl
example : label .pairDemandReturns = "pairDemandReturns" := rfl
example : label .pairSystemRealizability = "pairSystemRealizability" := rfl
example : label .pairSystemEarlyOutcome = "pairSystemEarlyOutcome" := rfl
example : label .pairSerialDemandSystem = "pairSerialDemandSystem" := rfl
example : label .pairIncrementCovered = "pairIncrementCovered" := rfl
example : label .pairIncrementEarlyOutcome =
    "pairIncrementEarlyOutcome" := rfl
example : label .pairSerialArithmetic = "pairSerialArithmetic" := rfl
example : label .pairPowerOfTwoCycle = "pairPowerOfTwoCycle" := rfl
example : label .windowClassOverload = "windowClassOverload" := rfl
example : label .windowClassAbsent = "windowClassAbsent" := rfl
example : label .remainderClassOverload = "remainderClassOverload" := rfl
example : label .remainderClassAbsent = "remainderClassAbsent" := rfl
example : label .homogeneousCapsHold = "homogeneousCapsHold" := rfl
example : label .homogeneousCapsFail = "homogeneousCapsFail" := rfl
example : label .homogeneousBottleneckPattern = "homogeneousBottleneckPattern" := rfl
example : label .bottleneckRouting = "bottleneckRouting" := rfl
example : label .typeBHandoff = "typeBHandoff" := rfl
example : label .typeBHandoffFails = "typeBHandoffFails" := rfl
example : label .sameTokenPatternUnresolved = "sameTokenPatternUnresolved" := rfl
example : label .homogeneousBottleneck = "homogeneousBottleneck" := rfl
example : label .sparseSurplusSurvivor = "sparseSurplusSurvivor" := rfl
example : label .activeSurplusDemands = "activeSurplusDemands" := rfl
example : label .dependentPairFamily = "dependentPairFamily" := rfl
example : label .independentPairFamily = "independentPairFamily" := rfl
example : label .mixedSparseSpineDependence = "mixedSparseSpineDependence" := rfl
example : label .exactCubicBaselineBudget = "exactCubicBaselineBudget" := rfl
example : label .incrementalSkeletonRoom = "incrementalSkeletonRoom" := rfl
example : label .skeletonDominates = "skeletonDominates" := rfl
example : label .exactResponseProfile = "exactResponseProfile" := rfl
example : label .barrierEnumeration = "barrierEnumeration" := rfl
-- F4 keys
example : label .freePairCountFails = "freePairCountFails" := rfl
example : label .blockedPairCountFails = "blockedPairCountFails" := rfl
example : label .blockedPairNoExit = "blockedPairNoExit" := rfl
example : label .primitiveClassOverload = "primitiveClassOverload" := rfl
example : label .pairFactorizationFails = "pairFactorizationFails" := rfl
example : label .pairRealizabilityFails = "pairRealizabilityFails" := rfl
example : label .pairSystemNoEarlyOutcome = "pairSystemNoEarlyOutcome" := rfl
example : label .pairIncrementFails = "pairIncrementFails" := rfl
example : label .pairIncrementNoEarlyOutcome = "pairIncrementNoEarlyOutcome" := rfl
example : label .pairCorrelation = "pairCorrelation" := rfl
example : label .pairCoverage = "pairCoverage" := rfl
example : label .pairFullModulus = "pairFullModulus" := rfl
example : label .pairUncrossing = "pairUncrossing" := rfl
-- SP keys
-- F1 keys
example : label .typeASupport = "typeASupport" := rfl
example : label .typeANoVisibleEntry = "typeANoVisibleEntry" := rfl
example : label .typeAExitFourAbsent = "typeAExitFourAbsent" := rfl
example : label .typeAExitSixProperScope = "typeAExitSixProperScope" := rfl
example : label .typeAExitSixGlobalScope = "typeAExitSixGlobalScope" := rfl
-- F3 keys
example : label .route8TwoCarrierExit = "route8TwoCarrierExit" := rfl
example : label .route8UnifiedTwoCarrierExit = "route8UnifiedTwoCarrierExit" := rfl
example : label .route8StageRate = "route8StageRate" := rfl
example : label .route8UnpaidTwoCarrier = "route8UnpaidTwoCarrier" := rfl
example : label .route8UnpaidWitnessFree = "route8UnpaidWitnessFree" := rfl
example : label .route8UnifiedEmptyAtG = "route8UnifiedEmptyAtG" := rfl
-- R8Q keys
example : label .route8QuotientEntriesAtG = "route8QuotientEntriesAtG" := rfl
example : label .typeBSublinearCanonicalForm = "typeBSublinearCanonicalForm" := rfl
example : label .groupedAbsorbedCoreSubset = "groupedAbsorbedCoreSubset" := rfl
example : label .typeBSublinearFailureArms = "typeBSublinearFailureArms" := rfl
example : label .groupedCentresHigh = "groupedCentresHigh" := rfl
example : label .handoffDegreeClauseEmpty = "handoffDegreeClauseEmpty" := rfl
example : label .pieceRoutingTotal = "pieceRoutingTotal" := rfl
example : label .coverPayment = "coverPayment" := rfl
example : label .loadFailureSaturated = "loadFailureSaturated" := rfl
example : label .unpaidAbsorbedWindowPort = "unpaidAbsorbedWindowPort" := rfl
example : label .receiverPortsAreWindowStubs = "receiverPortsAreWindowStubs" := rfl
example : label .saturatedReceiverBasin = "saturatedReceiverBasin" := rfl
example : label .loadFlowValue = "loadFlowValue" := rfl
example : label .coverFlowValue = "coverFlowValue" := rfl
example : label .pieceSizeProfile = "pieceSizeProfile" := rfl
example : label .typeAExitFourSwitchCycle = "typeAExitFourSwitchCycle" := rfl
example : label .typeAExitSevenSwitch = "typeAExitSevenSwitch" := rfl
-- F5 keys
example : label .coldNoPositiveGerm = "coldNoPositiveGerm" := rfl
-- SD keys (final pass)
example : label .degreeProfileFibres = "degreeProfileFibres" := rfl
example : label .targetCompleteContextUniversality = "targetCompleteContextUniversality" := rfl
example : label .hssTargetCycle = "hssTargetCycle" := rfl
-- SP keys (fix2)
example : label .pairResponseObstruction = "pairResponseObstruction" := rfl
example : label .pairNoResponseObstruction = "pairNoResponseObstruction" := rfl
example : label .pairDegreeProfileFibres = "pairDegreeProfileFibres" := rfl
example : label .pairProfileObstruction = "pairProfileObstruction" := rfl
example : label .pairNoProfileObstruction = "pairNoProfileObstruction" := rfl
example : label .sameTokenReadingsNotReplacement = "sameTokenReadingsNotReplacement" := rfl
example : label .twoSwitchForcedPath = "twoSwitchForcedPath" := rfl
example : label .highCentreSplitForced = "highCentreSplitForced" := rfl
example : label .crossSwitchFamily = "crossSwitchFamily" := rfl
example : label .sameVertexSwitchForcedPath = "sameVertexSwitchForcedPath" := rfl
example : label .sameTokenPatternSupports = "sameTokenPatternSupports" := rfl
example : label .sameTokenPatternSwap = "sameTokenPatternSwap" := rfl
example : label .sameTokenPairPartition = "sameTokenPairPartition" := rfl
example : label .coldCutStatesDistinct = "coldCutStatesDistinct" := rfl
example : label .coldRepeatedStateResidual = "coldRepeatedStateResidual" := rfl
example : label .coldHeavyEntryTerminal = "coldHeavyEntryTerminal" := rfl
example : label .entropyJointRealization = "entropyJointRealization" := rfl
example : label .allColdEntropyResidual = "allColdEntropyResidual" := rfl
example : label .realizedDensityOrder = "realizedDensityOrder" := rfl
example : label .realizedOrderLarge = "realizedOrderLarge" := rfl
example : label .realizedOrderSmall = "realizedOrderSmall" := rfl
example : label .boundedDensityOrder = "boundedDensityOrder" := rfl
example : label .route8RateFailsJoin = "route8RateFailsJoin" := rfl
example : label .route8RateFailsPiece = "route8RateFailsPiece" := rfl
example : label .route8RateFailsCrossBound = "route8RateFailsCrossBound" := rfl
example : label .route8RateFailsFlow = "route8RateFailsFlow" := rfl
example : label .route8CarrierInjection = "route8CarrierInjection" := rfl
example : label .route8RateExactSlack = "route8RateExactSlack" := rfl
example : label .route8StubDeficit = "route8StubDeficit" := rfl
example : label .route8DeficitVsStubs = "route8DeficitVsStubs" := rfl
example : label .route8EntryLowerBound = "route8EntryLowerBound" := rfl
example : label .route8CoreEmpty = "route8CoreEmpty" := rfl
example : label .route8StrongRate = "route8StrongRate" := rfl
example : label .route8ThinIsolation = "route8ThinIsolation" := rfl
example : label .route8WindowStub = "route8WindowStub" := rfl
example : label .route8ThinSmall = "route8ThinSmall" := rfl
example : label .route8WindowRPathGap = "route8WindowRPathGap" := rfl
example : label .route8HubStubs = "route8HubStubs" := rfl
example : label .route8WindowSelfRPathGap = "route8WindowSelfRPathGap" := rfl
example : label .route8PieceBoundary = "route8PieceBoundary" := rfl
example : label .route8WindowPieceRank = "route8WindowPieceRank" := rfl
example : label .route8AchievableLengths = "route8AchievableLengths" := rfl
example : label .boundedOrderLarge = "boundedOrderLarge" := rfl
example : label .boundedOrderSmall = "boundedOrderSmall" := rfl
example : label .edgeSurplusIdentity = "edgeSurplusIdentity" := rfl
example : label .surplusDartIdentity = "surplusDartIdentity" := rfl
example : label .highDegreeCountBound = "highDegreeCountBound" := rfl
example : label .highDegreePositive = "highDegreePositive" := rfl
example : label .highDegreeSurplusCapacity = "highDegreeSurplusCapacity" := rfl
example : label .packingOrderBound = "packingOrderBound" := rfl
example : label .ceilSqrtAboveScale = "ceilSqrtAboveScale" := rfl
example : label .orderAboveScaleSquare = "orderAboveScaleSquare" := rfl
example : label .sixVertexExtremalEnvelope = "sixVertexExtremalEnvelope" := rfl
example : label .noSuppressionChordViolation = "noSuppressionChordViolation" := rfl
example : label .admissibleQuotientsLabelInjective = "admissibleQuotientsLabelInjective" := rfl
example : label .singleBoundaryShape = "singleBoundaryShape" := rfl
example : label .remainderDeficiencyBelowCut = "remainderDeficiencyBelowCut" := rfl
example : label .windowCutCapacity = "windowCutCapacity" := rfl
example : label .canonicalCapacityExplicit = "canonicalCapacityExplicit" := rfl
example : label .primitiveCarrierCount = "primitiveCarrierCount" := rfl
example : label .canonicalTokenCount = "canonicalTokenCount" := rfl
example : label .canonicalBlockedFreePartition = "canonicalBlockedFreePartition" := rfl
example : label .canonicalLedgerDeficit = "canonicalLedgerDeficit" := rfl
example : label .pairCountDeficit = "pairCountDeficit" := rfl
example : label .canonicalCertificationCriterion = "canonicalCertificationCriterion" := rfl
example : label .paperBudgetBound = "paperBudgetBound" := rfl
example : label .paperBudgetCertifies = "paperBudgetCertifies" := rfl
example : label .canonicalOverloadOfFits = "canonicalOverloadOfFits" := rfl
example : label .canonicalFreeExcessOfCapped = "canonicalFreeExcessOfCapped" := rfl
example : label .pairCodeConfiguration = "pairCodeConfiguration" := rfl
example : label .specWitnessStructure = "specWitnessStructure" := rfl
example : label .everyWitnessSpectrumSplit = "everyWitnessSpectrumSplit" := rfl
example : label .highSurplusConfiguration = "highSurplusConfiguration" := rfl
example : label .highEndpointSwitch = "highEndpointSwitch" := rfl
example : label .neighbourhoodPairCount = "neighbourhoodPairCount" := rfl
example : label .starCycleConstraint = "starCycleConstraint" := rfl
example : label .meetingCycleConstraint = "meetingCycleConstraint" := rfl
example : label .highDegreePairSum = "highDegreePairSum" := rfl
example : label .vertexDeletionComponents = "vertexDeletionComponents" := rfl
example : label .cyclesThroughVertex = "cyclesThroughVertex" := rfl
example : label .cutVertexBlockPaths = "cutVertexBlockPaths" := rfl
example : label .cycleDoubleCount = "cycleDoubleCount" := rfl
example : label .threeRouteFan = "threeRouteFan" := rfl
example : label .threeRouteChain = "threeRouteChain" := rfl
example : label .windowPositionStubs = "windowPositionStubs" := rfl
example : label .windowAttachmentGap = "windowAttachmentGap" := rfl
example : label .cubicNeighbourSupply = "cubicNeighbourSupply" := rfl
example : label .hubCountBound = "hubCountBound" := rfl
example : label .lowEdgeParity = "lowEdgeParity" := rfl
example : label .bigHubBound = "bigHubBound" := rfl
example : label .bigHubVShapes = "bigHubVShapes" := rfl
example : label .highSurplusBound = "highSurplusBound" := rfl
example : label .hubLengthThreePairs = "hubLengthThreePairs" := rfl
example : label .densityExcess = "densityExcess" := rfl
example : label .remainderSlack = "remainderSlack" := rfl
example : label .hubWindowBudget = "hubWindowBudget" := rfl
example : label .windowHubBounds = "windowHubBounds" := rfl
example : label .remainderPathBounds = "remainderPathBounds" := rfl
example : label .windowFreeGeometry = "windowFreeGeometry" := rfl
example : label .inducedPathAttachment = "inducedPathAttachment" := rfl
example : label .highSurplusOrder = "highSurplusOrder" := rfl
example : label .windowChargeKinds = "windowChargeKinds" := rfl
example : label .responseObstructionTargetDefect = "responseObstructionTargetDefect" := rfl
example : label .hubLinkStructure = "hubLinkStructure" := rfl
example : label .hubClassCounts = "hubClassCounts" := rfl
example : label .slotRelation = "slotRelation" := rfl
example : label .closedClasses = "closedClasses" := rfl
example : label .hubTwoHopLinks = "hubTwoHopLinks" := rfl
example : label .slotLinear = "slotLinear" := rfl
example : label .scalePressure = "scalePressure" := rfl
example : label .freeSideStructure = "freeSideStructure" := rfl
example : label .freeSideCount = "freeSideCount" := rfl
example : label .freeSideHubs = "freeSideHubs" := rfl
example : label .extFreeEmpty = "extFreeEmpty" := rfl
example : label .extLoadSum = "extLoadSum" := rfl
example : label .extOverload = "extOverload" := rfl
example : label .extOverloadedToken = "extOverloadedToken" := rfl
example : label .newLoadBound = "newLoadBound" := rfl
example : label .separatedPairs = "separatedPairs" := rfl
example : label .portEndDegree = "portEndDegree" := rfl
example : label .pairArmAPattern = "pairArmAPattern" := rfl
example : label .pairArmARoleAlphabet = "pairArmARoleAlphabet" := rfl
example : label .pairArmB = "pairArmB" := rfl
example : label .sparseTargetDefectEmpty = "sparseTargetDefectEmpty" := rfl
example : label .sameTokenTransplantSize = "sameTokenTransplantSize" := rfl
example : label .sameTokenTransplantDeficit = "sameTokenTransplantDeficit" := rfl
example : label .sameTokenUnresolvedDecided = "sameTokenUnresolvedDecided" := rfl
example : label .sameTokenReadingsExact = "sameTokenReadingsExact" := rfl
example : label .sameTokenSwap = "sameTokenSwap" := rfl
example : label .sameTokenSwapExact = "sameTokenSwapExact" := rfl
example : label .sameTokenU2FreeWhole = "sameTokenU2FreeWhole" := rfl
example : label .blockedOwnRecord = "blockedOwnRecord" := rfl
example : label .blockedFailureSlack = "blockedFailureSlack" := rfl
example : label .blockedPrefixCompression = "blockedPrefixCompression" := rfl
example : label .blockedFailingSetCarries = "blockedFailingSetCarries" := rfl
example : label .blockedOverlapSupport = "blockedOverlapSupport" := rfl
example : label .pairHandoffSupport = "pairHandoffSupport" := rfl
example : label .pairHandoffCharge = "pairHandoffCharge" := rfl
example : label .pairHandoffNetCharge = "pairHandoffNetCharge" := rfl
example : label .pairHandoffHubCharge = "pairHandoffHubCharge" := rfl
example : label .pairHandoffBoundaryType = "pairHandoffBoundaryType" := rfl
example : label .pairHandoffCriticalCoordinate = "pairHandoffCriticalCoordinate" := rfl
example : label .pairObstructionDescent = "pairObstructionDescent" := rfl
example : label .pairHandoffHubForces = "pairHandoffHubForces" := rfl
example : label .pairHandoffDemandEnds = "pairHandoffDemandEnds" := rfl
example : label .pairHandoffHubBalance = "pairHandoffHubBalance" := rfl
example : label .pairHandoffFibreAtG = "pairHandoffFibreAtG" := rfl
example : label .stubDeficitIdentity = "stubDeficitIdentity" := rfl
example : label .remainderCycleSpectrum = "remainderCycleSpectrum" := rfl
example : label .sameTokenSeedCover = "sameTokenSeedCover" := rfl
example : label .sameTokenPathInteractions = "sameTokenPathInteractions" := rfl
example : label .typeAPeeledSaturatedReceiver = "typeAPeeledSaturatedReceiver" := rfl
example : label .typeAPeeledUnsaturatedDischarge = "typeAPeeledUnsaturatedDischarge" := rfl
example : label .typeAPeeledVisibleEntry = "typeAPeeledVisibleEntry" := rfl
example : label .typeAPeeledNoVisibleEntry = "typeAPeeledNoVisibleEntry" := rfl
example : label .typeAPeeledSilentExcess = "typeAPeeledSilentExcess" := rfl
example : label .typeAPeeledExitOneReturn = "typeAPeeledExitOneReturn" := rfl
example : label .typeAPeeledExitOneFree = "typeAPeeledExitOneFree" := rfl
example : label .typeAPeeledExitTwoTheta = "typeAPeeledExitTwoTheta" := rfl
example : label .typeAPeeledExitTwoFree = "typeAPeeledExitTwoFree" := rfl
example : label .typeAPeeledExitThreeCollision = "typeAPeeledExitThreeCollision" := rfl
example : label .typeAPeeledExitThreeFree = "typeAPeeledExitThreeFree" := rfl
example : label .typeAExitThreeCycle = "typeAExitThreeCycle" := rfl
example : label .typeAExitSevenEnvelope = "typeAExitSevenEnvelope" := rfl
example : label .coldAbsorbedNeutralConfiguration =
    "coldAbsorbedNeutralConfiguration" := rfl
example : label .coldSelectedFamilyEmpty = "coldSelectedFamilyEmpty" := rfl
example : label .coldMarkedGermUncompressed = "coldMarkedGermUncompressed" := rfl
example : label .coldMarkedGermStretchExcision = "coldMarkedGermStretchExcision" := rfl
end LabelPins

/-- The value schema at a residual: the object-level statement, read at the
residual's own object. -/
def Value (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key)
    (input : Core.Strategy.ProblemInput
      (problem BranchState Presentation presentation data.toParameters)) : Type :=
  PLift (Holds BranchState Presentation presentation data k input.object)

/-- The audit index of a key.  It is written out rather than taken from
`Key.ctorIdx` so that inserting or reordering a constructor cannot silently
renumber the audit names an earlier run emitted. -/
def idx : Key → Nat
  | .route8DemandUnitCount => 518
  | .route8OpenBoundarySaturated => 517
  | .windowShadowHitExcluded => 515
  | .windowShadowHitCycle => 514
  | .selection => 0
  | .cubicBaseline => 221
  | .minDegreeBaseline => 2850
  | .returnAvoidance => 1
  | .mersenneReturn => 606
  | .windowFree => 607
  | .windowPresent => 608
  | .noProperBaseline => 2
  | .tightEndpoint => 3
  | .slackIndependent => 4
  | .cycleRankConstraint => 425
  | .replacementExclusion => 223
  | .coldMassLinear => 224
  | .coldMassBounded => 225
  | .bridgeless => 226
  | .coldReturnCorridors => 227
  | .windowPackageRealized => 228
  | .windowPackageUnrealized => 229
  | .denseDeficiencyBelow => 230
  | .denseDeficiencyAtOrAbove => 231
  | .denseColdCorridorsTerminal => 403
  | .coldNeutralEqualLengthTerminal => 406
  | .coldWindowStubStructure => 232
  | .coldCanonicalNeutralConfiguration => 233
  | .coldGenuineSecondStrand => 234
  | .coldTwoStrandSurvivor => 410
  | .coldSymmetricPairExcluded => 411
  | .coldCanonicalSwapSmaller => 244
  | .coldCanonicalSwapSameSize => 245
  | .coldCanonicalReplacementSwap => 408
  | .coldCanonicalReplacementTrivial => 409
  | .blockedClassMember => 238
  | .blockedScaleAdditive => 320
  | .blockedCompressionBound => 423
  | .blockedCompressionCap => 424
  | .blockedBarrierOverlap => 321
  | .absorbedGermFanData => 235
  | .coldFamilyPositive => 236
  | .coldFamilyEmpty => 237
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
  | .barrierEnumeration => 211
  | .windowPackageSeparated => 35
  | .forcedCurvatureCost => 37
  | .remainderEntropyHigh => 38
  | .remainderEntropyLow => 39
  | .localTypeCoordinateRepetitive => 429
  | .localTypeCoordinateNonrepetitive => 430
  | .dominantRootedType => 431
  | .dominantRootedTypeWedgeFree => 432
  | .dominantRootedWedgeType => 428
  | .independentObstructionTranslates => 421
  | .entropyPackageDemand => 40
  | .entropyCapActive => 41
  | .entropyCapBound => 325
  | .largeBudgetResidual => 42
  | .netDeficiencyCap => 222
  | .exactCollisionFails => 146
  | .absorbedConfigurationResidual => 326
  | .absorbedGermSplit => 327
  | .netChargeCap => 145
  | .netChargeLocalization => 46
  | .netChargeNonNegative => 47
  | .netChargeNegative => 48
  | .negativeSupport => 50
  | .typeALowSurplus => 51
  | .typeABoundedSupport => 328
  | .typeBHighSurplus => 52
  | .typeBAssignedSupport => 250
  | .typeBFanEntry => 270
  | .typeBFanHeavyCentre => 251
  | .typeBFanDegreeFourCentres => 252
  | .sameCenterOpenPortCompatibility => 354
  | .typeBFanLocalDichotomy => 253
  | .typeBFanDegreeFourProfile => 254
  | .triangularFanCore => 355
  | .triangularShoulderCompletion => 426
  | .triangularPortReturn => 427
  | .triangularFirstLanding => 433
  | .triangularCrossShoulder => 434
  | .openPortSuppression => 435
  | .openPortSuppressionSafe => 436
  | .singleOpenPortSuppressionWitness => 437
  | .suppressedFamilyCriticalCycle => 438
  | .compatiblePairFanClosure => 443
  | .fanClosedPortTypeBRouting => 444
  | .compatiblePairTypeBRouting => 445
  | .triangularPortTypeBRouting => 446
  | .typeAReceiverRouting => 53
  | .typeASaturatedReceiver => 54
  | .typeAUnsaturatedReceivers => 55
  | .typeAUnsaturatedDischarge => 148
  | .typeAExclusion => 343
  | .typeBBridgeReduction => 344
  | .typeBSublinearLedger => 345
  | .typeBSublinearResidual => 346
  | .route8QuotientFree => 347
  | .route8QuotientResidual => 348
  | .route8DemandLedger => 349
  | .route8ExtractedEntryCensus => 350
  | .typeAPortReturn => 121
  | .typeAVisibleEntry => 56
  | .typeAVisibleFirstExcess => 57
  | .typeAExitOneReturn => 58
  | .typeAExitOneFree => 59
  | .typeAExitTwoTheta => 60
  | .typeAExitTwoFree => 61
  | .typeAExitThreeCollision => 62
  | .typeAExitThreeFree => 63
  | .typeASaturatedExitEntry => 123
  | .typeAExitSevenHandoff => 124
  | .typeBDecoratedAssignedSupport => 220
  | .typeAExitSevenFree => 125
  | .coldFailureCycle => 64
  | .coldFailureDefectRoute => 422
  | .coldFailureCompression => 66
  | .coldFailureRouting => 68
  | .coldFirstFailureOccurrence => 404
  | .coldExchangeBound => 177
  | .coldRoute8Below => 212
  | .coldRoute8AtOrAbove => 213
  | .coldHotEntropyOverflow => 214
  | .coldHotEntropyCap => 215
  | .coldMass => 216
  | .coldAmbientCubic => 217
  | .coldStubExcess => 218
  | .coldGermCandidates => 219
  | .coldGermFamilyPositive => 181
  | .coldSelectedBranchExcess => 179
  | .coldAmbientCubicStubExcess => 180
  | .coldPositiveGerm => 182
  | .coldHandoffTransfer => 69
  | .coldGermRouted => 71
  | .coldBranchClosed => 176
  | .coldGermSomeRealizing => 602
  | .coldGermNoneRealizing => 603
  | .coldGermSomeDistinguishing => 604
  | .coldGermNoneDistinguishing => 605
  | .highCentreNormalForm => 72
  | .fanCertificateCap => 76
  | .fanCertificateMarked => 77
  | .fanCertificateResidual => 78
  | .typeBHybridEntry => 80
  | .typeBDirectCycleFree => 82
  | .typeBB2Choice => 149
  | .typeBDisjointLedger => 150
  | .typeBOverlapObstruction => 84
  | .typeBGlobalLocalBridge => 447
  | .fanCertificateResidualMass => 186
  | .typeBOverlapObstructionMass => 187
  | .typeBAbsorbedHalfEdge => 2100
  | .typeBAbsorbedHalfEdgeAbsent => 2101
  | .absorbedHandoffCore => 3100
  | .absorbedHandoffCoreAbsent => 3101
  | .absorbedF4Charge => 3102
  | .typeBDegreeFourLedger => 2102
  | .typeBDegreeFourOverlap => 2103
  | .typeBDegreeFourClosed => 2104
  | .typeBAbsorbedCharge => 2800
  | .typeBRoute8Entry => 2801
  | .typeBBridgeMass => 85
  | .typeBBridgeSublinear => 189
  | .typeBExcluded => 166
  | .typeBExclusionResidual => 167
  | .typeAExitFourPeeled => 151
  | .typeAExitFourFiniteDescent => 153
  | .typeASaturatedHandoffExitFour => 156
  | .typeASaturatedHandoffExitFourFree => 157
  | .typeAExitFourReceiverDischarged => 152
  | .typeAExitFive => 96
  | .typeAExitFiveFree => 97
  | .typeAExitSix => 98
  | .typeAExitSixFree => 99
  | .typeAExitSixProper => 100
  | .typeAExitSixGlobal => 101
  | .route8ResidualProfile => 159
  | .route8BasinBurden => 161
  | .route8LargeBudgetDeficit => 162
  | .route8LargeBudgetDeficitFails => 329
  | .route8CarrierCore => 163
  | .route8TrueResidual => 332
  | .route8CarrierCutParity => 333
  | .route8SmallCoreEntry => 330
  | .route8NoSmallCoreEntry => 331
  | .route8SmallCoreCollapse => 168
  | .route8CarrierDeletionWitnesses => 170
  | .route8PrivateCarrierBudget => 171
  | .route8Census => 260
  | .route8Rate => 264
  | .route8RateFails => 265
  | .route8PiecesClassified => 266
  | .route8UnifiedNegative => 336
  | .route8UnifiedDeficit => 339
  | .route8UnifiedEntryCensus => 340
  | .route8StageRateFailed => 342
  | .route8DemandAbsorption => 351
  | .route8WindowBlockers => 352
  | .route8UnpaidExitFourResidual => 503
  | .route8UnifiedVisibleResidual => 504
  | .route8UnifiedVisibleOverload => 505
  | .route8JointBalance => 506
  | .route8TwoCarrierEntry => 261
  | .route8NoTwoCarrierEntry => 262
  | .route8TrueTwoCarrierEntry => 280
  | .route8PeelingDescent => 282
  | .route8UnifiedTrueTwoCarrierEntry => 334
  | .sparseSlackSurplus => 109
  | .activeSurplusFamily => 110
  | .sparsePortActivation => 111
  | .baselineSpineDemand => 112
  | .canonicalPairLedger => 113
  | .sparsePairExit => 143
  | .sparseTargetDefectResidual => 400
  | .canonicalBlockerRoute => 144
  | .sparseUpperEnvelope => 129
  | .capacityTokenLedger => 114
  | .roleFibrePartition => 115
  | .fibrePressure => 116
  | .spineSurplusEstimate => 126
  | .sparsePressureNearCubic => 127
  | .sparsePressureOverload => 128
  | .freePairEntropySandwich => 240
  | .freePairCodeUnrealized => 241
  | .blockedPairEntropySetup => 356
  | .blockedPairEntropySandwich => 242
  | .blockedPairCodeUnrealized => 243
  | .pairOverlapFirstFailure => 357
  | .pairOverlapSystem => 401
  | .pairConditionalFactorization => 412
  | .pairConditionalFactorizationResidual => 413
  | .pairFailureOverlap => 402
  | .pairDemandReturns => 405
  | .pairSystemRealizability => 414
  | .pairSystemEarlyOutcome => 415
  | .pairSerialDemandSystem => 416
  | .pairIncrementCovered => 417
  | .pairIncrementEarlyOutcome => 418
  | .pairSerialArithmetic => 419
  | .pairPowerOfTwoCycle => 420
  | .windowClassOverload => 130
  | .windowClassAbsent => 131
  | .remainderClassOverload => 132
  | .remainderClassAbsent => 133
  | .homogeneousCapsHold => 140
  | .homogeneousCapsFail => 601
  | .homogeneousBottleneckPattern => 141
  | .bottleneckRouting => 142
  | .typeBHandoff => 184
  | .typeBHandoffFails => 1801
  | .sameTokenPatternUnresolved => 1802
  | .homogeneousBottleneck => 118
  | .sparseSurplusSurvivor => 119
  | .activeSurplusDemands => 120
  | .hotColdPartition => 200
  | .dependentPairFamily => 201
  | .independentPairFamily => 202
  | .mixedSparseSpineDependence => 203
  | .exactCubicBaselineBudget => 204
  | .incrementalSkeletonRoom => 205
  | .skeletonDominates => 206
  | .exactResponseProfile => 207
  | .targetRankCircuit => 210
  -- F4 keys
  | .freePairCountFails => 1600
  | .blockedPairCountFails => 1601
  | .blockedPairNoExit => 1602
  | .primitiveClassOverload => 1603
  | .pairFactorizationFails => 1604
  | .pairRealizabilityFails => 1605
  | .pairSystemNoEarlyOutcome => 1606
  | .pairIncrementFails => 1607
  | .pairIncrementNoEarlyOutcome => 1608
  | .pairCorrelation => 8200
  | .pairCoverage => 8201
  | .pairFullModulus => 8202
  | .pairUncrossing => 8203
  -- SP keys
  -- F1 keys
  | .typeASupport => 1000
  | .typeANoVisibleEntry => 1001
  | .typeAExitFourAbsent => 1002
  | .typeAExitSixProperScope => 1004
  | .typeAExitSixGlobalScope => 1005
  -- F3 keys
  | .route8TwoCarrierExit => 1400
  | .route8UnifiedTwoCarrierExit => 1401
  | .route8StageRate => 1402
  | .route8UnpaidTwoCarrier => 1403
  | .route8UnpaidWitnessFree => 1404
  -- R3 keys
  | .route8UnifiedEmptyAtG => 7900
  -- R8Q keys
  | .route8QuotientEntriesAtG => 8150
  | .typeBSublinearCanonicalForm => 8300
  | .groupedAbsorbedCoreSubset => 8301
  | .typeBSublinearFailureArms => 8302
  | .groupedCentresHigh => 8303
  | .handoffDegreeClauseEmpty => 8304
  | .pieceRoutingTotal => 8305
  | .coverPayment => 8306
  | .loadFailureSaturated => 8307
  | .unpaidAbsorbedWindowPort => 8308
  | .receiverPortsAreWindowStubs => 8309
  | .saturatedReceiverBasin => 8310
  | .loadFlowValue => 8311
  | .coverFlowValue => 8312
  | .pieceSizeProfile => 8313
  -- R3b keys
  | .typeAExitFourSwitchCycle => 7960
  | .typeAExitSevenSwitch => 7961
  -- F5 keys
  | .coldNoPositiveGerm => 1800
  -- SD keys (final pass)
  | .degreeProfileFibres => 2300
  | .targetCompleteContextUniversality => 2301
  | .hssTargetCycle => 2303
  -- SP keys (fix2)
  | .pairResponseObstruction => 2900
  | .pairNoResponseObstruction => 2901
  | .pairDegreeProfileFibres => 2902
  | .pairProfileObstruction => 2903
  | .pairNoProfileObstruction => 2904
  | .sameTokenReadingsNotReplacement => 2905
  | .twoSwitchForcedPath => 6800
  | .highCentreSplitForced => 6801
  | .crossSwitchFamily => 6802
  | .sameVertexSwitchForcedPath => 6803
  | .sameTokenPatternSupports => 6804
  | .sameTokenPatternSwap => 6805
  | .sameTokenPairPartition => 6806
  | .coldCutStatesDistinct => 3200
  | .coldRepeatedStateResidual => 3201
  | .coldHeavyEntryTerminal => 3202
  | .entropyJointRealization => 3204
  | .allColdEntropyResidual => 3205
  -- C6 keys (density order)
  | .realizedDensityOrder => 6600
  | .realizedOrderLarge => 6601
  | .realizedOrderSmall => 6602
  | .boundedDensityOrder => 6603
  | .route8RateFailsJoin => 8250
  | .route8RateFailsPiece => 8251
  | .route8RateFailsCrossBound => 8252
  | .route8RateFailsFlow => 8253
  | .route8CarrierInjection => 8254
  | .route8RateExactSlack => 8255
  | .route8StubDeficit => 8256
  | .route8DeficitVsStubs => 8257
  | .route8EntryLowerBound => 8258
  | .route8CoreEmpty => 8259
  | .route8StrongRate => 8260
  | .route8ThinIsolation => 8261
  | .route8WindowStub => 8262
  | .route8ThinSmall => 8263
  | .route8WindowRPathGap => 8264
  | .route8HubStubs => 8265
  | .route8WindowSelfRPathGap => 8266
  | .route8PieceBoundary => 8267
  | .route8WindowPieceRank => 8268
  | .route8AchievableLengths => 8269
  | .boundedOrderLarge => 6604
  | .boundedOrderSmall => 6605
  -- [20a] enrichment keys
  | .edgeSurplusIdentity => 6606
  | .surplusDartIdentity => 6607
  | .highDegreeCountBound => 6608
  | .highDegreePositive => 6609
  | .highDegreeSurplusCapacity => 6610
  | .packingOrderBound => 6611
  | .ceilSqrtAboveScale => 6612
  | .orderAboveScaleSquare => 6613
  | .sixVertexExtremalEnvelope => 6614
  | .noSuppressionChordViolation => 6620
  | .admissibleQuotientsLabelInjective => 6626
  | .singleBoundaryShape => 6627
  | .remainderDeficiencyBelowCut => 6663
  | .windowCutCapacity => 6664
  | .canonicalCapacityExplicit => 6665
  | .primitiveCarrierCount => 6666
  | .canonicalTokenCount => 6667
  | .canonicalBlockedFreePartition => 6668
  | .canonicalLedgerDeficit => 6669
  | .pairCountDeficit => 6670
  | .canonicalCertificationCriterion => 6671
  | .paperBudgetBound => 6672
  | .paperBudgetCertifies => 6673
  | .canonicalOverloadOfFits => 6674
  | .canonicalFreeExcessOfCapped => 6675
  | .pairCodeConfiguration => 6676
  | .specWitnessStructure => 6677
  | .everyWitnessSpectrumSplit => 6702
  | .highSurplusConfiguration => 6703
  | .highEndpointSwitch => 6704
  -- port-cycles keys
  | .neighbourhoodPairCount => 6900
  | .starCycleConstraint => 6901
  | .meetingCycleConstraint => 6902
  | .highDegreePairSum => 6903
  | .vertexDeletionComponents => 6904
  | .cyclesThroughVertex => 6905
  | .cutVertexBlockPaths => 6906
  | .cycleDoubleCount => 6907
  -- port-local keys
  | .threeRouteFan => 7100
  | .threeRouteChain => 7101
  | .windowPositionStubs => 7102
  | .windowAttachmentGap => 7103
  -- port-joint keys
  | .cubicNeighbourSupply => 7200
  | .hubCountBound => 7201
  | .lowEdgeParity => 7202
  | .bigHubBound => 7203
  | .bigHubVShapes => 7204
  | .highSurplusBound => 7205
  | .hubLengthThreePairs => 7206
  | .densityExcess => 7207
  | .remainderSlack => 7208
  | .hubWindowBudget => 7209
  | .windowHubBounds => 7210
  | .remainderPathBounds => 7211
  | .windowFreeGeometry => 7212
  | .inducedPathAttachment => 7213
  | .highSurplusOrder => 7214
  | .windowChargeKinds => 7215
  | .responseObstructionTargetDefect => 7216
  | .hubLinkStructure => 7217
  | .hubClassCounts => 7218
  | .slotRelation => 7219
  | .closedClasses => 7220
  | .hubTwoHopLinks => 7221
  | .slotLinear => 7222
  | .scalePressure => 7223
  | .freeSideStructure => 7224
  | .freeSideCount => 7225
  | .freeSideHubs => 7226
  | .extFreeEmpty => 7227
  | .extLoadSum => 7228
  | .extOverload => 7229
  | .extOverloadedToken => 7230
  | .newLoadBound => 7231
  | .separatedPairs => 7232
  | .portEndDegree => 7233
  | .pairArmAPattern => 7234
  | .pairArmARoleAlphabet => 7235
  | .pairArmB => 7236
  | .sparseTargetDefectEmpty => 7800
  | .sameTokenTransplantSize => 8000
  | .sameTokenTransplantDeficit => 8001
  | .sameTokenUnresolvedDecided => 8100
  | .sameTokenReadingsExact => 8101
  | .sameTokenSwap => 8102
  | .sameTokenSwapExact => 8103
  | .sameTokenU2FreeWhole => 8104
  -- g-audit 172a keys
  | .blockedOwnRecord => 8600
  | .blockedFailureSlack => 8601
  | .blockedPrefixCompression => 8602
  | .blockedFailingSetCarries => 8603
  | .blockedOverlapSupport => 8604
  | .pairHandoffSupport => 8350
  | .pairHandoffCharge => 8351
  | .pairHandoffNetCharge => 8352
  | .pairHandoffHubCharge => 8353
  | .pairHandoffBoundaryType => 8354
  | .pairHandoffCriticalCoordinate => 8355
  | .pairObstructionDescent => 8356
  | .pairHandoffHubForces => 8357
  | .pairHandoffDemandEnds => 8358
  | .pairHandoffHubBalance => 8359
  | .pairHandoffFibreAtG => 8360
  | .stubDeficitIdentity => 8550
  | .remainderCycleSpectrum => 8551
  | .sameTokenSeedCover => 8105
  | .sameTokenPathInteractions => 8106
  -- TA keys
  | .typeAPeeledSaturatedReceiver => 2000
  | .typeAPeeledUnsaturatedDischarge => 2001
  | .typeAPeeledVisibleEntry => 2002
  | .typeAPeeledNoVisibleEntry => 2003
  | .typeAPeeledSilentExcess => 2004
  | .typeAPeeledExitOneReturn => 2005
  | .typeAPeeledExitOneFree => 2006
  | .typeAPeeledExitTwoTheta => 2007
  | .typeAPeeledExitTwoFree => 2008
  | .typeAPeeledExitThreeCollision => 2009
  | .typeAPeeledExitThreeFree => 2010
  | .typeAExitThreeCycle => 2011
  | .typeAExitSevenEnvelope => 2012
  | .coldAbsorbedNeutralConfiguration => 2700
  | .coldSelectedFamilyEmpty => 2701
  | .coldMarkedGermUncompressed => 8400
  | .coldMarkedGermStretchExcision => 8401

/-- Left inverse of `idx`.  Writing it out is also what checks the numbering:
two keys sharing an index would make `ofIdx_idx` unprovable. -/
def ofIdx : Nat → Key
  | 518 => .route8DemandUnitCount
  | 517 => .route8OpenBoundarySaturated
  | 515 => .windowShadowHitExcluded
  | 514 => .windowShadowHitCycle
  | 0 => .selection
  | 221 => .cubicBaseline
  | 2850 => .minDegreeBaseline
  | 1 => .returnAvoidance
  | 606 => .mersenneReturn
  | 607 => .windowFree
  | 608 => .windowPresent
  | 2 => .noProperBaseline
  | 3 => .tightEndpoint
  | 4 => .slackIndependent
  | 425 => .cycleRankConstraint
  | 223 => .replacementExclusion
  | 224 => .coldMassLinear
  | 225 => .coldMassBounded
  | 226 => .bridgeless
  | 227 => .coldReturnCorridors
  | 228 => .windowPackageRealized
  | 229 => .windowPackageUnrealized
  | 230 => .denseDeficiencyBelow
  | 231 => .denseDeficiencyAtOrAbove
  | 403 => .denseColdCorridorsTerminal
  | 406 => .coldNeutralEqualLengthTerminal
  | 232 => .coldWindowStubStructure
  | 233 => .coldCanonicalNeutralConfiguration
  | 234 => .coldGenuineSecondStrand
  | 410 => .coldTwoStrandSurvivor
  | 411 => .coldSymmetricPairExcluded
  | 244 => .coldCanonicalSwapSmaller
  | 245 => .coldCanonicalSwapSameSize
  | 408 => .coldCanonicalReplacementSwap
  | 409 => .coldCanonicalReplacementTrivial
  | 238 => .blockedClassMember
  | 320 => .blockedScaleAdditive
  | 423 => .blockedCompressionBound
  | 424 => .blockedCompressionCap
  | 321 => .blockedBarrierOverlap
  | 235 => .absorbedGermFanData
  | 236 => .coldFamilyPositive
  | 237 => .coldFamilyEmpty
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
  | 37 => .forcedCurvatureCost
  | 38 => .remainderEntropyHigh
  | 39 => .remainderEntropyLow
  | 429 => .localTypeCoordinateRepetitive
  | 430 => .localTypeCoordinateNonrepetitive
  | 431 => .dominantRootedType
  | 432 => .dominantRootedTypeWedgeFree
  | 428 => .dominantRootedWedgeType
  | 421 => .independentObstructionTranslates
  | 40 => .entropyPackageDemand
  | 41 => .entropyCapActive
  | 325 => .entropyCapBound
  | 42 => .largeBudgetResidual
  | 222 => .netDeficiencyCap
  | 146 => .exactCollisionFails
  | 326 => .absorbedConfigurationResidual
  | 327 => .absorbedGermSplit
  | 145 => .netChargeCap
  | 46 => .netChargeLocalization
  | 47 => .netChargeNonNegative
  | 48 => .netChargeNegative
  | 50 => .negativeSupport
  | 51 => .typeALowSurplus
  | 328 => .typeABoundedSupport
  | 52 => .typeBHighSurplus
  | 250 => .typeBAssignedSupport
  | 270 => .typeBFanEntry
  | 251 => .typeBFanHeavyCentre
  | 252 => .typeBFanDegreeFourCentres
  | 354 => .sameCenterOpenPortCompatibility
  | 253 => .typeBFanLocalDichotomy
  | 254 => .typeBFanDegreeFourProfile
  | 355 => .triangularFanCore
  | 426 => .triangularShoulderCompletion
  | 427 => .triangularPortReturn
  | 433 => .triangularFirstLanding
  | 434 => .triangularCrossShoulder
  | 435 => .openPortSuppression
  | 436 => .openPortSuppressionSafe
  | 437 => .singleOpenPortSuppressionWitness
  | 438 => .suppressedFamilyCriticalCycle
  | 443 => .compatiblePairFanClosure
  | 444 => .fanClosedPortTypeBRouting
  | 445 => .compatiblePairTypeBRouting
  | 446 => .triangularPortTypeBRouting
  | 53 => .typeAReceiverRouting
  | 54 => .typeASaturatedReceiver
  | 55 => .typeAUnsaturatedReceivers
  | 148 => .typeAUnsaturatedDischarge
  | 343 => .typeAExclusion
  | 344 => .typeBBridgeReduction
  | 345 => .typeBSublinearLedger
  | 346 => .typeBSublinearResidual
  | 347 => .route8QuotientFree
  | 348 => .route8QuotientResidual
  | 349 => .route8DemandLedger
  | 350 => .route8ExtractedEntryCensus
  | 56 => .typeAVisibleEntry
  | 57 => .typeAVisibleFirstExcess
  | 58 => .typeAExitOneReturn
  | 59 => .typeAExitOneFree
  | 60 => .typeAExitTwoTheta
  | 61 => .typeAExitTwoFree
  | 62 => .typeAExitThreeCollision
  | 63 => .typeAExitThreeFree
  | 64 => .coldFailureCycle
  | 422 => .coldFailureDefectRoute
  | 66 => .coldFailureCompression
  | 68 => .coldFailureRouting
  | 404 => .coldFirstFailureOccurrence
  | 177 => .coldExchangeBound
  | 212 => .coldRoute8Below
  | 213 => .coldRoute8AtOrAbove
  | 214 => .coldHotEntropyOverflow
  | 215 => .coldHotEntropyCap
  | 216 => .coldMass
  | 217 => .coldAmbientCubic
  | 218 => .coldStubExcess
  | 219 => .coldGermCandidates
  | 181 => .coldGermFamilyPositive
  | 179 => .coldSelectedBranchExcess
  | 180 => .coldAmbientCubicStubExcess
  | 182 => .coldPositiveGerm
  | 69 => .coldHandoffTransfer
  | 71 => .coldGermRouted
  | 176 => .coldBranchClosed
  | 602 => .coldGermSomeRealizing
  | 603 => .coldGermNoneRealizing
  | 604 => .coldGermSomeDistinguishing
  | 605 => .coldGermNoneDistinguishing
  | 72 => .highCentreNormalForm
  | 76 => .fanCertificateCap
  | 77 => .fanCertificateMarked
  | 78 => .fanCertificateResidual
  | 80 => .typeBHybridEntry
  | 82 => .typeBDirectCycleFree
  | 149 => .typeBB2Choice
  | 150 => .typeBDisjointLedger
  | 84 => .typeBOverlapObstruction
  | 447 => .typeBGlobalLocalBridge
  | 186 => .fanCertificateResidualMass
  | 187 => .typeBOverlapObstructionMass
  | 2100 => .typeBAbsorbedHalfEdge
  | 2101 => .typeBAbsorbedHalfEdgeAbsent
  | 3100 => .absorbedHandoffCore
  | 3101 => .absorbedHandoffCoreAbsent
  | 3102 => .absorbedF4Charge
  | 2102 => .typeBDegreeFourLedger
  | 2103 => .typeBDegreeFourOverlap
  | 2104 => .typeBDegreeFourClosed
  | 2800 => .typeBAbsorbedCharge
  | 2801 => .typeBRoute8Entry
  | 85 => .typeBBridgeMass
  | 189 => .typeBBridgeSublinear
  | 166 => .typeBExcluded
  | 167 => .typeBExclusionResidual
  | 151 => .typeAExitFourPeeled
  | 153 => .typeAExitFourFiniteDescent
  | 156 => .typeASaturatedHandoffExitFour
  | 157 => .typeASaturatedHandoffExitFourFree
  | 152 => .typeAExitFourReceiverDischarged
  | 96 => .typeAExitFive
  | 97 => .typeAExitFiveFree
  | 98 => .typeAExitSix
  | 99 => .typeAExitSixFree
  | 100 => .typeAExitSixProper
  | 101 => .typeAExitSixGlobal
  | 159 => .route8ResidualProfile
  | 161 => .route8BasinBurden
  | 162 => .route8LargeBudgetDeficit
  | 329 => .route8LargeBudgetDeficitFails
  | 163 => .route8CarrierCore
  | 332 => .route8TrueResidual
  | 333 => .route8CarrierCutParity
  | 330 => .route8SmallCoreEntry
  | 331 => .route8NoSmallCoreEntry
  | 168 => .route8SmallCoreCollapse
  | 170 => .route8CarrierDeletionWitnesses
  | 171 => .route8PrivateCarrierBudget
  | 260 => .route8Census
  | 264 => .route8Rate
  | 265 => .route8RateFails
  | 266 => .route8PiecesClassified
  | 336 => .route8UnifiedNegative
  | 339 => .route8UnifiedDeficit
  | 340 => .route8UnifiedEntryCensus
  | 342 => .route8StageRateFailed
  | 351 => .route8DemandAbsorption
  | 352 => .route8WindowBlockers
  | 503 => .route8UnpaidExitFourResidual
  | 504 => .route8UnifiedVisibleResidual
  | 505 => .route8UnifiedVisibleOverload
  | 506 => .route8JointBalance
  | 261 => .route8TwoCarrierEntry
  | 262 => .route8NoTwoCarrierEntry
  | 280 => .route8TrueTwoCarrierEntry
  | 282 => .route8PeelingDescent
  | 334 => .route8UnifiedTrueTwoCarrierEntry
  | 109 => .sparseSlackSurplus
  | 110 => .activeSurplusFamily
  | 111 => .sparsePortActivation
  | 112 => .baselineSpineDemand
  | 113 => .canonicalPairLedger
  | 143 => .sparsePairExit
  | 400 => .sparseTargetDefectResidual
  | 144 => .canonicalBlockerRoute
  | 129 => .sparseUpperEnvelope
  | 114 => .capacityTokenLedger
  | 115 => .roleFibrePartition
  | 116 => .fibrePressure
  | 130 => .windowClassOverload
  | 131 => .windowClassAbsent
  | 132 => .remainderClassOverload
  | 133 => .remainderClassAbsent
  | 140 => .homogeneousCapsHold
  | 601 => .homogeneousCapsFail
  | 141 => .homogeneousBottleneckPattern
  | 142 => .bottleneckRouting
  | 184 => .typeBHandoff
  | 1801 => .typeBHandoffFails
  | 1802 => .sameTokenPatternUnresolved
  | 118 => .homogeneousBottleneck
  | 119 => .sparseSurplusSurvivor
  | 120 => .activeSurplusDemands
  | 121 => .typeAPortReturn
  | 123 => .typeASaturatedExitEntry
  | 124 => .typeAExitSevenHandoff
  | 220 => .typeBDecoratedAssignedSupport
  | 125 => .typeAExitSevenFree
  | 126 => .spineSurplusEstimate
  | 127 => .sparsePressureNearCubic
  | 128 => .sparsePressureOverload
  | 240 => .freePairEntropySandwich
  | 241 => .freePairCodeUnrealized
  | 356 => .blockedPairEntropySetup
  | 242 => .blockedPairEntropySandwich
  | 243 => .blockedPairCodeUnrealized
  | 357 => .pairOverlapFirstFailure
  | 401 => .pairOverlapSystem
  | 412 => .pairConditionalFactorization
  | 413 => .pairConditionalFactorizationResidual
  | 402 => .pairFailureOverlap
  | 405 => .pairDemandReturns
  | 414 => .pairSystemRealizability
  | 415 => .pairSystemEarlyOutcome
  | 416 => .pairSerialDemandSystem
  | 417 => .pairIncrementCovered
  | 418 => .pairIncrementEarlyOutcome
  | 419 => .pairSerialArithmetic
  | 420 => .pairPowerOfTwoCycle
  | 200 => .hotColdPartition
  | 201 => .dependentPairFamily
  | 202 => .independentPairFamily
  | 203 => .mixedSparseSpineDependence
  | 204 => .exactCubicBaselineBudget
  | 205 => .incrementalSkeletonRoom
  | 206 => .skeletonDominates
  | 207 => .exactResponseProfile
  | 210 => .targetRankCircuit
  | 211 => .barrierEnumeration
  -- F4 keys
  | 1600 => .freePairCountFails
  | 1601 => .blockedPairCountFails
  | 1602 => .blockedPairNoExit
  | 1603 => .primitiveClassOverload
  | 1604 => .pairFactorizationFails
  | 1605 => .pairRealizabilityFails
  | 1606 => .pairSystemNoEarlyOutcome
  | 1607 => .pairIncrementFails
  | 1608 => .pairIncrementNoEarlyOutcome
  | 8200 => .pairCorrelation
  | 8201 => .pairCoverage
  | 8202 => .pairFullModulus
  | 8203 => .pairUncrossing
  -- SP keys
  -- F1 keys
  | 1000 => .typeASupport
  | 1001 => .typeANoVisibleEntry
  | 1002 => .typeAExitFourAbsent
  | 1004 => .typeAExitSixProperScope
  | 1005 => .typeAExitSixGlobalScope
  -- F3 keys
  | 1400 => .route8TwoCarrierExit
  | 1401 => .route8UnifiedTwoCarrierExit
  | 1402 => .route8StageRate
  | 1403 => .route8UnpaidTwoCarrier
  | 1404 => .route8UnpaidWitnessFree
  -- R3 keys
  | 7900 => .route8UnifiedEmptyAtG
  -- R8Q keys
  | 8150 => .route8QuotientEntriesAtG
  | 8300 => .typeBSublinearCanonicalForm
  | 8301 => .groupedAbsorbedCoreSubset
  | 8302 => .typeBSublinearFailureArms
  | 8303 => .groupedCentresHigh
  | 8304 => .handoffDegreeClauseEmpty
  | 8305 => .pieceRoutingTotal
  | 8306 => .coverPayment
  | 8307 => .loadFailureSaturated
  | 8308 => .unpaidAbsorbedWindowPort
  | 8309 => .receiverPortsAreWindowStubs
  | 8310 => .saturatedReceiverBasin
  | 8311 => .loadFlowValue
  | 8312 => .coverFlowValue
  | 8313 => .pieceSizeProfile
  -- R3b keys
  | 7960 => .typeAExitFourSwitchCycle
  | 7961 => .typeAExitSevenSwitch
  -- F5 keys
  | 1800 => .coldNoPositiveGerm
  -- SD keys (final pass)
  | 2300 => .degreeProfileFibres
  | 2301 => .targetCompleteContextUniversality
  | 2303 => .hssTargetCycle
  -- SP keys (fix2)
  | 2900 => .pairResponseObstruction
  | 2901 => .pairNoResponseObstruction
  | 2902 => .pairDegreeProfileFibres
  | 2903 => .pairProfileObstruction
  | 2904 => .pairNoProfileObstruction
  | 2905 => .sameTokenReadingsNotReplacement
  | 6800 => .twoSwitchForcedPath
  | 6801 => .highCentreSplitForced
  | 6802 => .crossSwitchFamily
  | 6803 => .sameVertexSwitchForcedPath
  | 6804 => .sameTokenPatternSupports
  | 6805 => .sameTokenPatternSwap
  | 6806 => .sameTokenPairPartition
  | 3200 => .coldCutStatesDistinct
  | 3201 => .coldRepeatedStateResidual
  | 3202 => .coldHeavyEntryTerminal
  | 3204 => .entropyJointRealization
  | 3205 => .allColdEntropyResidual
  -- C6 keys (density order)
  | 6600 => .realizedDensityOrder
  | 6601 => .realizedOrderLarge
  | 6602 => .realizedOrderSmall
  | 6603 => .boundedDensityOrder
  | 8250 => .route8RateFailsJoin
  | 8251 => .route8RateFailsPiece
  | 8252 => .route8RateFailsCrossBound
  | 8253 => .route8RateFailsFlow
  | 8254 => .route8CarrierInjection
  | 8255 => .route8RateExactSlack
  | 8256 => .route8StubDeficit
  | 8257 => .route8DeficitVsStubs
  | 8258 => .route8EntryLowerBound
  | 8259 => .route8CoreEmpty
  | 8260 => .route8StrongRate
  | 8261 => .route8ThinIsolation
  | 8262 => .route8WindowStub
  | 8263 => .route8ThinSmall
  | 8264 => .route8WindowRPathGap
  | 8265 => .route8HubStubs
  | 8266 => .route8WindowSelfRPathGap
  | 8267 => .route8PieceBoundary
  | 8268 => .route8WindowPieceRank
  | 8269 => .route8AchievableLengths
  | 6604 => .boundedOrderLarge
  | 6605 => .boundedOrderSmall
  -- [20a] enrichment keys
  | 6606 => .edgeSurplusIdentity
  | 6607 => .surplusDartIdentity
  | 6608 => .highDegreeCountBound
  | 6609 => .highDegreePositive
  | 6610 => .highDegreeSurplusCapacity
  | 6611 => .packingOrderBound
  | 6612 => .ceilSqrtAboveScale
  | 6613 => .orderAboveScaleSquare
  | 6614 => .sixVertexExtremalEnvelope
  | 6620 => .noSuppressionChordViolation
  | 6626 => .admissibleQuotientsLabelInjective
  | 6627 => .singleBoundaryShape
  | 6663 => .remainderDeficiencyBelowCut
  | 6664 => .windowCutCapacity
  | 6665 => .canonicalCapacityExplicit
  | 6666 => .primitiveCarrierCount
  | 6667 => .canonicalTokenCount
  | 6668 => .canonicalBlockedFreePartition
  | 6669 => .canonicalLedgerDeficit
  | 6670 => .pairCountDeficit
  | 6671 => .canonicalCertificationCriterion
  | 6672 => .paperBudgetBound
  | 6673 => .paperBudgetCertifies
  | 6674 => .canonicalOverloadOfFits
  | 6675 => .canonicalFreeExcessOfCapped
  | 6676 => .pairCodeConfiguration
  | 6677 => .specWitnessStructure
  | 6702 => .everyWitnessSpectrumSplit
  | 6703 => .highSurplusConfiguration
  | 6704 => .highEndpointSwitch
  -- port-cycles keys
  | 6900 => .neighbourhoodPairCount
  | 6901 => .starCycleConstraint
  | 6902 => .meetingCycleConstraint
  | 6903 => .highDegreePairSum
  | 6904 => .vertexDeletionComponents
  | 6905 => .cyclesThroughVertex
  | 6906 => .cutVertexBlockPaths
  | 6907 => .cycleDoubleCount
  -- port-local keys
  | 7100 => .threeRouteFan
  | 7101 => .threeRouteChain
  | 7102 => .windowPositionStubs
  | 7103 => .windowAttachmentGap
  -- port-joint keys
  | 7200 => .cubicNeighbourSupply
  | 7201 => .hubCountBound
  | 7202 => .lowEdgeParity
  | 7203 => .bigHubBound
  | 7204 => .bigHubVShapes
  | 7205 => .highSurplusBound
  | 7206 => .hubLengthThreePairs
  | 7207 => .densityExcess
  | 7208 => .remainderSlack
  | 7209 => .hubWindowBudget
  | 7210 => .windowHubBounds
  | 7211 => .remainderPathBounds
  | 7212 => .windowFreeGeometry
  | 7213 => .inducedPathAttachment
  | 7214 => .highSurplusOrder
  | 7215 => .windowChargeKinds
  | 7216 => .responseObstructionTargetDefect
  | 7217 => .hubLinkStructure
  | 7218 => .hubClassCounts
  | 7219 => .slotRelation
  | 7220 => .closedClasses
  | 7221 => .hubTwoHopLinks
  | 7222 => .slotLinear
  | 7223 => .scalePressure
  | 7224 => .freeSideStructure
  | 7225 => .freeSideCount
  | 7226 => .freeSideHubs
  | 7227 => .extFreeEmpty
  | 7228 => .extLoadSum
  | 7229 => .extOverload
  | 7230 => .extOverloadedToken
  | 7231 => .newLoadBound
  | 7232 => .separatedPairs
  | 7233 => .portEndDegree
  | 7234 => .pairArmAPattern
  | 7235 => .pairArmARoleAlphabet
  | 7236 => .pairArmB
  | 7800 => .sparseTargetDefectEmpty
  | 8000 => .sameTokenTransplantSize
  | 8001 => .sameTokenTransplantDeficit
  | 8100 => .sameTokenUnresolvedDecided
  | 8101 => .sameTokenReadingsExact
  | 8102 => .sameTokenSwap
  | 8103 => .sameTokenSwapExact
  | 8104 => .sameTokenU2FreeWhole
  -- g-audit 172a keys
  | 8600 => .blockedOwnRecord
  | 8601 => .blockedFailureSlack
  | 8602 => .blockedPrefixCompression
  | 8603 => .blockedFailingSetCarries
  | 8604 => .blockedOverlapSupport
  | 8350 => .pairHandoffSupport
  | 8351 => .pairHandoffCharge
  | 8352 => .pairHandoffNetCharge
  | 8353 => .pairHandoffHubCharge
  | 8354 => .pairHandoffBoundaryType
  | 8355 => .pairHandoffCriticalCoordinate
  | 8356 => .pairObstructionDescent
  | 8357 => .pairHandoffHubForces
  | 8358 => .pairHandoffDemandEnds
  | 8359 => .pairHandoffHubBalance
  | 8360 => .pairHandoffFibreAtG
  | 8550 => .stubDeficitIdentity
  | 8551 => .remainderCycleSpectrum
  | 8105 => .sameTokenSeedCover
  | 8106 => .sameTokenPathInteractions
  -- TA keys
  | 2000 => .typeAPeeledSaturatedReceiver
  | 2001 => .typeAPeeledUnsaturatedDischarge
  | 2002 => .typeAPeeledVisibleEntry
  | 2003 => .typeAPeeledNoVisibleEntry
  | 2004 => .typeAPeeledSilentExcess
  | 2005 => .typeAPeeledExitOneReturn
  | 2006 => .typeAPeeledExitOneFree
  | 2007 => .typeAPeeledExitTwoTheta
  | 2008 => .typeAPeeledExitTwoFree
  | 2009 => .typeAPeeledExitThreeCollision
  | 2010 => .typeAPeeledExitThreeFree
  | 2011 => .typeAExitThreeCycle
  | 2012 => .typeAExitSevenEnvelope
  | 2700 => .coldAbsorbedNeutralConfiguration
  | 2701 => .coldSelectedFamilyEmpty
  | 8400 => .coldMarkedGermUncompressed
  | 8401 => .coldMarkedGermStretchExcision
  | _ => .selection

set_option maxRecDepth 8192 in
theorem ofIdx_idx (k : Key) : ofIdx (idx k) = k := by
  cases k <;> rfl

theorem idx_injective : Function.Injective idx :=
  Function.LeftInverse.injective ofIdx_idx

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys.  The name carries the key's audit index as its final
component, so distinctness is inherited from `idx_injective` instead of being
re-derived by a pairwise comparison of the audit labels. -/
def name : Key → Lean.Name
  | .route8DemandUnitCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8DemandUnitCount") 518
  | .route8OpenBoundarySaturated =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8OpenBoundarySaturated") 517
  | .windowShadowHitExcluded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowShadowHitExcluded") 515
  | .windowShadowHitCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowShadowHitCycle") 514
  | .selection => .num (.str `Hypostructure.Graph.Strategy.Spine "selection") 0
  | .cubicBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cubicBaseline") 221
  | .minDegreeBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "minDegreeBaseline") 2850
  | .returnAvoidance =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "returnAvoidance") 1
  | .mersenneReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "mersenneReturn") 606
  | .windowFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowFree") 607
  | .windowPresent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowPresent") 608
  | .noProperBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "noProperBaseline") 2
  | .tightEndpoint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "tightEndpoint") 3
  | .slackIndependent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "slackIndependent") 4
  | .cycleRankConstraint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "cycleRankConstraint") 425
  | .replacementExclusion =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "replacementExclusion") 223
  | .coldMassLinear =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldMassLinear") 224
  | .coldMassBounded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldMassBounded") 225
  | .bridgeless =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "bridgeless") 226
  | .coldReturnCorridors =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldReturnCorridors") 227
  | .windowPackageRealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowPackageRealized") 228
  | .windowPackageUnrealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowPackageUnrealized") 229
  | .denseDeficiencyBelow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "denseDeficiencyBelow") 230
  | .denseDeficiencyAtOrAbove =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "denseDeficiencyAtOrAbove") 231
  | .denseColdCorridorsTerminal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "denseColdCorridorsTerminal") 403
  | .coldNeutralEqualLengthTerminal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldNeutralEqualLengthTerminal") 406
  | .coldWindowStubStructure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldWindowStubStructure") 232
  | .coldCanonicalNeutralConfiguration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldCanonicalNeutralConfiguration") 233
  | .coldGenuineSecondStrand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGenuineSecondStrand") 234
  | .coldTwoStrandSurvivor =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldTwoStrandSurvivor") 410
  | .coldSymmetricPairExcluded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldSymmetricPairExcluded") 411
  | .coldCanonicalSwapSmaller =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCanonicalSwapSmaller") 244
  | .coldCanonicalSwapSameSize =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCanonicalSwapSameSize") 245
  | .coldCanonicalReplacementSwap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldCanonicalReplacementSwap") 408
  | .coldCanonicalReplacementTrivial =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldCanonicalReplacementTrivial") 409
  | .blockedClassMember =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedClassMember") 238
  | .blockedScaleAdditive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedScaleAdditive") 320
  | .blockedCompressionBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedCompressionBound") 423
  | .blockedCompressionCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedCompressionCap") 424
  | .blockedBarrierOverlap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedBarrierOverlap") 321
  | .absorbedGermFanData =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "absorbedGermFanData") 235
  | .coldFamilyPositive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFamilyPositive") 236
  | .coldFamilyEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFamilyEmpty") 237
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
  | .barrierEnumeration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "barrierEnumeration") 211
  | .windowPackageSeparated =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "windowPackageSeparated") 35
  | .forcedCurvatureCost =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "forcedCurvatureCost") 37
  | .remainderEntropyHigh =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderEntropyHigh") 38
  | .remainderEntropyLow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderEntropyLow") 39
  | .localTypeCoordinateRepetitive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "localTypeCoordinateRepetitive") 429
  | .localTypeCoordinateNonrepetitive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "localTypeCoordinateNonrepetitive") 430
  | .dominantRootedType =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "dominantRootedType") 431
  | .dominantRootedTypeWedgeFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "dominantRootedTypeWedgeFree") 432
  | .dominantRootedWedgeType =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "dominantRootedWedgeType") 428
  | .independentObstructionTranslates =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "independentObstructionTranslates") 421
  | .entropyPackageDemand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyPackageDemand") 40
  | .entropyCapActive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyCapActive") 41
  | .entropyCapBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyCapBound") 325
  | .largeBudgetResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "largeBudgetResidual") 42
  | .netDeficiencyCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netDeficiencyCap") 222
  | .exactCollisionFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "exactCollisionFails") 146
  | .absorbedConfigurationResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "absorbedConfigurationResidual") 326
  | .absorbedGermSplit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "absorbedGermSplit") 327
  | .netChargeCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeCap") 145
  | .netChargeLocalization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeLocalization") 46
  | .netChargeNonNegative =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeNonNegative") 47
  | .netChargeNegative =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeNegative") 48
  | .negativeSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "negativeSupport") 50
  | .typeALowSurplus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeALowSurplus") 51
  | .typeABoundedSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeABoundedSupport") 328
  | .typeBHighSurplus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHighSurplus") 52
  | .typeBAssignedSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBAssignedSupport") 250
  | .typeBFanEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanEntry") 270
  | .typeBFanHeavyCentre =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanHeavyCentre") 251
  | .typeBFanDegreeFourCentres =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanDegreeFourCentres") 252
  | .sameCenterOpenPortCompatibility =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sameCenterOpenPortCompatibility") 354
  | .typeBFanLocalDichotomy =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanLocalDichotomy") 253
  | .typeBFanDegreeFourProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanDegreeFourProfile") 254
  | .triangularFanCore =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "triangularFanCore") 355
  | .triangularShoulderCompletion =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "triangularShoulderCompletion") 426
  | .triangularPortReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "triangularPortReturn") 427
  | .triangularFirstLanding =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "triangularFirstLanding") 433
  | .triangularCrossShoulder =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "triangularCrossShoulder") 434
  | .openPortSuppression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "openPortSuppression") 435
  | .openPortSuppressionSafe =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "openPortSuppressionSafe") 436
  | .singleOpenPortSuppressionWitness =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "singleOpenPortSuppressionWitness") 437
  | .suppressedFamilyCriticalCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "suppressedFamilyCriticalCycle") 438
  | .compatiblePairFanClosure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "compatiblePairFanClosure") 443
  | .fanClosedPortTypeBRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "fanClosedPortTypeBRouting") 444
  | .compatiblePairTypeBRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "compatiblePairTypeBRouting") 445
  | .triangularPortTypeBRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "triangularPortTypeBRouting") 446
  | .typeAReceiverRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAReceiverRouting") 53
  | .typeASaturatedReceiver =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedReceiver") 54
  | .typeAUnsaturatedReceivers =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAUnsaturatedReceivers") 55
  | .typeAUnsaturatedDischarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAUnsaturatedDischarge") 148
  | .typeAExclusion =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExclusion") 343
  | .typeBBridgeReduction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBBridgeReduction") 344
  | .typeBSublinearLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBSublinearLedger") 345
  | .typeBSublinearResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBSublinearResidual") 346
  | .route8QuotientFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8QuotientFree") 347
  | .route8QuotientResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8QuotientResidual") 348
  | .route8DemandLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8DemandLedger") 349
  | .route8ExtractedEntryCensus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8ExtractedEntryCensus") 350
  | .typeAPortReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPortReturn") 121
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
  | .typeASaturatedExitEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedExitEntry") 123
  | .typeAExitSevenHandoff =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitSevenHandoff") 124
  | .typeBDecoratedAssignedSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDecoratedAssignedSupport") 220
  | .typeAExitSevenFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSevenFree") 125
  | .coldFailureCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureCycle") 64
  | .coldFailureDefectRoute =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldFailureDefectRoute") 422
  | .coldFailureCompression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldFailureCompression") 66
  | .coldFailureRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldFailureRouting") 68
  | .coldFirstFailureOccurrence =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldFirstFailureOccurrence") 404
  | .coldExchangeBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldExchangeBound") 177
  | .coldRoute8Below =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldRoute8Below") 212
  | .coldRoute8AtOrAbove =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldRoute8AtOrAbove") 213
  | .coldHotEntropyOverflow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldHotEntropyOverflow") 214
  | .coldHotEntropyCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldHotEntropyCap") 215
  | .coldMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldMass") 216
  | .coldAmbientCubic =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldAmbientCubic") 217
  | .coldStubExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldStubExcess") 218
  | .coldGermCandidates =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermCandidates") 219
  | .coldGermFamilyPositive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldGermFamilyPositive") 181
  | .coldSelectedBranchExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldSelectedBranchExcess") 179
  | .coldAmbientCubicStubExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldAmbientCubicStubExcess") 180
  | .coldHandoffTransfer =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldHandoffTransfer") 69
  | .coldPositiveGerm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldPositiveGerm") 182
  | .coldGermRouted =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermRouted") 71
  | .coldBranchClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldBranchClosed") 176
  | .coldGermSomeRealizing =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermSomeRealizing") 602
  | .coldGermNoneRealizing =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermNoneRealizing") 603
  | .coldGermSomeDistinguishing =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermSomeDistinguishing") 604
  | .coldGermNoneDistinguishing =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermNoneDistinguishing") 605
  | .highCentreNormalForm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highCentreNormalForm") 72
  | .fanCertificateCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fanCertificateCap") 76
  | .fanCertificateMarked =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fanCertificateMarked") 77
  | .fanCertificateResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "fanCertificateResidual") 78
  | .typeBHybridEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHybridEntry") 80
  | .typeBDirectCycleFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBDirectCycleFree") 82
  | .typeBB2Choice =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBB2Choice") 149
  | .typeBDisjointLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDisjointLedger") 150
  | .typeBOverlapObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBOverlapObstruction") 84
  | .typeBGlobalLocalBridge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBGlobalLocalBridge") 447
  | .fanCertificateResidualMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "fanCertificateResidualMass") 186
  | .typeBOverlapObstructionMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBOverlapObstructionMass") 187
  | .typeBAbsorbedHalfEdge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBAbsorbedHalfEdge") 2100
  | .typeBAbsorbedHalfEdgeAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBAbsorbedHalfEdgeAbsent") 2101
  | .absorbedHandoffCore =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "absorbedHandoffCore") 3100
  | .absorbedHandoffCoreAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "absorbedHandoffCoreAbsent") 3101
  | .absorbedF4Charge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "absorbedF4Charge") 3102
  | .typeBDegreeFourLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDegreeFourLedger") 2102
  | .typeBDegreeFourOverlap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDegreeFourOverlap") 2103
  | .typeBDegreeFourClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDegreeFourClosed") 2104
  | .typeBAbsorbedCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBAbsorbedCharge") 2800
  | .typeBRoute8Entry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBRoute8Entry") 2801
  | .typeBBridgeMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBBridgeMass") 85
  | .typeBBridgeSublinear =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBBridgeSublinear") 189
  | .typeBExcluded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBExcluded") 166
  | .typeBExclusionResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBExclusionResidual") 167
  | .typeAExitFourPeeled =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourPeeled") 151
  | .typeAExitFourFiniteDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourFiniteDescent") 153
  | .typeASaturatedHandoffExitFour =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffExitFour") 156
  | .typeASaturatedHandoffExitFourFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffExitFourFree") 157
  | .typeAExitFourReceiverDischarged =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourReceiverDischarged") 152
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
  | .route8ResidualProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8ResidualProfile") 159
  | .route8BasinBurden =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8BasinBurden") 161
  | .route8LargeBudgetDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8LargeBudgetDeficit") 162
  | .route8LargeBudgetDeficitFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8LargeBudgetDeficitFails") 329
  | .route8CarrierCore =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8CarrierCore") 163
  | .route8TrueResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8TrueResidual") 332
  | .route8CarrierCutParity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8CarrierCutParity") 333
  | .route8SmallCoreEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8SmallCoreEntry") 330
  | .route8NoSmallCoreEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8NoSmallCoreEntry") 331
  | .route8SmallCoreCollapse =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8SmallCoreCollapse") 168
  | .route8CarrierDeletionWitnesses =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8CarrierDeletionWitnesses") 170
  | .route8PrivateCarrierBudget =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8PrivateCarrierBudget") 171
  | .route8Census =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Census") 260
  | .route8Rate =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Rate") 264
  | .route8RateFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateFails") 265
  | .route8PiecesClassified =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8PiecesClassified") 266
  | .route8UnifiedNegative =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnifiedNegative") 336
  | .route8UnifiedDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnifiedDeficit") 339
  | .route8UnifiedEntryCensus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8UnifiedEntryCensus") 340
  | .route8StageRateFailed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8StageRateFailed") 342
  | .route8DemandAbsorption =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8DemandAbsorption") 351
  | .route8WindowBlockers =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8WindowBlockers") 352
  | .route8UnpaidExitFourResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8UnpaidExitFourResidual") 503
  | .route8UnifiedVisibleResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8UnifiedVisibleResidual") 504
  | .route8UnifiedVisibleOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8UnifiedVisibleOverload") 505
  | .route8JointBalance =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8JointBalance") 506
  | .route8TwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8TwoCarrierEntry") 261
  | .route8NoTwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8NoTwoCarrierEntry") 262
  | .route8TrueTwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8TrueTwoCarrierEntry") 280
  | .route8PeelingDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8PeelingDescent") 282
  | .route8UnifiedTrueTwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8UnifiedTrueTwoCarrierEntry") 334
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
  | .sparsePairExit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sparsePairExit") 143
  | .sparseTargetDefectResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sparseTargetDefectResidual") 400
  | .canonicalBlockerRoute =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalBlockerRoute") 144
  | .sparseUpperEnvelope =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sparseUpperEnvelope") 129
  | .capacityTokenLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "capacityTokenLedger") 114
  | .roleFibrePartition =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "roleFibrePartition") 115
  | .fibrePressure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "fibrePressure") 116
  | .spineSurplusEstimate =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "spineSurplusEstimate") 126
  | .sparsePressureNearCubic =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sparsePressureNearCubic") 127
  | .sparsePressureOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sparsePressureOverload") 128
  | .freePairEntropySandwich =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "freePairEntropySandwich") 240
  | .freePairCodeUnrealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "freePairCodeUnrealized") 241
  | .blockedPairEntropySetup =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedPairEntropySetup") 356
  | .blockedPairEntropySandwich =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedPairEntropySandwich") 242
  | .blockedPairCodeUnrealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedPairCodeUnrealized") 243
  | .pairOverlapFirstFailure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairOverlapFirstFailure") 357
  | .pairOverlapSystem =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairOverlapSystem") 401
  | .pairConditionalFactorization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairConditionalFactorization") 412
  | .pairConditionalFactorizationResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairConditionalFactorizationResidual") 413
  | .pairFailureOverlap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairFailureOverlap") 402
  | .pairDemandReturns =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairDemandReturns") 405
  | .pairSystemRealizability =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairSystemRealizability") 414
  | .pairSystemEarlyOutcome =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairSystemEarlyOutcome") 415
  | .pairSerialDemandSystem =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairSerialDemandSystem") 416
  | .pairIncrementCovered =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairIncrementCovered") 417
  | .pairIncrementEarlyOutcome =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairIncrementEarlyOutcome") 418
  | .pairSerialArithmetic =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairSerialArithmetic") 419
  | .pairPowerOfTwoCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "pairPowerOfTwoCycle") 420
  | .windowClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowClassOverload") 130
  | .windowClassAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowClassAbsent") 131
  | .remainderClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "remainderClassOverload") 132
  | .remainderClassAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderClassAbsent") 133
  | .homogeneousCapsHold =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "homogeneousCapsHold") 140
  | .homogeneousCapsFail =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "homogeneousCapsFail") 601
  | .homogeneousBottleneckPattern =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "homogeneousBottleneckPattern") 141
  | .bottleneckRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "bottleneckRouting") 142
  | .typeBHandoff =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHandoff") 184
  | .typeBHandoffFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHandoffFails") 1801
  | .sameTokenPatternUnresolved =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sameTokenPatternUnresolved") 1802
  | .homogeneousBottleneck =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "homogeneousBottleneck") 118
  | .sparseSurplusSurvivor =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "sparseSurplusSurvivor") 119
  | .activeSurplusDemands =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "activeSurplusDemands") 120
  | .hotColdPartition =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hotColdPartition") 200
  | .dependentPairFamily =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "dependentPairFamily") 201
  | .independentPairFamily =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "independentPairFamily") 202
  | .mixedSparseSpineDependence =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "mixedSparseSpineDependence") 203
  | .exactCubicBaselineBudget =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "exactCubicBaselineBudget") 204
  | .incrementalSkeletonRoom =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "incrementalSkeletonRoom") 205
  | .skeletonDominates =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "skeletonDominates") 206
  | .exactResponseProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "exactResponseProfile") 207
  | .targetRankCircuit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "targetRankCircuit") 210
  -- F4 keys
  | .freePairCountFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "freePairCountFails") 1600
  | .blockedPairCountFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedPairCountFails") 1601
  | .blockedPairNoExit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedPairNoExit") 1602
  | .primitiveClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "primitiveClassOverload") 1603
  | .pairFactorizationFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairFactorizationFails") 1604
  | .pairRealizabilityFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairRealizabilityFails") 1605
  | .pairSystemNoEarlyOutcome =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairSystemNoEarlyOutcome") 1606
  | .pairIncrementFails =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairIncrementFails") 1607
  | .pairIncrementNoEarlyOutcome =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairIncrementNoEarlyOutcome") 1608
  | .pairCorrelation =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairCorrelation") 8200
  | .pairCoverage =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairCoverage") 8201
  | .pairFullModulus =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairFullModulus") 8202
  | .pairUncrossing =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairUncrossing") 8203
  -- SP keys
  -- F1 keys
  | .typeASupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeASupport") 1000
  | .typeANoVisibleEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeANoVisibleEntry") 1001
  | .typeAExitFourAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFourAbsent") 1002
  | .typeAExitSixProperScope =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSixProperScope") 1004
  | .typeAExitSixGlobalScope =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSixGlobalScope") 1005
  -- F3 keys
  | .route8TwoCarrierExit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8TwoCarrierExit") 1400
  | .route8UnifiedTwoCarrierExit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnifiedTwoCarrierExit") 1401
  | .route8StageRate =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8StageRate") 1402
  | .route8UnpaidTwoCarrier =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnpaidTwoCarrier") 1403
  | .route8UnpaidWitnessFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnpaidWitnessFree") 1404
  -- R3 keys
  | .route8UnifiedEmptyAtG =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8UnifiedEmptyAtG") 7900
  -- R8Q keys
  | .route8QuotientEntriesAtG =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8QuotientEntriesAtG") 8150
  | .typeBSublinearCanonicalForm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBSublinearCanonicalForm") 8300
  | .groupedAbsorbedCoreSubset =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "groupedAbsorbedCoreSubset") 8301
  | .typeBSublinearFailureArms =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBSublinearFailureArms") 8302
  | .groupedCentresHigh =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "groupedCentresHigh") 8303
  | .handoffDegreeClauseEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "handoffDegreeClauseEmpty") 8304
  | .pieceRoutingTotal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pieceRoutingTotal") 8305
  | .coverPayment =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coverPayment") 8306
  | .loadFailureSaturated =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "loadFailureSaturated") 8307
  | .unpaidAbsorbedWindowPort =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "unpaidAbsorbedWindowPort") 8308
  | .receiverPortsAreWindowStubs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "receiverPortsAreWindowStubs") 8309
  | .saturatedReceiverBasin =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "saturatedReceiverBasin") 8310
  | .loadFlowValue =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "loadFlowValue") 8311
  | .coverFlowValue =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coverFlowValue") 8312
  | .pieceSizeProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pieceSizeProfile") 8313
  -- R3b keys
  | .typeAExitFourSwitchCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFourSwitchCycle") 7960
  | .typeAExitSevenSwitch =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSevenSwitch") 7961
  -- F5 keys
  | .coldNoPositiveGerm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldNoPositiveGerm") 1800
  -- SD keys (final pass)
  | .degreeProfileFibres =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "degreeProfileFibres") 2300
  | .targetCompleteContextUniversality =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "targetCompleteContextUniversality") 2301
  | .hssTargetCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hssTargetCycle") 2303
  -- SP keys (fix2)
  | .pairResponseObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairResponseObstruction") 2900
  | .pairNoResponseObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairNoResponseObstruction") 2901
  | .pairDegreeProfileFibres =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairDegreeProfileFibres") 2902
  | .pairProfileObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairProfileObstruction") 2903
  | .pairNoProfileObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairNoProfileObstruction") 2904
  | .sameTokenReadingsNotReplacement =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenReadingsNotReplacement") 2905
  | .twoSwitchForcedPath =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "twoSwitchForcedPath") 6800
  | .highCentreSplitForced =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highCentreSplitForced") 6801
  | .crossSwitchFamily =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "crossSwitchFamily") 6802
  | .sameVertexSwitchForcedPath =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameVertexSwitchForcedPath") 6803
  | .sameTokenPatternSupports =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenPatternSupports") 6804
  | .sameTokenPatternSwap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenPatternSwap") 6805
  | .sameTokenPairPartition =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenPairPartition") 6806
  | .coldCutStatesDistinct =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCutStatesDistinct") 3200
  | .coldRepeatedStateResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldRepeatedStateResidual") 3201
  | .coldHeavyEntryTerminal =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldHeavyEntryTerminal") 3202
  | .entropyJointRealization =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyJointRealization") 3204
  | .allColdEntropyResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "allColdEntropyResidual") 3205
  -- C6 keys (density order)
  | .realizedDensityOrder =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "realizedDensityOrder") 6600
  | .realizedOrderLarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "realizedOrderLarge") 6601
  | .realizedOrderSmall =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "realizedOrderSmall") 6602
  | .boundedDensityOrder =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "boundedDensityOrder") 6603
  | .route8RateFailsJoin =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateFailsJoin") 8250
  | .route8RateFailsPiece =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateFailsPiece") 8251
  | .route8RateFailsCrossBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateFailsCrossBound") 8252
  | .route8RateFailsFlow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateFailsFlow") 8253
  | .route8CarrierInjection =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8CarrierInjection") 8254
  | .route8RateExactSlack =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8RateExactSlack") 8255
  | .route8StubDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8StubDeficit") 8256
  | .route8DeficitVsStubs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8DeficitVsStubs") 8257
  | .route8EntryLowerBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8EntryLowerBound") 8258
  | .route8CoreEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8CoreEmpty") 8259
  | .route8StrongRate =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8StrongRate") 8260
  | .route8ThinIsolation =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8ThinIsolation") 8261
  | .route8WindowStub =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8WindowStub") 8262
  | .route8ThinSmall =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8ThinSmall") 8263
  | .route8WindowRPathGap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8WindowRPathGap") 8264
  | .route8HubStubs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8HubStubs") 8265
  | .route8WindowSelfRPathGap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8WindowSelfRPathGap") 8266
  | .route8PieceBoundary =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8PieceBoundary") 8267
  | .route8WindowPieceRank =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8WindowPieceRank") 8268
  | .route8AchievableLengths =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8AchievableLengths") 8269
  | .boundedOrderLarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "boundedOrderLarge") 6604
  | .boundedOrderSmall =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "boundedOrderSmall") 6605
  -- [20a] enrichment keys
  | .edgeSurplusIdentity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "edgeSurplusIdentity") 6606
  | .surplusDartIdentity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "surplusDartIdentity") 6607
  | .highDegreeCountBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highDegreeCountBound") 6608
  | .highDegreePositive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highDegreePositive") 6609
  | .highDegreeSurplusCapacity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highDegreeSurplusCapacity") 6610
  | .packingOrderBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "packingOrderBound") 6611
  | .ceilSqrtAboveScale =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "ceilSqrtAboveScale") 6612
  | .orderAboveScaleSquare =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "orderAboveScaleSquare") 6613
  | .sixVertexExtremalEnvelope =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sixVertexExtremalEnvelope") 6614
  | .noSuppressionChordViolation =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "noSuppressionChordViolation") 6620
  | .admissibleQuotientsLabelInjective =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "admissibleQuotientsLabelInjective") 6626
  | .singleBoundaryShape =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "singleBoundaryShape") 6627
  | .remainderDeficiencyBelowCut =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderDeficiencyBelowCut") 6663
  | .windowCutCapacity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowCutCapacity") 6664
  | .canonicalCapacityExplicit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalCapacityExplicit") 6665
  | .primitiveCarrierCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "primitiveCarrierCount") 6666
  | .canonicalTokenCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalTokenCount") 6667
  | .canonicalBlockedFreePartition =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalBlockedFreePartition") 6668
  | .canonicalLedgerDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalLedgerDeficit") 6669
  | .pairCountDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairCountDeficit") 6670
  | .canonicalCertificationCriterion =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalCertificationCriterion") 6671
  | .paperBudgetBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "paperBudgetBound") 6672
  | .paperBudgetCertifies =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "paperBudgetCertifies") 6673
  | .canonicalOverloadOfFits =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalOverloadOfFits") 6674
  | .canonicalFreeExcessOfCapped =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "canonicalFreeExcessOfCapped") 6675
  | .pairCodeConfiguration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairCodeConfiguration") 6676
  | .specWitnessStructure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "specWitnessStructure") 6677
  | .everyWitnessSpectrumSplit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "everyWitnessSpectrumSplit") 6702
  | .highSurplusConfiguration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highSurplusConfiguration") 6703
  | .highEndpointSwitch =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highEndpointSwitch") 6704
  -- port-cycles keys
  | .neighbourhoodPairCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "neighbourhoodPairCount") 6900
  | .starCycleConstraint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "starCycleConstraint") 6901
  | .meetingCycleConstraint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "meetingCycleConstraint") 6902
  | .highDegreePairSum =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highDegreePairSum") 6903
  | .vertexDeletionComponents =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "vertexDeletionComponents") 6904
  | .cyclesThroughVertex =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cyclesThroughVertex") 6905
  | .cutVertexBlockPaths =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cutVertexBlockPaths") 6906
  | .cycleDoubleCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cycleDoubleCount") 6907
  -- port-local keys
  | .threeRouteFan =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "threeRouteFan") 7100
  | .threeRouteChain =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "threeRouteChain") 7101
  | .windowPositionStubs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowPositionStubs") 7102
  | .windowAttachmentGap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowAttachmentGap") 7103
  -- port-joint keys
  | .cubicNeighbourSupply =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cubicNeighbourSupply") 7200
  | .hubCountBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubCountBound") 7201
  | .lowEdgeParity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "lowEdgeParity") 7202
  | .bigHubBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "bigHubBound") 7203
  | .bigHubVShapes =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "bigHubVShapes") 7204
  | .highSurplusBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highSurplusBound") 7205
  | .hubLengthThreePairs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubLengthThreePairs") 7206
  | .densityExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "densityExcess") 7207
  | .remainderSlack =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderSlack") 7208
  | .hubWindowBudget =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubWindowBudget") 7209
  | .windowHubBounds =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowHubBounds") 7210
  | .remainderPathBounds =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderPathBounds") 7211
  | .windowFreeGeometry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowFreeGeometry") 7212
  | .inducedPathAttachment =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "inducedPathAttachment") 7213
  | .highSurplusOrder =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "highSurplusOrder") 7214
  | .windowChargeKinds =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowChargeKinds") 7215
  | .responseObstructionTargetDefect =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "responseObstructionTargetDefect") 7216
  | .hubLinkStructure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubLinkStructure") 7217
  | .hubClassCounts =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubClassCounts") 7218
  | .slotRelation =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "slotRelation") 7219
  | .closedClasses =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "closedClasses") 7220
  | .hubTwoHopLinks =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "hubTwoHopLinks") 7221
  | .slotLinear =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "slotLinear") 7222
  | .scalePressure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "scalePressure") 7223
  | .freeSideStructure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "freeSideStructure") 7224
  | .freeSideCount =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "freeSideCount") 7225
  | .freeSideHubs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "freeSideHubs") 7226
  | .extFreeEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "extFreeEmpty") 7227
  | .extLoadSum =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "extLoadSum") 7228
  | .extOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "extOverload") 7229
  | .extOverloadedToken =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "extOverloadedToken") 7230
  | .newLoadBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "newLoadBound") 7231
  | .separatedPairs =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "separatedPairs") 7232
  | .portEndDegree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "portEndDegree") 7233
  | .pairArmAPattern =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairArmAPattern") 7234
  | .pairArmARoleAlphabet =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairArmARoleAlphabet") 7235
  | .pairArmB =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairArmB") 7236
  | .sparseTargetDefectEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sparseTargetDefectEmpty") 7800
  | .sameTokenTransplantSize =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenTransplantSize") 8000
  | .sameTokenTransplantDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenTransplantDeficit") 8001
  | .sameTokenUnresolvedDecided =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenUnresolvedDecided") 8100
  | .sameTokenReadingsExact =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenReadingsExact") 8101
  | .sameTokenSwap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenSwap") 8102
  | .sameTokenSwapExact =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenSwapExact") 8103
  | .sameTokenU2FreeWhole =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenU2FreeWhole") 8104
  -- g-audit 172a keys
  | .blockedOwnRecord =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedOwnRecord") 8600
  | .blockedFailureSlack =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedFailureSlack") 8601
  | .blockedPrefixCompression =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedPrefixCompression") 8602
  | .blockedFailingSetCarries =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedFailingSetCarries") 8603
  | .blockedOverlapSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedOverlapSupport") 8604
  | .pairHandoffSupport =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffSupport") 8350
  | .pairHandoffCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffCharge") 8351
  | .pairHandoffNetCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffNetCharge") 8352
  | .pairHandoffHubCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffHubCharge") 8353
  | .pairHandoffBoundaryType =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffBoundaryType") 8354
  | .pairHandoffCriticalCoordinate =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffCriticalCoordinate") 8355
  | .pairObstructionDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairObstructionDescent") 8356
  | .pairHandoffHubForces =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffHubForces") 8357
  | .pairHandoffDemandEnds =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffDemandEnds") 8358
  | .pairHandoffHubBalance =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffHubBalance") 8359
  | .pairHandoffFibreAtG =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "pairHandoffFibreAtG") 8360
  | .stubDeficitIdentity =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "stubDeficitIdentity") 8550
  | .remainderCycleSpectrum =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderCycleSpectrum") 8551
  | .sameTokenSeedCover =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenSeedCover") 8105
  | .sameTokenPathInteractions =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "sameTokenPathInteractions") 8106
  -- TA keys
  | .typeAPeeledSaturatedReceiver =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledSaturatedReceiver") 2000
  | .typeAPeeledUnsaturatedDischarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledUnsaturatedDischarge") 2001
  | .typeAPeeledVisibleEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledVisibleEntry") 2002
  | .typeAPeeledNoVisibleEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledNoVisibleEntry") 2003
  | .typeAPeeledSilentExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledSilentExcess") 2004
  | .typeAPeeledExitOneReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitOneReturn") 2005
  | .typeAPeeledExitOneFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitOneFree") 2006
  | .typeAPeeledExitTwoTheta =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitTwoTheta") 2007
  | .typeAPeeledExitTwoFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitTwoFree") 2008
  | .typeAPeeledExitThreeCollision =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitThreeCollision") 2009
  | .typeAPeeledExitThreeFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPeeledExitThreeFree") 2010
  | .typeAExitThreeCycle =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitThreeCycle") 2011
  | .typeAExitSevenEnvelope =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSevenEnvelope") 2012
  | .coldAbsorbedNeutralConfiguration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldAbsorbedNeutralConfiguration") 2700
  | .coldSelectedFamilyEmpty =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldSelectedFamilyEmpty") 2701
  | .coldMarkedGermUncompressed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldMarkedGermUncompressed") 8400
  | .coldMarkedGermStretchExcision =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldMarkedGermStretchExcision") 8401

/-- The written-out names agree with `label` and `idx`.  `name` is spelled out
so that reducing it in a downstream audit proof costs one unfolding rather
than three; this lemma is what ties the spelling back to the two components,
and it is one constant-time `rfl` per key. -/
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
      (problem BranchState Presentation presentation data.toParameters) where
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

/-- The residual domain of a minimum-degree cycle spine. -/
abbrev Input (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :=
  Core.Strategy.ProblemInput
    (problem BranchState Presentation presentation data.toParameters)

/-- The spine's sole `FactSystem`.  It is a definition rather than an
instance because the registered `Data` is a parameter of the spine, not of the
problem; a caller installs it with `letI` for the run it is compiling. -/
noncomputable def factSystem
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    FactSystem
      (Core.Strategy.ProblemInput
        (problem BranchState Presentation presentation data.toParameters)) :=
  problemInputFactSystem
    (vocabulary BranchState Presentation presentation data)

/-- The exact semantic keys, as callers name them. -/
abbrev key (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key) :
    @FactKey _ _ (factSystem BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

/-- The vocabulary owns the unique fact-system registration for its residual
domain. Strategy executors import the vocabulary/rows directly; they do not
depend on the monolithic proof assembly merely to recover key elaboration. -/
noncomputable instance instFactSystem
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    FactSystem (Input BranchState Presentation presentation data) :=
  factSystem BranchState Presentation presentation data

/-- The spine's exact semantic keys. -/
abbrev K
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}}
    (k : Key) : FactKey (Input BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

/-- The residual domain's framework-owned closure key. -/
abbrev closed
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    FactKey (Input BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.closed

@[simp] theorem closureKey_eq_closed
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    (FactSystem.closureKey :
        FactKey (Input BranchState Presentation presentation data)) = closed :=
  rfl

@[simp] theorem K_eq_iff
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}}
    (left right : Key) :
    (K (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data) left = K right) ↔
      left = right := by
  change FactVocabulary.WithClosure.fact
      (vocabulary := vocabulary BranchState Presentation presentation data) left =
      FactVocabulary.WithClosure.fact
        (vocabulary := vocabulary BranchState Presentation presentation data) right ↔
      left = right
  constructor
  · intro same
    exact FactVocabulary.WithClosure.fact.inj same
  · intro same
    cases same
    rfl

@[simp] theorem K_ne_closed
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}}
    (key : Key) :
    K (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data) key ≠ closed := by
  change FactVocabulary.WithClosure.fact
      (vocabulary := vocabulary BranchState Presentation presentation data) key ≠
    FactVocabulary.WithClosure.closed
      (vocabulary := vocabulary BranchState Presentation presentation data)
  intro impossible
  cases impossible

/-! ## Key freshness by kernel decision

Freshness, distinctness and disjointness of spine keys are decided from the
closed vocabulary: a literal key list is tested by the kernel with the
vocabulary's own decidable equality (`Key`'s derived `DecidableEq`, which
compares constructor indices), so no pair of keys is ever compared by case
analysis and no table is written down.  An opaque ledger index `known` is
split off and closed by the caller's freshness hypothesis. -/

theorem keyFresh_append {α : Type _} {key : α} {left right : List α}
    (leftFresh : key ∉ left) (rightFresh : key ∉ right) :
    key ∉ left ++ right := by
  rw [List.mem_append]
  exact fun member => member.elim leftFresh rightFresh

theorem keyFresh_cons {α : Type _} {key head : α} {tail : List α}
    (headNe : key ≠ head) (tailFresh : key ∉ tail) : key ∉ head :: tail := by
  rw [List.mem_cons]
  exact fun member => member.elim headNe tailFresh

theorem keyFresh_of_cons_tail {α : Type _} {key head : α} {tail : List α}
    (fresh : key ∉ head :: tail) : key ∉ tail :=
  fun member => fresh (List.mem_cons_of_mem head member)

theorem keyFresh_of_append_left {α : Type _} {key : α} {left right : List α}
    (fresh : key ∉ left ++ right) : key ∉ left :=
  fun member => fresh (List.mem_append_left right member)

theorem keyFresh_of_append_right {α : Type _} {key : α} {left right : List α}
    (fresh : key ∉ left ++ right) : key ∉ right :=
  fun member => fresh (List.mem_append_right left member)

theorem keyFresh_of_contains {α : Type _} [DecidableEq α] {key : α}
    {keys : List α} (absent : keys.contains key = false) : key ∉ keys :=
  fun member => by
    have present : keys.contains key = true := List.elem_eq_true_of_mem member
    rw [absent] at present
    exact Bool.noConfusion present

/-- A key of a covering list is fresh for every list disjoint from it: one
`List.Disjoint covering known` hypothesis stands for the freshness of each key
of `covering` in an opaque ledger index `known`. -/
theorem keyFresh_of_disjoint {α : Type _} [DecidableEq α] {key : α}
    {covering keys : List α} (disjoint : List.Disjoint covering keys)
    (present : covering.contains key = true) : key ∉ keys :=
  fun member => disjoint (List.mem_of_elem_eq_true present) member

theorem keyNe_of_decide {α : Type _} [DecidableEq α] {left right : α}
    (distinct : decide (left = right) = false) : left ≠ right :=
  of_decide_eq_false distinct

theorem keyDisjoint_of_all {α : Type _} [DecidableEq α] {left right : List α}
    (fresh : (left.all fun key => !right.contains key) = true) :
    List.Disjoint left right := fun key member member' => by
  have absent := List.all_eq_true.mp fresh key member
  have present : right.contains key = true := List.elem_eq_true_of_mem member'
  rw [present] at absent
  exact Bool.noConfusion absent

theorem keyDisjoint_append_right {α : Type _} {left first second : List α}
    (firstDisjoint : List.Disjoint left first)
    (secondDisjoint : List.Disjoint left second) :
    List.Disjoint left (first ++ second) := fun _ member member' => by
  rw [List.mem_append] at member'
  exact member'.elim (firstDisjoint member) (secondDisjoint member)

theorem keyDisjoint_cons_right {α : Type _} {left tail : List α} {head : α}
    (headFresh : head ∉ left) (tailDisjoint : List.Disjoint left tail) :
    List.Disjoint left (head :: tail) := fun _ member member' => by
  rw [List.mem_cons] at member'
  exact member'.elim (fun same => headFresh (same ▸ member))
    (tailDisjoint member)

theorem keyDisjoint_cons_left {α : Type _} {head : α} {tail right : List α}
    (headFresh : head ∉ right) (tailDisjoint : List.Disjoint tail right) :
    List.Disjoint (head :: tail) right := fun _ member member' => by
  rw [List.mem_cons] at member
  exact member.elim (fun same => headFresh (same ▸ member'))
    (fun member => tailDisjoint member member')

theorem keyDisjoint_append_left {α : Type _} {first second right : List α}
    (firstDisjoint : List.Disjoint first right)
    (secondDisjoint : List.Disjoint second right) :
    List.Disjoint (first ++ second) right := fun _ member member' => by
  rw [List.mem_append] at member
  exact member.elim (fun member => firstDisjoint member member')
    (fun member => secondDisjoint member member')

theorem keyDisjoint_nil_left {α : Type _} {right : List α} :
    List.Disjoint ([] : List α) right := fun _ member => nomatch member

namespace KeyFresh

open Lean Meta Elab Tactic

/-- The key type of one `key_fresh` call, its universe, and its decidable
equality and list membership instances, found once per call. -/
structure Keys where
  type : Expr
  level : Level
  decEq : Expr
  membership : Expr

def Keys.ofType (type : Expr) : MetaM Keys := do
  let level ← decLevel (← getLevel type)
  -- A locally installed instance (`letI : FactSystem _ := instFactSystem`) is
  -- replaced by its value, so the evidence mentions the vocabulary's own
  -- decidable equality and stays checkable without unfolding local lets.
  let decEq ← zetaReduce (← instantiateMVars
    (← synthInstance (mkApp (mkConst ``DecidableEq [level.succ]) type)))
  let listType := mkApp (mkConst ``List [level]) type
  let membership ← zetaReduce (← instantiateMVars (← synthInstance
    (mkApp2 (mkConst ``Membership [level, level]) type listType)))
  return { type, level, decEq, membership }

def Keys.list (keys : Keys) : Expr := mkApp (mkConst ``List [keys.level]) keys.type

def Keys.notMem (keys : Keys) (list key : Expr) : Expr :=
  mkNot <| mkApp5 (mkConst ``Membership.mem [keys.level, keys.level]) keys.type
    keys.list keys.membership list key

def Keys.disjoint (keys : Keys) (left right : Expr) : Expr :=
  mkApp3 (mkConst ``List.Disjoint [keys.level]) keys.type left right

def Keys.ne (keys : Keys) (left right : Expr) : Expr :=
  mkApp3 (mkConst ``Ne [keys.level.succ]) keys.type left right

def Keys.contains (keys : Keys) (list key : Expr) : Expr :=
  let beq := mkApp2 (mkConst ``instBEqOfDecidableEq [keys.level.succ]) keys.type keys.decEq
  mkApp4 (mkConst ``List.contains [keys.level]) keys.type beq list key

/-- Does `e` mention a free variable whose type is a list?  Such a variable is
an opaque ledger index; every other free variable is a parameter that the
kernel decision does not inspect. -/
def mentionsListFVar (e : Expr) : MetaM Bool := do
  let fvars := (collectFVars {} e).fvarIds
  fvars.anyM fun fvar => do
    let decl ← fvar.getDecl
    if decl.isLet then return false
    return (← whnfR (← instantiateMVars decl.type)).isAppOf ``List

def isListSpine (e : Expr) : Bool :=
  e.isAppOf ``HAppend.hAppend || e.isAppOf ``List.append ||
    e.isAppOf ``List.cons || e.isAppOf ``List.nil || e.isFVar

/-- Expose the next cell of a key list: `let`s and let-bound variables are
substituted, and anything else (a row manifest projection, say) is unfolded
to weak head normal form. -/
partial def listCell (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e with
  | .letE _ _ value body _ => listCell (body.instantiate1 value)
  | .fvar fvar =>
    match ← fvar.getValue? with
    | some value => listCell value
    | none => return e
  | _ =>
    if isListSpine e then return e
    let e' ← whnfD e
    if e' == e then return e else listCell e'

def bool (value : Bool) : Expr :=
  if value then mkConst ``Bool.true else mkConst ``Bool.false

def boolRefl (value : Bool) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (bool value)

/-- The literal elements of a key list, as far as they are syntactically
visible (`let`s and let-bound variables substituted, nothing unfolded). -/
partial def visibleElements (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e with
  | .letE _ _ value body _ => visibleElements (body.instantiate1 value) acc
  | .fvar fvar =>
    match ← fvar.getValue? with
    | some value => visibleElements value acc
    | none => return acc
  | _ =>
    if e.isAppOfArity ``List.cons 3 then
      visibleElements e.appArg! (acc.push e.appFn!.appArg!)
    else if e.isAppOfArity ``HAppend.hAppend 6 || e.isAppOfArity ``List.append 3 then
      visibleElements e.appArg! (← visibleElements e.appFn!.appArg! acc)
    else
      return acc

/-- Report a claim the goal itself refutes: `key` appears literally in
`list`.  This is diagnostics only; the verdict is the kernel's. -/
def refuteVisible (claim list key : Expr) : MetaM Unit := do
  let key ← instantiateMVars key
  if (← visibleElements list).contains key then
    throwError "key_fresh: the key occurs in the list{indentExpr claim}"

/-- Close `claim` with `proof rfl`, where `rfl : test = expected`.  The
kernel evaluates `test` -- the closed vocabulary's decidable equality on the
literal keys -- when it checks the enclosing declaration, sharing its
reduction cache across every key compared there. -/
def closeByKernel (goal : MVarId) (claim test : Expr) (expected : Bool)
    (proof : Expr → Expr) : MetaM Unit := do
  if (← instantiateMVars test).hasMVar then
    throwError "key_fresh: statement still has metavariables{indentExpr claim}"
  goal.assign (proof (boolRefl expected))

/-- Restrict a freshness proof `proof : key ∉ spine` to the opaque segment
`target` of `spine`, following its visible `cons`/`++` cells. -/
partial def restrictFresh (keys : Keys) (key proof spine target : Expr) :
    MetaM (Option Expr) := do
  let spine := (← instantiateMVars spine).cleanupAnnotations
  if spine == target then return some proof
  match spine with
  | .letE _ _ value body _ =>
      restrictFresh keys key proof (body.instantiate1 value) target
  | .fvar fvar =>
      match ← fvar.getValue? with
      | some value => restrictFresh keys key proof value target
      | none => return none
  | _ =>
    if spine.isAppOfArity ``List.cons 3 then
      let head := spine.appFn!.appArg!
      let tail := spine.appArg!
      restrictFresh keys key
        (mkApp5 (mkConst ``keyFresh_of_cons_tail [keys.level]) keys.type key head tail proof)
        tail target
    else if spine.isAppOfArity ``HAppend.hAppend 6 || spine.isAppOfArity ``List.append 3 then
      let left := spine.appFn!.appArg!
      let right := spine.appArg!
      if let some restricted ← restrictFresh keys key
          (mkApp5 (mkConst ``keyFresh_of_append_right [keys.level]) keys.type key left right
            proof) right target then
        return some restricted
      restrictFresh keys key
        (mkApp5 (mkConst ``keyFresh_of_append_left [keys.level]) keys.type key left right proof)
        left target
    else
      return none

/-- Every element of a closed key list, unfolding its cells as far as needed. -/
partial def elementsOf (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let cell ← listCell e
  if cell.isAppOfArity ``List.cons 3 then
    elementsOf cell.appArg! (acc.push (← instantiateMVars cell.appFn!.appArg!))
  else if cell.isAppOfArity ``HAppend.hAppend 6 || cell.isAppOfArity ``List.append 3 then
    elementsOf cell.appArg! (← elementsOf cell.appFn!.appArg! acc)
  else
    return acc

/-- The caller's freshness hypothesis for an opaque ledger index `list`: a
local `key ∉ spine` whose spine contains `list` as a visible segment. -/
def findHypothesis (keys : Keys) (list key : Expr) : MetaM (Option Expr) := do
  let mut candidates := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type := (← instantiateMVars decl.type).cleanupAnnotations
    let_expr Not inner := type | continue
    let_expr Membership.mem _ _ _ spine hypothesisKey := inner | continue
    if hypothesisKey == key then
      if let some proof ← restrictFresh keys key decl.toExpr spine list then
        return some proof
    else
      candidates := candidates.push (decl.toExpr, spine, hypothesisKey)
  for (proof, spine, hypothesisKey) in candidates do
    if ← isDefEq hypothesisKey key then
      if let some proof ← restrictFresh keys key proof spine list then
        return some proof
  -- A covering hypothesis `List.Disjoint covering list` whose literal
  -- `covering` contains `key`; the kernel checks the membership.
  let key ← instantiateMVars key
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type := (← instantiateMVars decl.type).cleanupAnnotations
    let_expr List.Disjoint _ covering spine := type | continue
    unless (← instantiateMVars spine).cleanupAnnotations == list do continue
    if (← mentionsListFVar covering) then continue
    let elements ← elementsOf covering
    unless elements.contains key || (← elements.anyM (isDefEq · key)) do continue
    return some <| mkApp7 (mkConst ``keyFresh_of_disjoint [keys.level]) keys.type
      keys.decEq key covering list decl.toExpr (boolRefl true)
  return none

mutual

/-- `key ∉ list`. -/
partial def notMem (keys : Keys) (goal : MVarId) (list key : Expr) : MetaM Unit := do
  let claim := keys.notMem list key
  if !(← mentionsListFVar list) then
    refuteVisible claim list key
    return ← closeByKernel goal claim (keys.contains list key) false fun rfl =>
      mkApp5 (mkConst ``keyFresh_of_contains [keys.level]) keys.type keys.decEq key list rfl
  let cell ← listCell list
  if cell.isAppOf ``HAppend.hAppend || cell.isAppOf ``List.append then
    let left := cell.appFn!.appArg!
    let right := cell.appArg!
    let leftGoal ← mkFreshExprSyntheticOpaqueMVar (keys.notMem left key)
    let rightGoal ← mkFreshExprSyntheticOpaqueMVar (keys.notMem right key)
    goal.assign <| mkApp6 (mkConst ``keyFresh_append [keys.level]) keys.type key left right
      leftGoal rightGoal
    notMem keys leftGoal.mvarId! left key
    notMem keys rightGoal.mvarId! right key
  else if cell.isAppOf ``List.cons then
    let head := cell.appFn!.appArg!
    let tail := cell.appArg!
    let headGoal ← mkFreshExprSyntheticOpaqueMVar (keys.ne key head)
    let tailGoal ← mkFreshExprSyntheticOpaqueMVar (keys.notMem tail key)
    goal.assign <| mkApp6 (mkConst ``keyFresh_cons [keys.level]) keys.type key head tail
      headGoal tailGoal
    distinct keys headGoal.mvarId! key head
    notMem keys tailGoal.mvarId! tail key
  else if cell.isAppOf ``List.nil then
    goal.assign <| mkApp2 (mkConst ``List.not_mem_nil [keys.level]) keys.type key
  else
    match ← findHypothesis keys cell key with
    | some proof => goal.assign proof
    | none => throwError "key_fresh: no freshness hypothesis for{indentExpr claim}"

/-- `left ≠ right`. -/
partial def distinct (keys : Keys) (goal : MVarId) (left right : Expr) : MetaM Unit := do
  let equality := mkApp3 (mkConst ``Eq [keys.level.succ]) keys.type left right
  let test := mkApp2 (mkConst ``Decidable.decide) equality (mkApp2 keys.decEq left right)
  if (← instantiateMVars left) == (← instantiateMVars right) then
    throwError "key_fresh: the two keys are equal{indentExpr (keys.ne left right)}"
  closeByKernel goal (keys.ne left right) test false fun rfl =>
    mkApp5 (mkConst ``keyNe_of_decide [keys.level]) keys.type keys.decEq left right rfl

/-- `List.Disjoint left right`. -/
partial def disjoint (keys : Keys) (goal : MVarId) (left right : Expr) : MetaM Unit := do
  let claim := keys.disjoint left right
  if !(← mentionsListFVar left) && !(← mentionsListFVar right) then
    let predicate ← withLocalDeclD `key keys.type fun key => do
      mkLambdaFVars #[key] <| mkApp (mkConst ``not) (keys.contains right key)
    let test := mkApp3 (mkConst ``List.all [keys.level]) keys.type left predicate
    for key in ← visibleElements left do
      refuteVisible claim right key
    return ← closeByKernel goal claim test true fun rfl =>
      mkApp5 (mkConst ``keyDisjoint_of_all [keys.level]) keys.type keys.decEq left right rfl
  -- The caller's own covering hypothesis `List.Disjoint left right`, verbatim.
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type := (← instantiateMVars decl.type).cleanupAnnotations
    let_expr List.Disjoint _ covering spine := type | continue
    if covering.cleanupAnnotations == left.cleanupAnnotations &&
        spine.cleanupAnnotations == right.cleanupAnnotations then
      goal.assign decl.toExpr
      return
  let rightCell ← listCell right
  if rightCell.isAppOf ``HAppend.hAppend || rightCell.isAppOf ``List.append then
    let first := rightCell.appFn!.appArg!
    let second := rightCell.appArg!
    let firstGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint left first)
    let secondGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint left second)
    goal.assign <| mkApp6 (mkConst ``keyDisjoint_append_right [keys.level]) keys.type
      left first second firstGoal secondGoal
    disjoint keys firstGoal.mvarId! left first
    disjoint keys secondGoal.mvarId! left second
    return
  if rightCell.isAppOf ``List.cons then
    let head := rightCell.appFn!.appArg!
    let tail := rightCell.appArg!
    let headGoal ← mkFreshExprSyntheticOpaqueMVar (keys.notMem left head)
    let tailGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint left tail)
    goal.assign <| mkApp6 (mkConst ``keyDisjoint_cons_right [keys.level]) keys.type
      left tail head headGoal tailGoal
    notMem keys headGoal.mvarId! left head
    disjoint keys tailGoal.mvarId! left tail
    return
  let leftCell ← listCell left
  if leftCell.isAppOf ``List.cons then
    let head := leftCell.appFn!.appArg!
    let tail := leftCell.appArg!
    let headGoal ← mkFreshExprSyntheticOpaqueMVar (keys.notMem right head)
    let tailGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint tail right)
    goal.assign <| mkApp6 (mkConst ``keyDisjoint_cons_left [keys.level]) keys.type
      head tail right headGoal tailGoal
    notMem keys headGoal.mvarId! right head
    disjoint keys tailGoal.mvarId! tail right
  else if leftCell.isAppOf ``HAppend.hAppend || leftCell.isAppOf ``List.append then
    let first := leftCell.appFn!.appArg!
    let second := leftCell.appArg!
    let firstGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint first right)
    let secondGoal ← mkFreshExprSyntheticOpaqueMVar (keys.disjoint second right)
    goal.assign <| mkApp6 (mkConst ``keyDisjoint_append_left [keys.level]) keys.type
      first second right firstGoal secondGoal
    disjoint keys firstGoal.mvarId! first right
    disjoint keys secondGoal.mvarId! second right
  else if leftCell.isAppOf ``List.nil then
    goal.assign <| mkApp2 (mkConst ``keyDisjoint_nil_left [keys.level]) keys.type right
  else
    throwError "key_fresh: no disjointness hypothesis for{indentExpr claim}"

end

/-- Dispatch one freshness, distinctness or disjointness goal. -/
def fresh (goal : MVarId) : MetaM Unit := goal.withContext do
  let claim := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  match_expr claim with
  | Not inner =>
      match_expr inner with
      | Membership.mem keyType _ _ list key =>
          notMem (← Keys.ofType keyType) goal list key
      | Eq keyType left right =>
          distinct (← Keys.ofType keyType) goal left right
      | _ => throwError "key_fresh: not a key freshness goal{indentExpr claim}"
  | Ne keyType left right => distinct (← Keys.ofType keyType) goal left right
  | List.Disjoint keyType left right =>
      disjoint (← Keys.ofType keyType) goal left right
  | List.Nodup keyType list =>
      let keys ← Keys.ofType keyType
      let decision := mkApp3 (mkConst ``List.nodupDecidable [keys.level]) keyType keys.decEq list
      closeByKernel goal claim (mkApp2 (mkConst ``Decidable.decide) claim decision) true
        fun rfl => mkApp3 (mkConst ``of_decide_eq_true) claim decision rfl
  | _ => throwError "key_fresh: not a key freshness goal{indentExpr claim}"

end KeyFresh

/-- `key_fresh` discharges fact-key freshness and distinctness: `k ∉ keys`,
`List.Disjoint produced keys`, `k ≠ k'` and `List.Nodup keys`.  A literal key
list is decided by one kernel evaluation of the closed vocabulary's decidable
equality; an opaque ledger index is split off and closed by the caller's
freshness hypothesis. -/
elab "key_fresh" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  KeyFresh.fresh goal
  Lean.Elab.Tactic.replaceMainGoal []

end Hypostructure.Graph.Strategy.Spine
