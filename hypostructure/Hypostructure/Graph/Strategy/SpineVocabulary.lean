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
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.FanCertificate
import Hypostructure.Graph.TypeBDirectCycle
import Hypostructure.Graph.TypeBFanIncidence
import Hypostructure.Graph.TypeBHybridIncidence
import Hypostructure.Graph.TypeBRefinedSupport
import Hypostructure.Graph.TypeBEnvelopeCharge
import Hypostructure.Graph.TypeBPostLedgerCore
import Hypostructure.Graph.TypeBMaximalCompletion
import Hypostructure.Graph.TypeADischarge
import Hypostructure.Graph.AnchoredReturnCompletion
import Hypostructure.Graph.ExitFourFamily
import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.Route8CarrierCore
import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.ReceiverRouting
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.CommonPortReturnCycle
import Hypostructure.Graph.PortReturnExistence
import Hypostructure.Graph.VisibleEntryQuotient
import Hypostructure.Graph.DecoratedHandoffEnvelope
import Hypostructure.Graph.TypeAVisibleResponseAssembly
import Hypostructure.Graph.TypeAExitSevenGermSchedule
import Hypostructure.Graph.WindowLabelCollision
import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.WedgeLowerBound
import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.OneThreeRepair
import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Core.CeilSqrt
import Hypostructure.Core.Finite.CertifiedTableAggregation
import Hypostructure.Graph.SeparatedPackageSkeleton
import Hypostructure.Graph.WindowTargetPackage
import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.RemainderEntropy
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.ObjectCapacityLedger
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

/-- The homogeneous cap computed from a presentation's declared routing
alphabet.  This pre-`Data` form lets the record certify arithmetic involving
the derived cap without registering a duplicate numeric constant. -/
def registeredHomogeneousCap (routingLabelBound : Nat) : Nat :=
  Graph.SameTokenBlockerRoles.homogeneousTokenCap routingLabelBound

/-- The final square-root coefficient, entirely derived from the public
presentation and the generic capacity-token accounting. -/
def registeredSpineScale
    (routingLabelBound threshold deficitScale : Nat) : Nat :=
  let cap := registeredHomogeneousCap routingLabelBound
  2 * (1 + 2 * cap) +
    (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2))

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
  /-- **`def:same-token-routing-germs`' routing-label alphabet.**

  *"The routing label of a pair in `Π_{t,r}` records the same-token role `r`,
  the subtype of `t`, the ordered endpoint of the pair under discussion, the
  local open/triangular status of the corresponding selected ports, the
  boundary-degree profile of the bounded port supports `T(p),T(q)`, the
  `P₁₃`-label entries appearing in the bounded part of the support, and the
  suppressed-chord flag when the blocker has type (f).  These labels form a
  finite set; denote its cardinality by `Q_geom`."*

  `Q_geom` is a number the *registered declared-coordinate signature* fixes, not
  one that varies with the object, which is why the alphabet is registered here
  rather than quantified at the node: `L_geom = Q_geom + 1` has to be one
  number, or nodes `[140]`--`[144]` are not testing the manuscript's threshold.
  Only the boundary-degree profile alphabet is registered here.  The `P₁₃`
  label is *not*: it is `Graph.WindowCurvature.Label windowOrder`, the
  labelling's own computed alphabet, whose legality table node `[125]`'s
  `localAlgebra` entry already carries -- so it is derived from the registered
  window order rather than declared again.  The other five coordinates are the
  framework's own finite alphabets, so `SameTokenRoutingGerms.RoutingLabel` at
  the registered profile alphabet and that label type *is* the set `ρ_t` lands
  in, and `Q_geom` is its cardinality. -/
  BoundaryProfile : Type
  /-- The profile alphabet is finite. -/
  boundaryProfileFintype : Fintype BoundaryProfile
  /-- The declared boundary-profile alphabet has a realizable profile. -/
  boundaryProfileInhabited : Inhabited BoundaryProfile
  /-- `Q_geom`, registered as a number so strategy arithmetic never evaluates
  the potentially enormous `Fintype` enumeration. -/
  routingLabelBound : Nat
  /-- The registered number is exactly the cardinality of the paper's routed
  seven-coordinate label alphabet. -/
  routingLabelBound_eq :
    letI := boundaryProfileFintype
    routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel BoundaryProfile
        (Graph.WindowCurvature.Label windowOrder))
  /-- The problem's declared same-token role alphabet covers the universal
  coefficient left by the generic quadratic absorption estimate.  This is a
  presentation check: the framework neither writes nor reconstructs a numeric
  lower bound for the problem's role alphabet. -/
  roleSafety :
    Graph.TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound)
  /-- The linear baseline-deficit scale certified by node `[21]` and consumed
  at `[129]`.  The final `C_sp` is not registered: `registeredSpineScale`
  derives it from this scale, the baseline degree, and the routing alphabet. -/
  surplusScale : Nat
  /-- The registered per-window barrier rate of the finite enumeration. -/
  windowRate : Nat
  /-- The complete certified finite barrier table from which `windowRate` is
  derived.  Generic package construction reads this projection; strategy rows
  never import an application-owned finite check. -/
  windowBarrier : Core.Finite.CertifiedTableAggregation.BarrierPresentation
  /-- The registered rate is exactly the aggregate rate of the public table. -/
  windowRate_eq_barrier :
    windowRate = windowBarrier.binaryRateFloor
  /-- The selected dyadic scales of `lem:p13-window-package`. -/
  separatedScaleCount : Nat → Nat
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
  /-- **`c_Ω`, node `[48]`'s registered curvature cost.**  The entropy price of
  one independent curvature coordinate, in the units the skeleton budget is
  measured in.  `rem:curvature-provenance` is explicit that the routing supplies
  the *independence* of the curvature cost, not its size, and that the value
  enters only through `K_win = c_Ω·ω_win` and `K = c_Ω·ω`; `rem:closure-robust`
  adds that the closure outside the explicit residuals does not use the exact
  value at all.  So it is a presentation constant, registered here. -/
  curvatureCost : Nat
  /-- The registered one-step curvature cost is one certified row rate of the
  same public finite table. -/
  curvatureBarrierRow : windowBarrier.Index
  curvatureCost_eq_barrierRow :
    letI := windowBarrier.indexFintype
    curvatureCost =
      Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
        windowBarrier.table curvatureBarrierRow
  /-- **The `10` of node `[50]`.**  `prop:two-budget` splits on
  `η(R) ≥ (1/10)·log₂ n`, and the denominator is the proof's own threshold
  choice rather than anything measured on a graph.  Node `[50]` compares
  `n^{|R|}` against `|𝒢(R)|^d` at this `d`, so no logarithm or division is
  written. -/
  entropyDenominator : Nat
  entropyDenominator_pos : 0 < entropyDenominator
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

/-- `M₀ = Cap_hom(L_geom)`, computed generically from the public declared
coordinate signature.  No application repeats or hardcodes this alphabet. -/
def Data.homogeneousCap (data : Data.{u}) : Nat :=
  registeredHomogeneousCap data.routingLabelBound

/-- The coefficient of the linear capacity-token supply, derived from the
public baseline degree. -/
def Data.capacityTokenScale (data : Data.{u}) : Nat :=
  3 * (data.threshold - 1) + 2

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
  let labelWitness : Label :=
    (⟨Graph.SameTokenBlockerRoles.BlockerKind.sharedDeclaredSupport,
        Graph.SameTokenBlockerRoles.TokenSubtype.boundaryWindow⟩,
      .boundaryWindow, 0, (.openPort, .openPort),
      (default, default), ∅, false)
  letI : Nonempty Label := ⟨labelWitness⟩
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

/-- The paper's `C_sp`, obtained by the generic quadratic absorption from the
public presentation's baseline deficit scale and the computed token cap. -/
def Data.spineScale (data : Data.{u}) : Nat :=
  registeredSpineScale data.routingLabelBound data.threshold data.surplusScale

/-- **The registered scale threshold `C_sp·⌈√n⌉` of node `[19]`**. -/
def Data.surplusThreshold (data : Data.{u}) (size : Nat) : Nat :=
  data.spineScale * Core.ceilSqrt size

/-- **`A`, the net-charge coefficient of `cor:global-window-join-pressure`.**
`s·(δ·order − 2(order−1)) + order`, the manuscript's `73` at its own values.
No node writes it; it is read from the registered numbers. -/
def Data.netChargeCoefficient (data : Data.{u}) : Nat :=
  data.dischargeScale *
      (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) +
    data.windowOrder

/-- The Type A/B presentation determined by the spine's registered data. -/
def Data.typeABPresentation (data : Data.{u}) : Graph.TypeAB.Presentation.{u} where
  baselineDegree := data.threshold
  inducedPathOrder := data.windowOrder
  dischargeScale := data.dischargeScale
  Target := Graph.HasCycleWithLength data.LengthOK
  LengthOK := data.LengthOK

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
  /-- Node `[30]`, the demand floor it is stated for: the wedge lower bound
  with the boundary-demand ceiling substituted for the deficiency.  This is
  invariant 28, the demand side of the final collision. -/
  | curvatureDemandFloor
  /-- `def:exact-response-profile` at the concrete remainder selected from the
  incoming maximal-packing fact.  The fact stores the boundary-degree profile,
  the literal all-context obstruction profile, the raw D4 coordinate family,
  its embedded values, and label exactness. -/
  | exactResponseProfile
  /-- `def:admissible-rank-quotient` for the exact response profile of the
  concrete remainder.  The fact publishes precisely the quotients represented
  by a connected, carrying, boundary-fibre preserving, context-universal
  `DeclaredQuotient` with the paper's proper and closed representative clauses. -/
  | admissibleRankQuotient
  /-- `def:functional-rank-quotient` for the admissible quotient family on the
  concrete remainder.  Membership is the exact admissible predicate restricted
  by the manuscript's finite determination axiom `RankQuotient.FunctionalOn`. -/
  | functionalRankQuotient
  /-- Node `[31]`: the curvature target-rank of the remainder is attained by a
  maximum-cardinality subfamily of raw internal curvature tests that survives
  every functional admissible rank quotient (`def:curvature-target-rank`).
  Circuit extraction is a separate later fact. -/
  | curvatureTargetRank
  /-- `lem:target-rank-circuit`: every coordinate outside the selected maximal
  surviving curvature family has a proper finite determination certificate
  for a functional admissible quotient. -/
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
  That certificate is the object nodes `[36]`, `[38]` and `[40]` route. -/
  | branchDependence
  /-- Node `[36]`, yes arm: the determination the certificate makes is valid
  against every outside context, and the states it identifies lie in one
  boundary-degree fibre (`lem:context-universality`,
  `lem:degree-profile-fibres`).  This is the residual node `[38]` consumes. -/
  | contextUniversal
  /-- Node `[36]`, no arm — the terminal `[37]`: some pair of states the
  certificate identifies is separated by a concrete outside context.  This is
  case (i) of `lem:curvature-dependence-routing`, a target-defective quotient.
  Boundary-profile preservation is already part of quotient admissibility. -/
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
  /-- Node `[60]` is entered in the paper's sufficiently-large regime. -/
  | netChargeLarge
  /-- The exhaustive complement of `netChargeLarge`; the asymptotic endpoint
  eliminates this arm before node `[60]`. -/
  | netChargeSmall
  /-- Node `[60]`: the large-budget remainder has negative total net charge
  once the paper's explicit sufficiently-large predicate holds. -/
  | netChargeCap
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
  /-- Node `[91]`: the `3/7/11` discharging conclusion on every unsaturated
  Type A support, in the exact integral form
  `|V(X)| ≤ s * def⁺(X)`. -/
  | typeAUnsaturatedDischarge
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
  /-- Node `[93]`, yes arm — clause (Q1) of `def:typeA-exit4-family`.  The
  visible receiver-entry coordinate identification at the port node `[93]`
  fixed is a member of the canonical exit-`(4)` family `𝒬₄(w)`: it is generated
  from the receiver's declared reading, it collapses at least one declared
  coordinate because the port carries a visible load, and its declared
  routed-load support contains every visible load of the port.  This is the
  clause row 16's exit-`(4)` peeling draws a *visible* load from; without it
  `𝒬₄(w)` is exhibited at none of its five generators. -/
  | typeAVisibleEntryClause
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
  /-- Node `[107]`, yes arm — exit `(7)` of `def:typeA-saturated-exits`: *"a
  high-degree decorated handoff fan envelope is produced"*, at the visible
  saturated port node `[93]` delivered.  This is the Type B handoff exit, and it
  is the one exit of the list that neither closes nor stays in Type A:
  `lem:typeA-exits-discharged` says the branch *"is reclassified as a decorated
  handoff fan envelope and leaves the Type A charge calculation"*.

  The envelope is `def:decorated-fan-envelope`'s `𝔛 = (Y, H)` with `Y` the Type
  A support itself and `H` the surviving first separator of two declared outside
  connector germs through the port — `def:typeA-trace-basin` clause (d), routed
  by `lem:typeA-continuation-routing`, with ambient degree at least `4` by
  `lem:typeA-cubic-switch-absorption` and handed over by
  `lem:typeA-high-degree-handoff`.  The fact carries the envelope's
  admissibility as well, which is `lem:decorated-fan-admissibility`: the handoff
  interface the Type B fan calculation consumes.  By
  `rem:typeA-typeB-stratification` no conclusion of `lem:typeB-exclusion` is
  used, and none is available on this cursor. -/
  | typeAExitSevenHandoff
  /-- Node `[107]`, no arm — the entry of node `[109]`: no high-degree decorated
  handoff fan envelope is produced at any visible port of any saturated receiver
  of any Type A support, so exit `(7)` is not the exit this branch realizes and
  the saturated exit list continues at exit `(8)`, the route-8 residual of
  `def:typeA-silent-core-residual`. -/
  | typeAExitSevenFree
  | coldFailureCycle
  | coldFailureDefect
  | coldFailureCompression
  | coldFailureHandoff
  | coldFailureRouting
  | coldExchangeBound
  | coldWindowLedgerSplit
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
  /-- Node `[153]`: a positive current-residual bounded-germ family. -/
  | coldGermCandidates
  | coldSelectedBranchExcess
  | coldAmbientCubicStubExcess
  | coldHandoffTransfer
  | coldGermExtraction
  | coldPositiveGerm
  | coldGermRouted
  | coldTerminalResidual
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
  /-- Node `[72]`/`[81]`, yes arm: the selected canonical Type B component has
  a pairwise-disjoint choice from the finite candidate family at every assigned
  high centre. -/
  | typeBB2Choice
  /-- The B2-success arm: the selected canonical piece carries the one disjoint
  candidate ledger, its exact augmented-ledger refinement, the inherited Type A
  hygiene of every remaining component, and the grouped exit-`(7)` handoff
  coverage used by B2(d). -/
  | typeBDisjointLedger
  /-- Node `[76]`/`[85]`, Step 1: every selected B2 fan entry is a certified
  candidate with nonnegative local augmented charge, and the selected entry sum
  is therefore nonnegative on the same canonical ledger. -/
  | typeBSelectedFanCharge
  /-- Node `[72]`/`[81]`, no arm — the entry of `[73]`/`[83]`: B2's
  disjoint-carrier clause fails on some assigned support, which by
  `lem:typeB-bridge-to-overlap` carries a minimal Type B overlap obstruction of
  `def:typeB-overlap-obstruction`.  The fact records the obstruction, not the
  bare failure: the minimality is what the fan-mass accounting consumes. -/
  | typeBOverlapObstruction
  /-- Nodes `[73]`/`[75]`: the fan-mass bound instantiated at the certificate
  residual selected by the incoming ledger. -/
  | fanCertificateResidualMass
  /-- Nodes `[83]`/`[84]`: the fan-mass bound instantiated at the selected
  minimal overlap obstruction. -/
  | typeBOverlapObstructionMass
  /-- Nodes `[76]`/`[85]`: the fan-mass bound instantiated at the selected
  failure of the disjoint B2 ledger. -/
  | typeBExclusionResidualMass
  /-- Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts
  for certificate residuals, overlap obstructions, and grouped decorated
  envelope residuals. -/
  | typeBBridgeMass
  /-- `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been
  extracted into the Type A ledger, the remaining Type B bridge residual mass is
  paid by the assigned high-centre surplus. -/
  | typeBBridgeSublinear
  /-- `thm:branch-kill`: outside the explicit residual classes, the
  large-budget negative-support branch has been closed on the current exact
  residual.  The explicit Type B bridge and route-`8` continuations remain
  separate ledger facts. -/
  | branchKillClosed
  /-- Node `[76]`/`[85]`: the Type B B-ledger charge implication read from the
  selected disjoint ledger. -/
  | typeBExclusionCharge
  /-- Node `[76]`/`[85]`, closed arm: the selected Type B ledger gives
  nonnegative net charge. -/
  | typeBExcluded
  /-- Node `[76]`/`[85]`, surviving arm: the Type B exclusion hypotheses are not
  all discharged on the selected B2 branch. -/
  | typeBExclusionResidual
  /-- Node `[101]`, yes arm: on the exact selected visible package after exits
  `(1)`, `(2)`, and `(3)` are absent, some canonical Q1--Q4 exit-`(4)` witness
  is target-defective and its declared support contains one of that package's
  selected visible unpeeled loads. -/
  | typeAExitFour
  /-- Node `[102]`: the exit-`(4)` witness has been charged to the peeling
  ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load
  condition and dropping the residual load by one. -/
  | typeAExitFourPeeled
  /-- `lem:typeA-saturated-handoff`, finite exit-`(4)` descent from the exact
  current saturated receiver/peeling state. -/
  | typeAExitFourFiniteDescent
  /-- `lem:typeA-exit4-residual-routing`, visible arm at the exact current
  saturated receiver/peeling state. -/
  | typeASaturatedHandoffVisible
  /-- `lem:typeA-exit4-residual-routing`, silent-excess arm at the exact
  current saturated receiver/peeling state. -/
  | typeASaturatedHandoffSilent
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
  /-- Node `[101]`, no arm: the exact selected visible package carries no
  target-defective Q1--Q4 exit-`(4)` witness supporting one of its selected
  visible unpeeled loads. -/
  | typeAExitFourFree
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
  /-- Node `[107]`, yes arm: the selected saturated-handoff residual, after
  exits `(4)`--`(6)` have failed, produces the exit-`(7)` decorated handoff
  envelope.  The admissibility interface is committed separately at `[108]`. -/
  | typeAExitSevenProduced
  /-- Node `[109]`, the route-8 arm: the incoming selected Type A residual has
  denied exit `(7)` and therefore continues to the route-8 accounting segment.
  The fact is a ledger refinement of the same residual state, not a secondary
  route-8 object. -/
  | route8Residual
  /-- Node `[110]`, exit `(8)`: the selected route-8 residual satisfies the
  silent-core residual profile.  This is a semantic fact about the selected
  residual state, not an indexed carrier or basin transport object. -/
  | route8ResidualProfile
  /-- Node `[111]`: the selected route-`8` residual profile lies on the
  large-budget branch extracted by the global squeeze. -/
  | route8GlobalSqueeze
  /-- Node `[112]`: the selected route-`8` residual carries the basin-burden
  lower side of `lem:typeA-route8-burden`. -/
  | route8BasinBurden
  /-- Node `[113]`: the same selected route-`8` residual carries the
  large-budget Type A deficit lower side. -/
  | route8LargeBudgetDeficit
  /-- Node `[114]`: canonical minimal carrier-core facts for every declared
  reading of the selected route-`8` residual. -/
  | route8CarrierCore
  /-- Nodes `[115]`--`[116]`: zero/one essential carrier cores activate the
  selected trace-basin minimality alternatives, hence the branch returns to
  exits `(4)`--`(7)` rather than continuing as route `8`. -/
  | route8SmallCoreCollapse
  /-- Node `[117]`: the private-carrier squeeze produces a two-carrier entry
  from the selected indexed essential-core family. -/
  | route8TwoCarrierReduction
  /-- Node `[118]`: a selected two-carrier essential-core entry carries the
  carrier-deletion target-defect witnesses and declared forgotten coordinates
  required by the Q5 clause of exit `(4)`. -/
  | route8CarrierDeletionWitnesses
  /-- Nodes `[119]`--`[120]`: the no-two-carrier branch gives the private
  essential-carrier budget against the selected route-`8` carrier supply. -/
  | route8PrivateCarrierBudget
  /-- Nodes `[121]`--`[122]`: the no-two-carrier branch contradicts the
  route-`8` burden/deficit and registered rate facts. -/
  | route8NoTwoCarrierContradiction
  /-- Node `[123]`: pressure descent join.  The selected route-`8` branch now
  carries both the finite exit-`(4)` descent fact and the carrier-reduction
  contradiction, so any survivor is the terminal two-carrier obstruction sent
  to node `[124]`. -/
  | route8PressureDescent
  /-- Node `[123]`, terminal survivor arm: the incoming pressure residual still
  presents a terminal two-carrier route-`8` obstruction to node `[124]`. -/
  | route8TerminalResidual
  /-- Node `[124]`: the terminal two-carrier route-`8` no-go.  Carrier-deletion
  witnesses become canonical Q5 exit-`(4)` witnesses, contradicting the
  no-exit-`(4)` fact of the same true route-`8` residual. -/
  | route8TerminalNoGo
  /-- `thm:large-budget-route8-only`, terminal route-`8` survivor closed by
  the node `[124]` no-go. -/
  | largeBudgetRoute8Closed
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
  /-- Node `[132]`, blocker arm of `lem:sparse-pair-dependence-exit` with
  `lem:mixed-sparse-spine-dependence` and
  `prop:sparse-pair-independence-dichotomy`: no sparse surplus exit settles the
  dependence, so at an object admitting no proper-support replacement a
  rank-reducing attempted determination exhibits the blocker of type (d) or (e)
  as concrete separated realizations, and the declared family attains full
  target rank.  This is the arm the canonical blocker ledger `[134]` is
  levied on. -/
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
  /-- Node `[139]`, yes arm: the overloading token of node `[137]` lies in
  `𝔗_W`, so the branch enters the window-incidence audit `[140]`. -/
  | windowClassOverload
  /-- Node `[139]`, no arm: no overloading token lies in `𝔗_W`, so the branch
  falls through to node `[141]`. -/
  | windowClassAbsent
  /-- Node `[141]`, yes arm: the overloading token lies in `𝔗_R`, so the branch
  enters the remainder-surplus audit `[142]`. -/
  | remainderClassOverload
  /-- Node `[141]`, no arm: no overloading token lies in `𝔗_R` either, so the
  branch enters the primitive-carrier audit `[143]`. -/
  | remainderClassAbsent
  /-- Node `[140]`, the window-incidence geometric audit: a token of `𝔗_W` whose
  load exceeds `Cap_hom(L_geom)` carries a role-homogeneous `L_geom`-matching or
  `L_geom`-star, at the counted routing-label alphabet of
  `def:same-token-routing-germs`. -/
  | windowIncidenceAudit
  /-- Node `[142]`, the remainder-surplus geometric audit, at `𝔗_R`. -/
  | remainderSurplusAudit
  /-- Node `[143]`, the primitive-carrier geometric audit, at `𝔗_prim`. -/
  | primitiveCarrierAudit
  /-- Node `[143]`'s own class verdict: the overloading token lies in `𝔗_prim`.
  It is *derived* at that node from node `[137]`'s overload and the two negative
  arms of `[139]` and `[141]`, because `class(t)` has three values. -/
  | primitiveClassOverload
  /-- `cor:quantitative-homogeneous-overload`: the forced role-homogeneous
  pattern scale `K_hom(G) ≥ ψ(N_*(G)/(Q_st(8n+σ(G))))`, cleared of division.
  Committed on each of the three audit arms, because it is what makes the audit
  a quantitative verdict rather than a bare alternative. -/
  | quantitativeOverload
  /-- Node `[144]`, the tested half of
  `thm:homogeneous-overload-geometric-closure`: no capacity token of the object
  supports a role-homogeneous same-token `L_geom`-matching or `L_geom`-star, at
  the counted routing-label alphabet.  This is the subbranch the manuscript's
  fixed caps `L_W = L_R = L_P = L_geom` hold on. -/
  | homogeneousCapsHold
  /-- Node `[144]`, the bottleneck arm: some capacity token *does* support such
  a pattern.  `lem:same-token-bottleneck-routing` reads it as a sparse surplus
  exit or as decorated Type B handoff fan data. -/
  | homogeneousBottleneckPattern
  /-- Node `[144]`, the bottleneck arm's own fact:
  `thm:homogeneous-overload-geometric-closure`'s first assertion, which is
  `lem:same-token-bottleneck-routing` at every declared routed bottleneck. -/
  | bottleneckRouting
  /-- Node `[144]`, the bottleneck arm's Type B handoff fact: every declared
  routed bottleneck produces admissible decorated Type B handoff fan data. -/
  | typeBHandoff
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
  The witnesses are derived from `LiveHotWindow` on the incoming residual;
  they are not supplied as routing data. -/
  | hotColdPartition
  /-- Node `[130]`, blocked/dependent arm: a concrete `Π`, its declared
  response family `ℛ_Π`, and the rank-reducing attempted quotient consumed by
  node `[132]`. -/
  | dependentPairFamily
  /-- Node `[130]`, independent arm for the same concrete full response family. -/
  | independentPairFamily
  /-- Node `[131]`, `lem:mixed-sparse-spine-dependence` on the concrete
  baseline spine family and full pair-response schedule. -/
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
  deriving DecidableEq

/-- **`𝒲₂(R)`**: the raw internal length-two curvature tests carried by the
remainder a packing leaves.  This is the family whose rank
`def:curvature-target-rank` takes, and `internalWedgeFamily_card` says it has
exactly `W₂(R)` members. -/
noncomputable abbrev remainderCurvatureTests (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Finset (object.InternalWedge (object.remainderSupport packing)) :=
  object.internalWedgeFamily (object.remainderSupport packing)

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
    (test : object.InternalWedge (object.remainderSupport packing))
    (determiners : Set
      (object.InternalWedge (object.remainderSupport packing)))
    (quotient : remainderQuotient data object packing)
    (supportData : Finset
      (object.InternalWedge (object.remainderSupport packing))) : Prop := by
  classical
  exact
    let family := remainderCurvatureTests object packing
    test ∈ family ∧ determiners ⊆ (↑family : Set _) ∧ determiners.Finite ∧
      test ∉ determiners ∧ quotient.toRankQuotient.FunctionalOn ↑family ∧
        quotient.toRankQuotient.RankReducingOn ↑family ∧
          quotient.toRankQuotient.Determines test determiners ∧
            supportData = family ∧
              ∀ coordinate ∈ supportData,
                Graph.FiniteObject.internalWedgeSupport
                    (region := object.remainderSupport packing) coordinate ⊆
                  quotient.support

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
    (object.positiveDeficiency (object.remainderSupport packing) data.threshold)
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

/-- `lem:curv-enum` at node `[21]`: the three exact certified counts and their
flatness entropy cost.

The witnesses are read from the registered `(1,1)` row itself.  Its semantic
certificate proves that they are exactly the finite safe, curvature-positive,
and flat enumerations.  Thus the EG presentation reduces these witnesses to
the manuscript's displayed values without copying any numeral into the
strategy row. -/
def BarrierEnumerationStatement (data : Data.{u}) : Prop :=
  let presentation := data.windowBarrier
  letI := presentation.indexFintype
  let row := data.curvatureBarrierRow
  let left := presentation.table.counts.leftLength row
  let right := presentation.table.counts.rightLength row
  ∃ safe curvaturePositive flat : Nat,
    safe = presentation.table.counts.storedSafe row ∧
    curvaturePositive = safe - flat ∧
    flat = presentation.table.counts.storedFlat row ∧
    safe = presentation.profile.safeCount left right ∧
    curvaturePositive = presentation.profile.obstructedCount left right ∧
    flat = presentation.profile.flatCount left right ∧
    Real.logb 2 ((safe : ℝ) / flat) =
      Real.logb 2
        ((presentation.table.counts.storedSafe row : ℝ) /
          presentation.table.counts.storedFlat row)

/-- A packed window is live-hot exactly when its declared singleton window
package is retained at every selected scale. -/
def LiveHotWindow (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (window : Finset object.Vertex) : Prop :=
  object.IsWindowPacking data.windowOrder {window} ∧
    let bits := data.windowRate * data.separatedScaleCount object.vertexCount
    let family := object.windowTargetFamily bits (object.windowSupport {window})
    (∀ declared : Graph.DeclaredQuotient
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object family
        object.windowTargetSupport,
      declared.toRankQuotient.FunctionalOn ↑family →
        declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
    2 ^ bits ≤ Graph.skeletonBudget object

/-- The manuscript fixes one maximal packing before splitting it.  This is the
canonical finite choice of that packing, hence every later key names the same
family without transporting a witness outside the ledger. -/
noncomputable def canonicalWindowPacking (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) :=
  Classical.choose (object.exists_windowPacking_card_eq data.windowOrder)

noncomputable def canonicalHotWindows (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  exact (canonicalWindowPacking data object).filter (LiveHotWindow data object)

noncomputable def canonicalColdWindows (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  exact (canonicalWindowPacking data object).filter
    (fun window => ¬ LiveHotWindow data object window)

/-- The hot/cold partition created at node `[22]`.  Both parts are defined
inside the selected maximal packing; the equivalences prevent a consumer from
substituting an arbitrary partition. -/
def IsHotColdWindowPartition (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing hot cold : Finset (Finset object.Vertex)) : Prop :=
    object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    (∀ support : Finset object.Vertex,
      object.InducesWindow data.windowOrder support →
        ∃ member ∈ packing, ¬ Disjoint support member) ∧
    (∀ window, window ∈ hot ↔
      window ∈ packing ∧ LiveHotWindow data object window) ∧
    (∀ window, window ∈ cold ↔
      window ∈ packing ∧ ¬ LiveHotWindow data object window) ∧
    Disjoint hot cold ∧
    ∀ window, window ∈ packing ↔ window ∈ hot ∨ window ∈ cold

def HotColdWindowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  IsHotColdWindowPartition data object
    (canonicalWindowPacking data object)
    (canonicalHotWindows data object)
    (canonicalColdWindows data object)

def BarrierCapStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      (∀ support : Finset object.Vertex,
        object.InducesWindow data.windowOrder support →
          ∃ member ∈ packing, ¬ Disjoint support member) ∧
    2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
          packing.card) ≤
      Graph.skeletonBudget object ∧
    ∀ family : Finset Nat, object.edgeCount ∈ family →
      Graph.skeletonBudget object ≤
        Graph.variableEdgeBudget object.vertexCount family

def BarrierOverflowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      (∀ support : Finset object.Vertex,
        object.InducesWindow data.windowOrder support →
          ∃ member ∈ packing, ¬ Disjoint support member) ∧
    Graph.skeletonBudget object <
      2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        packing.card)

/-- Node `[145]`: the hot/cold interface on the literal post-spine residual.
It fixes the maximal packing together with the canonical live window package
already committed by the predecessor.  Later nodes decide the route-8 and
live-hot alternatives; this fact performs neither decision. -/
def ColdWindowLedgerStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  HotColdWindowStatement data object

/-- The external-stub count of an ambient baseline-degree window.  For the
Erdős presentation this evaluates to `15`; no numerical value is written into
the strategy. -/
def coldExternalStubCount (data : Data.{u}) : Nat :=
  data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)

/-- The exact finite bit rate used by the near-cubic density comparison. -/
def coldWindowBitRate (data : Data.{u}) (object : Graph.FiniteObject.{u}) : Nat :=
  2 * (data.windowRate * data.separatedScaleCount object.vertexCount)

/-- The exact finite skeleton allowance; its two summands are the baseline
degree mass and the registered sublinear surplus threshold. -/
def coldSkeletonAllowance (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Nat :=
  (Graph.dyadicScaleCount object + 1) *
    (data.threshold * object.vertexCount +
      data.surplusThreshold object.vertexCount)

def ColdRoute8BelowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.ColdCorridor.TauBelow (coldExternalStubCount data) 3 13
    (canonicalWindowPacking data object).card object.vertexCount

def ColdRoute8AtOrAboveStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ Graph.ColdCorridor.TauBelow (coldExternalStubCount data) 3 13
    (canonicalWindowPacking data object).card object.vertexCount

def ColdHotEntropyOverflowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldSkeletonAllowance data object <
    coldWindowBitRate data object * (canonicalHotWindows data object).card

def ColdHotEntropyCapStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldWindowBitRate data object * (canonicalHotWindows data object).card ≤
    coldSkeletonAllowance data object

/-- `lem:hot-failure-cold-mass`, with logarithms and division cleared. -/
def ColdMassStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldWindowBitRate data object * (canonicalWindowPacking data object).card ≤
    coldWindowBitRate data object * (canonicalColdWindows data object).card +
      coldSkeletonAllowance data object

/-- A cold window is ambient-baseline exactly when every one of its vertices
has the registered baseline degree. -/
def AmbientCubicWindow (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (window : Finset object.Vertex) : Prop :=
  ∀ vertex ∈ window, object.degree vertex = data.threshold

/-- `def:surviving-cold-branch`'s `o(n)` assertion in exact finite form: the
non-ambient-cubic loss is charged injectively to degree surplus. -/
noncomputable def ColdAmbientCubicStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  exact cold.card ≤ cubic.card + object.degreeSurplus data.threshold ∧
    object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount

/-- `lem:cold-window-stub-excess`, subtraction-free and specialized to the
canonical cold family. -/
noncomputable def ColdStubExcessStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let perWindow := Graph.ColdCorridor.branchExcessOf
    (coldExternalStubCount data)
  exact perWindow * cold.card ≤
    perWindow * cubic.card + perWindow * object.degreeSurplus data.threshold

/-- `lem:cold-germ-extraction` on the current residual.  The selected
half-edge count pays for an actual candidate family; the framework-local
greedy extraction then returns a positive disjoint family. -/
noncomputable def ColdGermCandidatesStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  exact ∃ candidates disjointFamily : Finset
      (Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object),
      Graph.ColdCorridor.CandidateGermFamily data.coldSignature data.threshold
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object candidates ∧
      Graph.ColdCorridor.ExtractedGermFamily data.coldSignature data.threshold
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object candidates disjointFamily ∧
      let perWindow := Graph.ColdCorridor.branchExcessOf
        (coldExternalStubCount data)
      perWindow * cubic.card ≤
        candidates.card + perWindow * object.degreeSurplus data.threshold

/-- Node `[152]`: the scalar branch-excess witness for the canonical cold
family. -/
def ColdSelectedBranchExcessStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ packing hot cold : Finset (Finset object.Vertex),
    IsHotColdWindowPartition data object packing hot cold →
    ∃ excess : Nat,
      excess = Graph.ColdCorridor.branchExcessOf
        (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
          cold.card

/-- Node `[151]`: the scalar ambient-cubic estimate for the canonical cold
family. -/
def ColdAmbientCubicStubExcessStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ packing hot cold : Finset (Finset object.Vertex),
    IsHotColdWindowPartition data object packing hot cold →
    ∃ excess : Nat,
      excess = Graph.ColdCorridor.branchExcessOf
        (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
          cold.card
/-- First-failure routing specialized to the current residual's committed cold
family.  The corridor quantification ranges only over the current object and is
paired with the exact `[152]` witness that activates the extraction. -/
def ColdFailureRoutingStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ColdAmbientCubicStubExcessStatement data object ∧
  ∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment),
    Function.Injective index →
      Graph.ColdCorridor.Corridor.TerminalCorridor corridor data.coldSignature ∨
        Graph.ColdCorridor.Corridor.RepeatedState corridor presentation index

/-- The exchange bound for the same current-residual first-failure routing. -/
def ColdExchangeBoundStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ColdFailureRoutingStatement data object ∧
  ∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component),
    Graph.ColdCorridor.Corridor.TerminalCorridor corridor data.coldSignature →
      corridor.statesRead + Graph.ColdCorridor.interfaceBudget data.coldSignature ≤
        Graph.ColdCorridor.exchangeBound data.coldSignature

attribute [instance] Data.boundaryProfileFintype

/-! ## The exit-`(7)` handoff envelope, at the spine's registered data

The three parameters `def:decorated-fan-envelope` is quantified over are fixed
here once, so the node's two arms, its row and its fixture all read the same
predicate.

*The high-degree predicate* is `lem:typeA-cubic-switch-absorption`'s own
conclusion `d_G(z) ≥ 4` at a surviving first separator.  It is the count of
incidences the separation uses — the root incidence and the two next incidences
— strictly exceeded; it is not a registered baseline, and the registered
`threshold` is deliberately not written here.

*The absorbing predicate* is `def:typeB-fan-safe` clause (ii), the label
collision of `lem:labels`: exit `(3)`, which the branch reaching node `[107]`
has already denied and which the row therefore reads rather than restates.

*The two admissibility predicates* are node `[14]`'s hereditary
target-uncompressibility and the `P₁₃`-freeness of the counted core. -/

/-- `V_{≥4}(G)` at a surviving first separator: `lem:typeA-cubic-switch-absorption`. -/
abbrev handoffHighDegree (object : Graph.FiniteObject.{u}) :
    object.Vertex → Prop :=
  fun vertex => 3 < object.degree vertex

/-- **`def:typeB-fan-safe` clauses (ii)--(v)**, at the registered data.
`lem:typeA-high-degree-handoff` reads them off the exit list: *"failures of the
other four fan-safe conditions are exactly the label, target-defect,
target-compression, and delocalization exits already removed before exit (7)"*.
The exit `(3)` label clause is the only local fan predicate.  The denials of
exits `(4)`, `(5)`, and `(6)` are ledger facts in `SelectedNoExitSixWith`, not
secondary route-8 objects smuggled through this predicate. -/
abbrev handoffAbsorbing (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    object.Vertex → object.Vertex → object.Vertex → Prop :=
  fun _centre _first _second =>
    Graph.WindowLabelCollision.LabelCollision object data.windowOrder
      data.LengthOK packing

/-- `cor:uncompressible` at node `[14]`, as the envelope's admissibility reads
it. -/
abbrev handoffUncompressible (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex → Prop :=
  fun support =>
    ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support

/-- The counted core is `P₁₃`-free. -/
abbrev handoffWindowFree (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    Finset object.Vertex → Prop :=
  fun support =>
    ∀ window : Finset object.Vertex, window ⊆ support →
      ¬ object.InducesWindow data.windowOrder window

/-- **A decorated handoff fan envelope is produced at a support.**  The test
node `[107]` splits on: `def:decorated-fan-envelope`'s data, with the Type A
support as the counted core and at least one high-degree decoration. -/
def HandoffProduced (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty

/-- **The envelope produced is admissible Type B fan-envelope data**
(`lem:decorated-fan-admissibility`).  This is the handoff interface, and by
`rem:typeA-typeB-stratification` it uses no conclusion of
`lem:typeB-exclusion`. -/
def HandoffAdmissible (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

/-- Exit `(6)` at the selected Type A support.

The delocalizing declared response entry is not a free route-8 object: it is
presented at the same support `piece` currently carried by the ledger branch. -/
def ExitSixDelocalizes (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) : Prop :=
  ∃ presented : Graph.Route8.PresentedEntry object,
    presented.support = piece ∧
      Nonempty
        (Graph.Route8.Delocalization
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) presented)

/-- The exact selected saturated Type A state after exits `(4)`, `(5)`, and
`(6)` have failed, with one additional local clause on its selected packing and
support.  This is a fact-schema abbreviation only: rows still read it from the
incoming `ExactLedger` and commit descendants through `Decision.run` or
`factOnly`. -/
abbrev SelectedNoExitSixWith (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ((∃ package :
                      Graph.ExitFour.VisibleFourUnpeeledPackage piece
                        data.threshold data.dischargeScale receiver peeled,
                    ¬ ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver peeled,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside peeled,
                        witness.load = load) ∨
                    (Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ¬ ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                          data.threshold data.dischargeScale receiver peeled)) ∧
                  (¬ ∃ support : Finset object.Vertex,
                    Graph.Strategy.InterfaceReplacement.CompressibleSupport
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK) object support) ∧
                  ¬ ExitSixDelocalizes data object piece ∧
                  extra packing piece

/-- The same selected no-exit-`(6)` residual, but with the selected receiver
and current peeling set exposed to the next local route-`8` fact.  This is a
schema helper only: the framework still carries the full `ExactLedger`, and
rows still read the predecessor facts by key. -/
abbrev SelectedNoExitSixReceiverWith (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      (piece : Finset object.Vertex) → object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ((∃ package :
                      Graph.ExitFour.VisibleFourUnpeeledPackage piece
                        data.threshold data.dischargeScale receiver peeled,
                    ¬ ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver peeled,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside peeled,
                        witness.load = load) ∨
                    (Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ¬ ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                          data.threshold data.dischargeScale receiver peeled)) ∧
                  (¬ ∃ support : Finset object.Vertex,
                    Graph.Strategy.InterfaceReplacement.CompressibleSupport
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK) object support) ∧
                  ¬ ExitSixDelocalizes data object piece ∧
                  extra packing piece receiver peeled

/-- The selected silent-core residual profile at exit `(8)`.  It exposes the
same selected saturated residual state as `[109]`, with the selected receiver
and current peeling set in scope for later semantic facts, and asserts that no
decorated handoff fan is produced. -/
abbrev SilentCoreResidualProfile (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun packing piece _receiver _peeled =>
      ¬ HandoffProduced data object packing piece)

/-- Node `[110]` from node `[109]`: once exit `(7)` is denied on the selected
no-exit-`(6)` residual, the receiver-exposed silent-core residual profile is
the same residual statement with the selected local data brought into scope. -/
theorem silentCoreResidualProfile_of_route8Residual
    {data : Data.{u}} {object : Graph.FiniteObject.{u}}
    (residual :
      SelectedNoExitSixWith data object
        (fun packing piece => ¬ HandoffProduced data object packing piece)) :
    SilentCoreResidualProfile data object := by
  obtain ⟨packing, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, routing,
    noCompression, noDelocalization, noHandoff⟩ := residual
  exact ⟨packing, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, routing,
    noCompression, noDelocalization, noHandoff⟩

/-- The exact finite exit-`(4)` descent theorem committed before the route-`8`
arm.  This is a schema abbreviation only: the fact is still read from the
ledger by key and transported by the framework. -/
abbrev TypeAExitFourFiniteDescentFact (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ startPeeled : Finset object.Vertex,
                startPeeled ⊆ object.routedLoads piece data.threshold
                    receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver startPeeled ∧
                  ∀ Retained Terminal : Finset object.Vertex → Prop,
                    Retained startPeeled →
                    (∀ peeled,
                      peeled ⊆ object.routedLoads piece data.threshold
                          receiver →
                      Retained peeled →
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled →
                      Terminal peeled ∨
                        ∃ load ∈ object.routedLoads piece data.threshold
                            receiver,
                          ∃ fresh : load ∉ peeled,
                            Retained (Finset.cons load peeled fresh)) →
                    (∃ finalPeeled ⊆
                        object.routedLoads piece data.threshold receiver,
                      Retained finalPeeled ∧ Terminal finalPeeled) ∨
                    (∃ finalPeeled ⊆
                        object.routedLoads piece data.threshold receiver,
                      Retained finalPeeled ∧
                        ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                          data.dischargeScale receiver finalPeeled)

/-- Residual C, in the exact schema committed earlier by the spine. -/
abbrev LargeBudgetResidual (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ((∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        jointPackageDemand data object packing ≤ Graph.skeletonBudget object) ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
          data.windowOrder data.threshold
          (object.positiveDeficiency (object.remainderSupport packing)
            data.threshold)
          (object.remainderSupport packing).card)

/-- Node `[111]`: the selected route-`8` profile lies on the large-budget
branch. -/
abbrev Route8GlobalSqueeze (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  SilentCoreResidualProfile data object ∧ LargeBudgetResidual data object

/-- Node `[112]`, in the cleared form already proved by the selected
silent-excess count: `|X| ≤ S_sil^exc(X) + s·def⁺(X)`, i.e.
`S_sil^exc(X) ≥ s·D_A(X)`.

The first conjunct ties the statement to the incoming true route-`8` residual;
the second conjunct is exactly the support-local burden fact committed earlier
on the same ledger prefix. -/
abbrev Route8BasinBurden (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8GlobalSqueeze data object ∧
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ component ∈ object.canonicalPieces
            (object.remainderSupport packing),
          let piece := object.pieceSupport
            (object.remainderSupport packing) component
          object.NegativeNetCharge piece data.threshold
              data.dischargeScale ∧
            object.ambientSurplus piece data.threshold = 0 ∧
            ∃ receiver : object.Vertex,
              object.IsReceiver piece data.threshold receiver ∧
                object.Saturated piece data.threshold data.dischargeScale
                  receiver ∧
                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                    data.dischargeScale receiver ∅ ∧
                piece.card ≤
                  (∑ other ∈ object.receivers piece data.threshold,
                    (Graph.VisibleEntry.silentExcess object piece
                      data.threshold data.dischargeScale other).card) +
                    data.dischargeScale *
                      object.positiveDeficiency piece data.threshold

/-- Node `[113]`: the selected route-`8` residual has both the basin burden and
the large-budget deficit branch. -/
abbrev Route8LargeBudgetDeficit (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8BasinBurden data object ∧ LargeBudgetResidual data object

/-- Node `[114]`: the carrier-core facts committed as an ordinary ledger fact
on top of the selected `[113]` route-`8` residual. -/
abbrev Route8CarrierCore (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8LargeBudgetDeficit data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ presented : Graph.Route8.PresentedEntry object,
      (presented.toEntry (Graph.HasCycleWithLength data.LengthOK)).CarrierCoreFacts

/-- Nodes `[115]`--`[116]`: the small-core-collapse facts committed after
`[114]` as an ordinary ledger fact. -/
abbrev Route8SmallCoreCollapse (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8CarrierCore data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ presented : Graph.Route8.PresentedEntry object,
      (presented.toEntry
        (Graph.HasCycleWithLength data.LengthOK)).SmallCoreCollapseFacts

/-- Node `[117]`: the selected two-carrier-reduction stage, as an ordinary
fact over the current route-`8` residual. -/
abbrev Route8TwoCarrierReduction (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8SmallCoreCollapse data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ {Index : Type u} [DecidableEq Index]
      (entries : Finset Index)
      (core : Index → Finset (Sym2 object.Vertex))
      (supply : Finset (Sym2 object.Vertex))
      (core_subset : ∀ index ∈ entries, core index ⊆ supply)
      {threshold discharge ambient : Nat},
        ambient ≤ entries.card + discharge * supply.card →
        ((threshold + 1) * discharge + 1) * supply.card <
          (threshold + 1) * ambient →
        ∃ index ∈ entries,
          Graph.Route8.IndexedTwoCarrierCore entries core threshold index

/-- Node `[118]`: selected carrier-deletion witnesses, committed after the
two-carrier stage without a terminal-entry wrapper. -/
abbrev Route8CarrierDeletionWitnesses (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8TwoCarrierReduction data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ (presented : Graph.Route8.PresentedEntry object)
      {Index : Type u} [DecidableEq Index]
      (entries : Finset Index)
      (core : Index → Finset (Sym2 object.Vertex))
      {threshold : Nat} {index : Index},
        Graph.Route8.IndexedTwoCarrierCore entries core threshold index →
        core index =
          (presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)).essentialCore →
        let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
        Graph.Route8.TwoCarrierDeletionWitnesses (Target :=
          Graph.HasCycleWithLength data.LengthOK) entry.carriers
          entry.coordinates entry.car entry.state entries core threshold index

/-- Nodes `[119]`--`[120]`: the selected private-carrier budget stage on the
same route-`8` residual. -/
abbrev Route8PrivateCarrierBudget (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8CarrierDeletionWitnesses data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ {Index : Type u} [DecidableEq Index]
      (entries : Finset Index)
      (core : Index → Finset (Sym2 object.Vertex))
      (supply : Finset (Sym2 object.Vertex))
      (core_subset : ∀ index ∈ entries, core index ⊆ supply)
      {threshold : Nat},
        (∀ index ∈ entries,
          ¬ Graph.Route8.IndexedTwoCarrierCore entries core threshold index) →
        (threshold + 1) * entries.card ≤ supply.card

/-- Nodes `[121]`--`[122]`: the selected no-two-carrier contradiction stage. -/
abbrev Route8NoTwoCarrierContradiction (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8PrivateCarrierBudget data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ {Index : Type u} [DecidableEq Index]
      (entries : Finset Index)
      (core : Index → Finset (Sym2 object.Vertex))
      (supply : Finset (Sym2 object.Vertex))
      (core_subset : ∀ index ∈ entries, core index ⊆ supply)
      {threshold discharge ambient : Nat},
        ambient ≤ entries.card + discharge * supply.card →
        ((threshold + 1) * discharge + 1) * supply.card <
          (threshold + 1) * ambient →
        (∀ index ∈ entries,
          ¬ Graph.Route8.IndexedTwoCarrierCore entries core threshold index) →
        False

/-- Node `[123]`: the pressure-descent join fact.

This fact is deliberately not a route-`8` data carrier.  The row that commits
it reads the existing finite exit-`(4)` descent theorem and the carrier
reduction/no-two-carrier contradiction from the same `ExactLedger` prefix, and
publishes their semantic conjunction as the paper's pressure-descent survivor
state for node `[124]`. -/
abbrev Route8PressureDescent (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8NoTwoCarrierContradiction data object ∧
    TypeAExitFourFiniteDescentFact data object

/-- Node `[123]`, terminal-survivor arm: the surviving pressure residual
presents a terminal two-carrier route-`8` obstruction to node `[124]`.

This is an ordinary fact about the selected object.  It is read from the
incoming `ExactLedger` on a branch that claims the terminal survivor exists;
node `[124]` appends the no-go fact separately, and Core closes from the two
facts. -/
abbrev Route8TerminalResidual (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8PressureDescent data object ∧
    Route8CarrierDeletionWitnesses data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∃ presented : Graph.Route8.PresentedEntry object,
      let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
      ¬ Graph.Route8.TerminalTwoCarrierNoGoFacts
        (Graph.HasCycleWithLength data.LengthOK) entry.carriers
        entry.coordinates entry.car entry.car_subset entry.state

/-- Node `[124]`: terminal two-carrier route-`8` no-go.

This is the canonical Q5 carrier-deletion closure.  The fact reads the
pressure-descent survivor state and exposes the generic theorem that any
selected terminal two-carrier deletion quotient yields an exit-`(4)` witness,
contradicting the no-exit-`(4)` ledger fact. -/
abbrev Route8TerminalNoGo (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8PressureDescent data object ∧
    Route8CarrierDeletionWitnesses data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    ∀ presented : Graph.Route8.PresentedEntry object,
      let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
      Graph.Route8.TerminalTwoCarrierNoGoFacts
        (Graph.HasCycleWithLength data.LengthOK) entry.carriers
        entry.coordinates entry.car entry.car_subset entry.state

/-- The value schema of each spine fact, stated of the *object* alone.

Every spine fact is a statement about the selected graph, never about a side
payload carried beside it.  Making that explicit is what lets a fact transport
along a refinement by a rewrite: refinement is object equality.

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
      BarrierCapStatement data object
  | .barrierOverflow, object =>
      BarrierOverflowStatement data object
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
  | .exactResponseProfile, object =>
      -- `def:exact-response-profile` on the one concrete remainder inherited
      -- from `maximalPacking`.  Raw D4 coordinates all carry the common
      -- presence value `Unit`; exactness means their wedge labels remain
      -- distinct despite that equality of embedded numerical values.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          let support := object.remainderSupport packing
          let boundary :=
            Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support
          let piece :=
            Graph.Strategy.InterfaceReplacement.SupportAtom.piece object support
          let family := object.internalWedgeFamily support
          let profile :
              Graph.BoundaryDegreeProfile boundary ×
                (Graph.OutsideContext boundary → Prop) ×
                Finset (object.InternalWedge support) ×
                (object.InternalWedge support → Unit) :=
            (piece.boundaryDegreeProfile,
              (fun outside => Graph.HasCycleWithLength data.LengthOK
                (Graph.glue piece outside)), family, fun _ => ())
          profile.1 = piece.boundaryDegreeProfile ∧
            profile.2.1 = (fun outside =>
              Graph.HasCycleWithLength data.LengthOK (Graph.glue piece outside)) ∧
            profile.2.2.1 = family ∧
            (∀ coordinate ∈ profile.2.2.1, profile.2.2.2 coordinate = ()) ∧
            Set.InjOn (fun coordinate => coordinate)
              (↑profile.2.2.1 : Set (object.InternalWedge support)))
  | .admissibleRankQuotient, object =>
      -- `def:admissible-rank-quotient` on the exact response profile already
      -- selected for the concrete remainder.  Membership is exactly existence
      -- of the paper's declared quotient datum: its fields are the connected
      -- carrying support, boundary-degree fibre preservation, all-context
      -- target-completeness, and the proper/closed representative clauses.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          let support := object.remainderSupport packing
          let family := object.internalWedgeFamily support
          ∃ admissible :
              Core.TargetRank.RankQuotient.{u, u + 1}
                  (object.InternalWedge support) → Prop,
            ∀ quotient,
              admissible quotient ↔
                ∃ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object family
                    (Graph.FiniteObject.internalWedgeSupport (region := support)),
                  declared.toRankQuotient = quotient)
  | .functionalRankQuotient, object =>
      -- `def:functional-rank-quotient`: restrict the incoming admissible
      -- family, without changing its quotients, to the members satisfying the
      -- paper's finite functional-dependence axiom on the declared family.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          let support := object.remainderSupport packing
          let family := object.internalWedgeFamily support
          ∃ functional :
              Core.TargetRank.RankQuotient.{u, u + 1}
                  (object.InternalWedge support) → Prop,
            ∀ quotient,
              functional quotient ↔
                ((∃ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object family
                    (Graph.FiniteObject.internalWedgeSupport (region := support)),
                    declared.toRankQuotient = quotient) ∧
                  quotient.FunctionalOn ↑family))
  | .curvatureTargetRank, object =>
      -- `def:curvature-target-rank` only.  At the concrete remainder inherited
      -- from the functional-quotient fact, `independent` survives precisely
      -- when every functional admissible quotient remains label-injective on
      -- it.  Its cardinality is the finite maximum.  Circuit extraction is a
      -- separate later label and is deliberately absent here.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          let support := object.remainderSupport packing
          let family := object.internalWedgeFamily support
          ∃ independent ⊆ family,
            (∀ quotient : Core.TargetRank.RankQuotient.{u, u + 1}
                (object.InternalWedge support),
              ((∃ declared : Graph.DeclaredQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object family
                  (Graph.FiniteObject.internalWedgeSupport (region := support)),
                  declared.toRankQuotient = quotient) ∧
                quotient.FunctionalOn ↑family) →
              quotient.LabelInjectiveOn ↑independent) ∧
            independent.card =
              object.curvatureTargetRank
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) support ∧
            ∀ candidate ⊆ family,
              (∀ quotient : Core.TargetRank.RankQuotient.{u, u + 1}
                  (object.InternalWedge support),
                ((∃ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object family
                    (Graph.FiniteObject.internalWedgeSupport (region := support)),
                    declared.toRankQuotient = quotient) ∧
                  quotient.FunctionalOn ↑family) →
                quotient.LabelInjectiveOn ↑candidate) →
              candidate.card ≤ independent.card)
  | .targetRankCircuit, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          let support := object.remainderSupport packing
          let family := object.internalWedgeFamily support
          let ProperDependence := fun
              (test : object.InternalWedge support)
              (determiners : Set (object.InternalWedge support)) =>
            determiners.Finite ∧ test ∉ determiners ∧
              ∃ declared : Graph.DeclaredQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object family
                (Graph.FiniteObject.internalWedgeSupport (region := support)),
                declared.toRankQuotient.FunctionalOn ↑family ∧
                  declared.toRankQuotient.RankReducingOn ↑family ∧
                    declared.toRankQuotient.Determines test determiners
          ∃ independent ⊆ family,
            (∀ quotient : Core.TargetRank.RankQuotient.{u, u + 1}
                (object.InternalWedge support),
              ((∃ declared : Graph.DeclaredQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object family
                  (Graph.FiniteObject.internalWedgeSupport (region := support)),
                  declared.toRankQuotient = quotient) ∧
                quotient.FunctionalOn ↑family) →
              quotient.LabelInjectiveOn ↑independent) ∧
            independent.card =
              object.curvatureTargetRank
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) support ∧
            (∀ test ∈ family, test ∉ independent →
              ∃ determiners : Set (object.InternalWedge support),
                determiners ⊆ ↑independent ∧ ProperDependence test determiners) ∧
            ((¬ ∃ test ∈ family,
                ∃ determiners : Set (object.InternalWedge support),
                  determiners ⊆ ↑family ∧ ProperDependence test determiners) →
              ∀ quotient : Core.TargetRank.RankQuotient.{u, u + 1}
                  (object.InternalWedge support),
                ((∃ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object family
                    (Graph.FiniteObject.internalWedgeSupport (region := support)),
                    declared.toRankQuotient = quotient) ∧
                  quotient.FunctionalOn ↑family) →
                quotient.LabelInjectiveOn ↑family))
  | .curvatureRankDrop, object =>
      -- Any strict loss of raw curvature rank supplies the proper
      -- target-dependence routed by Branch D.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          remainderCurvatureTargetRank data object packing <
              remainderWedgeSupply object packing ∧
            let support := object.remainderSupport packing
            let family := object.internalWedgeFamily support
            ∃ test ∈ family,
              ∃ determiners : Set (object.InternalWedge support),
                determiners ⊆ ↑family ∧ determiners.Finite ∧
                  test ∉ determiners ∧
                    ∃ declared : Graph.DeclaredQuotient
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK) object family
                      (Graph.FiniteObject.internalWedgeSupport
                        (region := support)),
                      declared.toRankQuotient.FunctionalOn ↑family ∧
                        declared.toRankQuotient.RankReducingOn ↑family ∧
                          declared.toRankQuotient.Determines test determiners)
  | .curvatureFullRank, object =>
      -- This is the equality proved in the last paragraph of `lem:full-rank`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
            remainderCurvatureTargetRank data object packing =
              remainderWedgeSupply object packing)
  | .branchDependence, object =>
      -- Nodes `[33]`/`[35]`: choose the paper's determination certificate with
      -- inclusion-minimal connected support.  The determined coordinate is
      -- fixed during minimization, while its finite determining subfamily may
      -- vary.  A `remainderQuotient` is already a declared admissible quotient;
      -- its support/carries fields are the connected declared support data.
      by
        classical
        exact ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            remainderCurvatureTargetRank data object packing <
                remainderWedgeSupply object packing ∧
              ∃ test,
              let Supports := object.vertexFinset.powerset.filter
                fun candidateSupport =>
                  ∃ determiners quotient,
                    quotient.support = candidateSupport ∧
                      ∃ supportData,
                        DeterminationCertificate data object packing test
                          determiners quotient supportData
              ∃ determiners quotient supportData,
                DeterminationCertificate data object packing test determiners
                    quotient supportData ∧
                  ∀ smaller : Finset object.Vertex,
                    smaller ⊂ quotient.support →
                      ∀ narrower : remainderQuotient data object packing,
                        narrower.support = smaller →
                          ∀ narrowerDeterminers narrowerSupportData,
                            ¬ DeterminationCertificate data object packing test
                              narrowerDeterminers narrower narrowerSupportData
  | .contextUniversal, object =>
      -- Node `[36]`, yes: the single certificate chosen at `[33]` remains
      -- valid against every outside context.  The certificate and its
      -- same-coordinate inclusion-minimality identify exactly which quotient
      -- this branch fact concerns; the earlier strict-drop fact remains in the
      -- ExactLedger and is not copied here.
      by
        classical
        exact ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            ∃ test determiners quotient supportData,
              DeterminationCertificate data object packing test determiners
                  quotient supportData ∧
              (∀ smaller : Finset object.Vertex,
                smaller ⊂ quotient.support →
                  ∀ narrower : remainderQuotient data object packing,
                    narrower.support = smaller →
                      ∀ narrowerDeterminers narrowerSupportData,
                        ¬ DeterminationCertificate data object packing test
                          narrowerDeterminers narrower narrowerSupportData) ∧
              ∀ left right, Identified quotient left right →
                Graph.Response.ContextEquivalent
                  (Graph.HasCycleWithLength data.LengthOK) left right
  | .contextDefect, object =>
      -- Node `[36]`, no: the same selected certificate has a concrete pair of
      -- identified realizations separated by an outside context, exactly the
      -- paper's target-defective alternative.  Boundary-fibre preservation is
      -- part of admissibility and is not reproved or branched on here.
      by
        classical
        exact ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            ∃ test determiners quotient supportData,
              DeterminationCertificate data object packing test determiners
                  quotient supportData ∧
              (∀ smaller : Finset object.Vertex,
                smaller ⊂ quotient.support →
                  ∀ narrower : remainderQuotient data object packing,
                    narrower.support = smaller →
                      ∀ narrowerDeterminers narrowerSupportData,
                        ¬ DeterminationCertificate data object packing test
                          narrowerDeterminers narrower narrowerSupportData) ∧
              ∃ left right, Identified quotient left right ∧
                Graph.Response.TargetDefect
                  (Graph.HasCycleWithLength data.LengthOK) left right
  | .atomCompression, object =>
      -- Node `[38]` yes, the terminal `[39]`: the determination is certified
      -- without leaving `C`, which is case (ii) -- "it holds for every outside
      -- context already with support `C`".
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
              TargetCompleteAt data quotient ∧
                quotient.support ⊆ object.remainderSupport packing ∧
                  Graph.Strategy.InterfaceReplacement.ReplacementSupport
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object
                    quotient.support)
  | .delocalizedSupport, object =>
      -- Node `[40]`: case (iii)'s entry.  The certificate reaches outside `C`,
      -- so the connected support the determination needs strictly contains it.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
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
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ object.remainderSupport packing ∧
                  ∃ vertex,
                    vertex ∉ delocalizationSupport data object packing quotient ∧
                  Graph.Strategy.InterfaceReplacement.ReplacementSupport
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object
                    quotient.support)
  | .globalDelocalization, object =>
      -- Node `[43]`: `Z = G`.  The quotient is then a closed exact-profile
      -- quotient, which is the hypothesis of `lem:no-silent-global-smearing`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
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
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
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
      -- support predicate supplied by the incoming ledger, so a row cannot
      -- escape by naming its own; a row that is not handed off and not distinguishing is a
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
                (carrier (index left)) (carrier (index right))))
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
      -- a support already recorded in the incoming ledger transfers there.
      -- The cold row records only the local membership; it constructs no
      -- envelope object.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (Handoff : Finset object.Vertex → Prop)
        (segment : corridor.Segment),
        Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment →
          ∃ support, Handoff support ∧ corridor.head segment ∈ support)
  | .coldFailureRouting, object =>
      ColdFailureRoutingStatement data object
  | .coldExchangeBound, object =>
      ColdExchangeBoundStatement data object
  | .coldWindowLedgerSplit, object =>
      ColdWindowLedgerStatement data object
  | .coldRoute8Below, object =>
      ColdRoute8BelowStatement data object
  | .coldRoute8AtOrAbove, object =>
      ColdRoute8AtOrAboveStatement data object
  | .coldHotEntropyOverflow, object =>
      ColdHotEntropyOverflowStatement data object
  | .coldHotEntropyCap, object =>
      ColdHotEntropyCapStatement data object
  | .coldMass, object =>
      ColdMassStatement data object
  | .coldAmbientCubic, object =>
      ColdAmbientCubicStatement data object
  | .coldStubExcess, object =>
      ColdStubExcessStatement data object
  | .coldGermCandidates, object =>
      ColdGermCandidatesStatement data object
  | .coldSelectedBranchExcess, object =>
      ColdSelectedBranchExcessStatement data object
  | .coldAmbientCubicStubExcess, object =>
      ColdAmbientCubicStubExcessStatement data object
  | .barrierEnumeration, _object =>
      BarrierEnumerationStatement data
  | .windowPackageSeparated, object => by
      classical
      let barrier := data.windowBarrier
      letI := barrier.indexFintype
      let scales := data.separatedScaleCount object.vertexCount
      let safe := Core.Finite.CertifiedTableAggregation.safeProduct barrier.table
      let flat := Core.Finite.CertifiedTableAggregation.flatProduct barrier.table
      let bits := Nat.log2 ((safe ^ scales - 1) / flat ^ scales)
      exact ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            (∀ support : Finset object.Vertex,
              object.InducesWindow data.windowOrder support →
                ∃ member ∈ packing, ¬ Disjoint support member) ∧
            let Coordinate := Graph.DeclaredSignature.Coordinate
              object.Vertex (Fin bits × Finset object.Vertex)
            let package : Finset object.Vertex → Finset Coordinate := fun window =>
              Finset.univ.image fun bit =>
                Graph.DeclaredSignature.Coordinate.base
                  .windowLabel (bit, window) window
            let family := packing.biUnion package
            (∀ window ∈ packing, (package window).card = bits) ∧
              (∀ left ∈ packing, ∀ right ∈ packing, left ≠ right →
                Disjoint (package left) (package right)) ∧
              family.card = bits * packing.card ∧
              (∀ declared : Graph.DeclaredQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object family
                  Graph.DeclaredSignature.Coordinate.support,
                declared.toRankQuotient.FunctionalOn ↑family →
                  declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
              (∀ (BaselineCoordinate : Type u)
                  (baseline : Finset BaselineCoordinate)
                  (baselineSupport : BaselineCoordinate → Finset object.Vertex),
                (∀ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object baseline
                    baselineSupport,
                  declared.toRankQuotient.FunctionalOn ↑baseline →
                    declared.toRankQuotient.LabelInjectiveOn ↑baseline) →
                let combined := family.image Sum.inl ∪ baseline.image Sum.inr
                let combinedSupport : Sum Coordinate BaselineCoordinate →
                    Finset object.Vertex :=
                  Sum.elim Graph.DeclaredSignature.Coordinate.support
                    baselineSupport
                ∀ declared : Graph.DeclaredQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object combined
                    combinedSupport,
                  declared.toRankQuotient.FunctionalOn ↑combined →
                    declared.toRankQuotient.LabelInjectiveOn ↑combined)
  | .coldHandoffTransfer, object =>
      -- `lem:cold-corridor-first-failure` (iv), as a ledger transfer.  The
      -- support is already marked by the incoming ledger; this row does not
      -- allocate a handoff carrier.
      (∀ (windows component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (Handoff : Finset object.Vertex → Prop)
        (segment : corridor.Segment)
        (failure : Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor
          Handoff segment),
        ∃ support, Handoff support ∧ corridor.head segment ∈ support)
  | .coldGermExtraction, object =>
      -- `lem:cold-germ-extraction`, in ledger form on the current object.  The
      -- candidate family consists of actual bounded germs of this residual, so
      -- the overlap graph is the one on their literal supports.  No arbitrary
      -- `Germ` type, support-realization premise, disjoint-family carrier, or
      -- theorem bundle is exported.
      ColdExchangeBoundStatement data object ∧
        Graph.ColdCorridor.ColdGermExtractionLocal data.coldSignature
          data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
  | .coldPositiveGerm, _object =>
      ∀ (Germ : Type u) (_ : DecidableEq Germ)
        (candidates disjointFamily : Finset Germ)
        (perWindow coldCount branchExcess denominator slack : Nat),
        perWindow * coldCount ≤ branchExcess + slack →
          branchExcess ≤ candidates.card + slack →
            candidates.card ≤ disjointFamily.card * denominator →
              2 * slack < perWindow * coldCount →
                0 < disjointFamily.card
  | .coldGermRouted, object =>
      -- The length-changing germ conclusion obtained by eliminating G1 and G3
      -- and then reading the G2 route from the ledger.  The fact therefore
      -- carries the actual target-defect route, not just the intermediate
      -- `Distinguishing` predicate.
      ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
        germ.increment < 0 →
          germ.Distinguishing ∧
            ∀ (Profile : Type)
              (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
              ¬ Graph.Response.TargetComplete profile
                (Graph.HasCycleWithLength data.LengthOK)
                germ.piece germ.canonical
  | .coldTerminalResidual, object =>
      Graph.ColdCorridor.TerminalColdResidual data.coldSignature
        data.threshold data.LengthOK
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
  | .coldBranchClosed, object =>
      -- `thm:cold-branch-quantitative-closure`, in the form consumed by the
      -- cold oval: after the current residual's length-changing germs and
      -- same-interface table rows have been routed, no local terminal cold
      -- pattern remains on this residual.
      Graph.ColdCorridor.NoTerminalColdResidual data.coldSignature data.threshold
        data.LengthOK (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
  | .forcedCurvatureCost, object =>
      -- `cor:forced-curvature-cost` after substituting the exact equality
      -- proved by `lem:full-rank` into node `[30]`'s demand floor.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        data.curvatureCost *
              (data.threshold * (object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
            data.curvatureCost *
                remainderCurvatureTargetRank data object packing +
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
          (object.positiveDeficiency (object.remainderSupport packing)
            data.threshold)
          (object.remainderSupport packing).card)
  | .remainderEntropyLow, object =>
      -- Node `[50]`, no.  The exact negation, with the witness exhibited.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
            data.windowOrder data.threshold
            (object.positiveDeficiency (object.remainderSupport packing)
              data.threshold)
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
      -- Residual C.  The high-entropy arm reaches it through the exact
      -- skeleton comparison; the low-entropy arm is routed here unchanged, as `prop:two-budget` prescribes.
      LargeBudgetResidual data object
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
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            object.NegativeNetCharge
              (object.pieceSupport (object.remainderSupport packing) component)
              data.threshold data.dischargeScale)
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
  | .netChargeLarge, object =>
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale object.vertexCount
  | .netChargeSmall, object =>
      ¬ Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale object.vertexCount
  | .netChargeCap, object =>
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
          packing.card = object.windowPackingNumber data.windowOrder →
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
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            object.NegativeNetCharge
              (object.pieceSupport (object.remainderSupport packing) component)
              data.threshold data.dischargeScale)
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
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0)
  | .typeBHighSurplus, object =>
      -- Node `[62]`, yes -- node `[64]`, Type B: it carries some.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
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
      -- Node `[89]`, yes: the selected canonical Type A component retains an
      -- actual saturated receiver.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver)
  | .typeAUnsaturatedReceivers, object =>
      -- Node `[89]`, no -- node `[90]`: every receiver of that same selected
      -- canonical component satisfies `L(w) ≤ s·q(w) − 1`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            1 + object.routedLoad piece data.threshold receiver ≤
              data.dischargeScale *
                object.missingPorts piece data.threshold receiver)
  | .typeAUnsaturatedDischarge, object =>
      -- Node `[91]`, `lem:typeA-unsaturated-discharge`, on the same selected
      -- canonical component carried by node `[90]`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ component ∈ object.canonicalPieces
            (object.remainderSupport packing),
          let piece := object.pieceSupport
            (object.remainderSupport packing) component
          object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
            object.ambientSurplus piece data.threshold = 0 ∧
            piece.card ≤
              data.dischargeScale *
                object.positiveDeficiency piece data.threshold)
  | .typeAPortReturn, object =>
      -- `lem:typeA-port-return`: every completion port of the object carries an
      -- anchored return.  Stated of the object and of every support, receiver
      -- and port, because the manuscript's proof reads only `lem:bridgeless` at
      -- the port edge -- nothing about the support the port belongs to.
      (∀ support : Finset object.Vertex, ∀ receiver outside : object.Vertex,
        outside ∈ Graph.VisibleEntry.completionPorts object support receiver →
        Nonempty (Graph.VisibleEntry.AnchoredReturn object receiver outside))
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
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅))
  | .typeAVisibleFirstExcess, object =>
      -- Node `[93]`, no -- node `[94]`, `lem:typeA-silent-excess-count`:
      -- `S_sil^exc(X) ≥ s·D_A(X)` at every Type A support, with
      -- `s·D_A(X) = |V(X)| − s·def⁺(X)` written without division or
      -- subtraction.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                      data.dischargeScale receiver ∅ ∧
                  piece.card ≤
                    (∑ other ∈ object.receivers piece data.threshold,
                      (Graph.VisibleEntry.silentExcess object piece
                        data.threshold data.dischargeScale other).card) +
                      data.dischargeScale *
                        object.positiveDeficiency piece data.threshold)
  | .typeAExitOneReturn, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ return' : Graph.VisibleEntry.AnchoredReturn object receiver
                        package.outside,
                      Graph.ShiftedCycleLength data.LengthOK return'.path.length)
  | .typeAExitOneFree, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∀ return' : Graph.VisibleEntry.AnchoredReturn object receiver
                        package.outside,
                      ¬ Graph.ShiftedCycleLength data.LengthOK return'.path.length)
  | .typeAExitTwoTheta, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK
                      receiver package.outside)
  | .typeAExitTwoFree, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ¬ Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK
                      receiver package.outside)
  | .typeAExitThreeCollision, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.WindowLabelCollision.LabelCollision object
                      data.windowOrder data.LengthOK packing)
  | .typeAExitThreeFree, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.WindowLabelCollision.LabelCollisionFree object
                      data.windowOrder data.LengthOK packing)
  | .typeASaturatedExitEntry, object =>
      -- The shared entry of nodes `[101]`--`[107]`, and the hypothesis of
      -- `lem:typeA-exit4-residual-routing`: a saturated Type A receiver with a
      -- peeling set whose residual load is still at or above the saturation
      -- threshold.  `def:typeA-exit4-peeling`'s `P₄(w) ⊆ ℒ(w)` and
      -- `L₄(w) ≥ s·q(w)` are the two clauses the routing lemma uses; the
      -- witnesses attached to the peeled loads are node `[102]`'s fact.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled)
  | .typeAExitSevenProduced, object =>
      -- Node `[107]`, yes: exit `(7)` is produced on the exact selected
      -- no-exit-`(6)` residual.
      SelectedNoExitSixWith data object
        (fun packing piece => HandoffProduced data object packing piece)
  | .typeAExitSevenHandoff, object =>
      -- Node `[108]`: the produced envelope is committed with the admissible
      -- Type B handoff interface.
      SelectedNoExitSixWith data object
        (fun packing piece => HandoffAdmissible data object packing piece)
  | .typeAExitSevenFree, object =>
      -- Node `[107]`, no: the same selected residual has no decorated
      -- handoff envelope and therefore enters the route-8 test.
      SelectedNoExitSixWith data object
        (fun packing piece => ¬ HandoffProduced data object packing piece)
  | .typeAVisibleEntryClause, object =>
      -- Node `[93]`, yes arm: the exact selected visible package and the
      -- response/germ prefix derived from it before any semantic quotient.
    (∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ component ∈ object.canonicalPieces
            (object.remainderSupport packing),
          let piece := object.pieceSupport
            (object.remainderSupport packing) component
          object.NegativeNetCharge piece data.threshold
              data.dischargeScale ∧
            object.ambientSurplus piece data.threshold = 0 ∧
            ∃ receiver : object.Vertex,
              object.IsReceiver piece data.threshold receiver ∧
                object.Saturated piece data.threshold
                  data.dischargeScale receiver ∧
                ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                    data.threshold data.dischargeScale receiver ∅,
                  (∀ load : package.SelectedLoad,
                    ((∀ vertex ∈
                        (package.selectedReturn load.1 load.2).connector.support,
                      vertex ≠ (package.selectedResponseCoordinate load).entry.1 →
                        vertex ∉ piece) ∧
                      Graph.VisibleEntry.IsChannel object piece
                        (package.selectedResponseCoordinate load).channel) ∧
                      (package.selectedPieceChannel load).length =
                        (package.selectedResponseCoordinate load).channel.length ∧
                      (package.selectedContextConnector load).length =
                        (package.selectedResponseCoordinate load).connectorLabel) ∧
                  (∀ selected : package.SelectedGerm,
                    selected ∈ package.germSchedule.values) ∧
                  (∀ pair : package.GermPair,
                    pair ∈ package.germPairSchedule.values ∧
                      Graph.DecoratedHandoff.SeparatesAt
                        pair.left.germ.path pair.right.germ.path
                          pair.firstSeparator.separator ∧
                      pair.separatorOrder = pair.firstSeparator.separator ::
                        pair.firstSeparator.remaining))
  | .highCentreNormalForm, object =>
      -- Node `[68]`: `lem:heavy-neighbourhood-normal-form`, at every high
      -- centre of the object at once.  It is not about one support, so it is
      -- stated of the object and both arms of the split read it.
      (∀ centre : object.Vertex,
        Graph.IsHighCentre object data.threshold centre →
        Graph.NormalForm object data.threshold centre)
  | .typeBHeavyCentre, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece, data.threshold + 1 < object.degree centre)
  | .typeBDegreeFourCentres, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
                object.degree centre = data.threshold + 1)
  | .typeBLocalDichotomy, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              (∃ centre ∈ piece,
                data.threshold + 1 < object.degree centre) ∧
              ∀ centre ∈ piece,
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
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre →
                Nonempty
                  (Graph.FanCertificateLabelling object data.windowOrder centre))
  | .fanCertificateResidual, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre ∧
                  IsEmpty
                    (Graph.FanCertificateLabelling object data.windowOrder
                      centre))
  | .typeBDegreeFourProfile, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              (∀ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre →
                object.degree centre = data.threshold + 1) ∧
              ∀ centre ∈ piece, object.degree centre = data.threshold + 1 →
                ((∃ left right : object.Vertex,
                      Graph.FanCompatible object centre left right) ∨
                    data.threshold - 1 ≤
                      (Graph.triangularEndpoints object centre).card) ∧
                  object.degree centre - data.threshold = 1 ∧
                  ∀ envelope : Finset object.Vertex,
                    Graph.TypeBFanIncidence.closedCount object data.threshold
                        envelope centre ≤ data.threshold + 1 ∧
                      Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                          data.dischargeScale envelope centre =
                        (data.dischargeScale : Int) *
                            (Graph.TypeBFanIncidence.closedCount object
                              data.threshold envelope centre : Int) -
                          (data.dischargeScale : Int) *
                            (data.threshold : Int) +
                          ((data.threshold : Int) + 2))
  | .typeBHybridEntry, object =>
      -- Node `[74]`/`[82]`.  Scoped to the centres of a Type B support, because
      -- `k ≤ α(D)` is available only at a certificate-marked fan, and quantified
      -- over the envelope and the packed-window union because both are fan data.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
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
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre ∧
                  Graph.TypeBDirectCycle.DirectCycleConfiguration object
                    data.windowOrder data.LengthOK packing centre)
  | .typeBDirectCycleFree, object =>
      -- Node `[72]`, surviving arm, on the one support selected at node `[62]`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
                  data.LengthOK packing centre)
  | .typeBB2Choice, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece object packing,
            object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus canonicalPiece.vertices data.threshold ∧
              Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
                data.dischargeScale canonicalPiece
                (Graph.TypeBRefinedSupport.centres object data.threshold
                  canonicalPiece.vertices))
  | .typeBDisjointLedger, object =>
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece object packing,
            object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus canonicalPiece.vertices data.threshold ∧
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
                  data.threshold data.dischargeScale canonicalPiece,
                ledger.ExactAugmentedLedgerRefinement ∧
                  (∀ component : Graph.SupportComponents.Connected.Component
                        object ledger.remainingCore,
                      component ∈ Graph.SupportComponents.Connected.order object
                          ledger.remainingCore →
                        Graph.TypeBPostLedgerCore.PostLedgerComponent
                          data.typeABPresentation ledger component) ∧
                  ∀ components :
                      Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                        ledger),
                    (∀ component ∈ components,
                      component ∈ Graph.SupportComponents.Connected.order object
                        ledger.remainingCore) →
                      ∀ production : ∀ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent ledger
                            components,
                        Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                          component.1 data.LengthOK (handoffHighDegree object)
                          (handoffAbsorbing data object packing),
                        ∃ grouped :
                          Graph.DecoratedHandoff.GroupedEnvelopes object
                            data.LengthOK (handoffUncompressible data object)
                            (handoffWindowFree data object)
                            (handoffHighDegree object)
                            (handoffAbsorbing data object packing)
                            (Graph.TypeBMaximalCompletion.SelectedComponent
                              ledger components),
                          (∀ component :
                              Graph.TypeBMaximalCompletion.SelectedComponent
                                ledger components,
                            (grouped.envelope component).core =
                              Graph.SupportComponents.Connected.vertices object
                                ledger.remainingCore component.1) ∧
                            ∀ centre : object.Vertex,
                              centre ∈ grouped.centres ↔
                                ∃ component :
                                  Graph.TypeBMaximalCompletion.SelectedComponent
                                    ledger components,
                                  centre =
                                    (production component).separation.separator)
  | .typeBSelectedFanCharge, object =>
      ∀ packing : Finset (Finset object.Vertex),
        ∀ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece object packing,
          ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement →
              (∀ centre
                  (member : centre ∈ Graph.TypeBRefinedSupport.centres object
                    data.threshold canonicalPiece.vertices),
                (ledger.choice.entry centre member).IsCandidate data.threshold
                  data.dischargeScale canonicalPiece centre) ∧
                (0 : Int) ≤ ledger.selectedEntryPayment₂
  | .typeBOverlapObstruction, object =>
      -- Node `[72]`/`[81]`, no.  `lem:typeB-bridge-to-overlap`: the
      -- disjoint-carrier clause fails on some assigned support, and what that
      -- support then carries is a *minimal* Type B overlap obstruction.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece object packing,
            object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus canonicalPiece.vertices data.threshold ∧
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
                data.threshold data.dischargeScale canonicalPiece))
  | .fanCertificateResidualMass, object =>
      ∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre object data.threshold centre ∧
                  IsEmpty (Graph.FanCertificateLabelling object
                    data.windowOrder centre) ∧
                  ∀ envelope : Finset object.Vertex,
                    Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                        data.threshold data.dischargeScale envelope centre ≤
                      data.bridgeMassFactor * data.dischargeScale *
                        (object.degree centre - data.threshold)
  | .typeBOverlapObstructionMass, object =>
      ∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece object packing,
            object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus canonicalPiece.vertices data.threshold ∧
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
                data.threshold data.dischargeScale canonicalPiece) ∧
              ∀ centre ∈ canonicalPiece.vertices,
                Graph.IsHighCentre object data.threshold centre →
                ∀ envelope : Finset object.Vertex,
                  Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                      data.threshold data.dischargeScale envelope centre ≤
                    data.bridgeMassFactor * data.dischargeScale *
                      (object.degree centre - data.threshold)
  | .typeBExclusionResidualMass, object =>
      ∃ packing : Finset (Finset object.Vertex),
        ∃ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece object packing,
          ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement ∧
              (¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex) ∧
              ∀ centre ∈ canonicalPiece.vertices,
                Graph.IsHighCentre object data.threshold centre →
                ∀ envelope : Finset object.Vertex,
                  Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                      data.threshold data.dischargeScale envelope centre ≤
                    data.bridgeMassFactor * data.dischargeScale *
                      (object.degree centre - data.threshold)
  | .typeBBridgeMass, object =>
      ((∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset object.Vertex,
          piece ⊆ object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn object piece →
          object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < object.ambientSurplus piece data.threshold →
          (∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
            ∀ envelope : Finset object.Vertex,
              Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
                  data.dischargeScale envelope centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (object.degree centre - data.threshold)) ∧
            (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
                data.threshold data.dischargeScale →
              piece.card + data.dischargeScale *
                    object.ambientSurplus piece data.threshold ≤
                data.dischargeScale * object.positiveDeficiency piece data.threshold +
                  data.bridgeMassFactor * data.dischargeScale *
                    object.ambientSurplus piece data.threshold)) ∧
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
  | .typeBBridgeSublinear, object =>
      ∀ packing : Finset (Finset object.Vertex),
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
                object.degreeSurplus data.threshold
  | .branchKillClosed, object =>
      LargeBudgetResidual data object ∧
        ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            (∀ window : Finset object.Vertex,
              object.InducesWindow data.windowOrder window →
              ∃ member ∈ packing, ¬ Disjoint window member) ∧
            ∃ component ∈ object.canonicalPieces
                (object.remainderSupport packing),
              object.NegativeNetCharge
                (object.pieceSupport (object.remainderSupport packing) component)
                data.threshold data.dischargeScale
  | .typeBExclusionCharge, object =>
      ∀ packing : Finset (Finset object.Vertex),
        ∀ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece object packing,
          ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement →
              (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex →
              object.NonNegativeNetCharge canonicalPiece.vertices
                data.threshold data.dischargeScale
  | .typeBExcluded, object =>
      False
  | .typeBExclusionResidual, object =>
      ∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece object packing,
            object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < object.ambientSurplus canonicalPiece.vertices data.threshold ∧
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
                  data.threshold data.dischargeScale canonicalPiece,
                ledger.ExactAugmentedLedgerRefinement ∧
                  (∀ component : Graph.SupportComponents.Connected.Component
                        object ledger.remainingCore,
                      component ∈ Graph.SupportComponents.Connected.order object
                          ledger.remainingCore →
                        Graph.TypeBPostLedgerCore.PostLedgerComponent
                          data.typeABPresentation ledger component) ∧
                  ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                    Graph.TypeBRefinedSupport.scaledCoreCharge object
                      data.threshold data.dischargeScale canonicalPiece.vertices
                      vertex
  | .typeAExitFour, object =>
      -- Node `[101]`, yes: on the selected visible package after exits `(1)`,
      -- `(2)`, and `(3)` are absent, a canonical exit-`(4)` witness peels one
      -- unpeeled routed load.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ _package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          _package.outside ∅,
                        witness.load = load)
  | .typeAExitFourPeeled, object =>
      -- Node `[102]`: `lem:typeA-exit4-discharge`, read on the exact witness
      -- committed at node `[101]`.  The next peeling set is obtained by
      -- inserting that witness's routed load; it remains a subset of the routed
      -- loads and the residual load drops by exactly one.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            object.routedLoads piece data.threshold receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver ∅)
  | .typeAExitFourFiniteDescent, object =>
      -- `lem:typeA-saturated-handoff`: the finite descent principle read at
      -- the exact selected receiver and current peeling set.  Downstream rows
      -- instantiate `Terminal` with the paper's closed exits, exit-(7)
      -- handoff, and route-8 residual alternatives; this fact only records
      -- the finite exit-(4) descent, so it cannot invent a terminal branch.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ startPeeled : Finset object.Vertex,
                    startPeeled ⊆ object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver startPeeled ∧
                      ∀ Retained Terminal :
                          Finset object.Vertex → Prop,
                        Retained startPeeled →
                        (∀ peeled,
                          peeled ⊆
                            object.routedLoads piece data.threshold receiver →
                          Retained peeled →
                          Graph.ExitFour.SaturatedAfter piece data.threshold
                            data.dischargeScale receiver peeled →
                          Terminal peeled ∨
                            ∃ load ∈ object.routedLoads piece data.threshold
                                receiver,
                              ∃ fresh : load ∉ peeled, Retained (Finset.cons load peeled fresh)) →
                        (∃ finalPeeled ⊆
                            object.routedLoads piece data.threshold receiver,
                          Retained finalPeeled ∧ Terminal finalPeeled) ∨
                        (∃ finalPeeled ⊆
                            object.routedLoads piece data.threshold receiver,
                          Retained finalPeeled ∧
                            ¬ Graph.ExitFour.SaturatedAfter piece
                              data.threshold data.dischargeScale receiver
                              finalPeeled))
  | .typeASaturatedHandoffVisible, object =>
      -- `lem:typeA-exit4-residual-routing`, visible case at the current
      -- peeling set: a completion port carries the registered four unpeeled
      -- visible returns, packaged canonically for exits `(1)`--`(7)`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Nonempty
                        (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                          data.threshold data.dischargeScale receiver peeled))
  | .typeASaturatedHandoffSilent, object =>
      -- `lem:typeA-exit4-residual-routing`, silent case at the current
      -- peeling set: no port has four unpeeled visible returns, so the
      -- canonical residual excess set is nonempty and silent.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled)
  | .typeASaturatedHandoffExitFour, object =>
      -- `lem:typeA-exit4-residual-routing`, exit `(4)` at the current peeling
      -- state.  In the visible case the witness supports one of the selected
      -- four visible loads; in the silent case it supports a load from the
      -- canonical residual excess set `E₄(w)`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)))
  | .typeASaturatedHandoffExitFourFree, object =>
      -- The selected current saturated-handoff state has no exit-`(4)`
      -- witness of the corresponding visible or silent kind.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)))
  | .typeAExitFourReceiverDischarged, object =>
      -- Node `[102]`, discharged arm: after the same peel, the selected
      -- receiver is unsaturated at the peeled residual, equivalently its
      -- remaining receiver charge is nonnegative in the cleared scale.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            object.routedLoads piece data.threshold receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver ∅ ∧
                          ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                              data.dischargeScale receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) ∧
                          1 + Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) ≤
                            data.dischargeScale *
                              object.missingPorts piece data.threshold
                                receiver)
  | .typeAExitFourFree, object =>
      -- Node `[101]`, no: the same selected package carries no exit-`(4)`
      -- witness.  This is not a global route-8 statement.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ _package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ¬ ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          _package.outside ∅,
                        witness.load = load)
  | .typeAExitFive, object =>
      -- Node `[103]`, yes: at the exact current saturated-handoff state after
      -- exit `(4)` is absent, exit `(5)` supplies a target-complete proper
      -- support compression.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ∃ support : Finset object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitFiveFree, object =>
      -- Node `[103]`, no: the same current saturated-handoff state has no
      -- target-complete proper support compression.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ¬ ∃ support : Finset object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitSix, object =>
      -- Node `[105]`, yes: the selected saturated handoff state, after exits
      -- `(4)` and `(5)` have failed, carries an equality of declared response
      -- coordinates that becomes target-complete only after adjoining a larger
      -- connected support.  The witness is tied to the incoming residual; it is
      -- not an arbitrary route-8 object.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ ∃ support : Finset object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK) object
                          support) ∧
                      ExitSixDelocalizes data object piece)
  | .typeAExitSixFree, object =>
      -- Node `[105]`, no: the same selected saturated handoff state has no
      -- exit-`(6)` delocalization witness.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ object.canonicalPieces
              (object.remainderSupport packing),
            let piece := object.pieceSupport
              (object.remainderSupport packing) component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ ∃ support : Finset object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK) object
                          support) ∧
                      ¬ ExitSixDelocalizes data object piece)
  | .typeAExitSixProper, object =>
      -- Node `[106]`, proper scope: `lem:proper-smearing` returns a
      -- proper-support replacement for the selected delocalization.
      (∃ support : Finset object.Vertex,
        Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object support)
  | .typeAExitSixGlobal, object =>
      -- Node `[106]`, global scope: `lem:no-silent-global-smearing` returns a
      -- strictly smaller closed representative.
      (∃ representative : Graph.FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK object))
  | .route8Residual, object =>
      -- Node `[109]`: the selected no-exit-`(7)` residual enters the route-8
      -- arm.  This is only the residual fact; Part IX may later read this
      -- exact ledger state, but no route-8 carrier package is registered here.
      SelectedNoExitSixWith data object (fun packing piece =>
        ¬ HandoffProduced data object packing piece)
  | .route8ResidualProfile, object =>
      -- Node `[110]`: the selected route-8 residual satisfies the
      -- silent-core residual profile, without creating a secondary carrier.
      SilentCoreResidualProfile data object
  | .route8GlobalSqueeze, object =>
      -- Node `[111]`: the selected route-8 profile lies on the large-budget
      -- branch.
      Route8GlobalSqueeze data object
  | .route8BasinBurden, object =>
      -- Node `[112]`: the selected route-8 residual carries the basin-burden
      -- lower side of `lem:typeA-route8-burden`.
      Route8BasinBurden data object
  | .route8LargeBudgetDeficit, object =>
      -- Node `[113]`: the selected route-8 residual carries both the basin
      -- burden and the large-budget Type A deficit lower side.
      Route8LargeBudgetDeficit data object
  | .route8CarrierCore, object =>
      -- Node `[114]`: the canonical minimal carrier-core theorem package,
      -- available on the selected route-8 residual.
      Route8CarrierCore data object
  | .route8SmallCoreCollapse, object =>
      -- Nodes `[115]`--`[116]`: the zero/one-core collapse package, available
      -- on the selected route-8 residual after `[114]`.
      Route8SmallCoreCollapse data object
  | .route8TwoCarrierReduction, object =>
      -- Node `[117]`: the private-carrier squeeze package, available on the
      -- selected route-8 residual after `[115]`--`[116]`.
      Route8TwoCarrierReduction data object
  | .route8CarrierDeletionWitnesses, object =>
      -- Node `[118]`: carrier-deletion target-defect witnesses for every
      -- selected two-carrier essential-core entry.
      Route8CarrierDeletionWitnesses data object
  | .route8PrivateCarrierBudget, object =>
      -- Nodes `[119]`--`[120]`: no two-carrier entry gives the
      -- private-carrier budget on the selected route-8 residual.
      Route8PrivateCarrierBudget data object
  | .route8NoTwoCarrierContradiction, object =>
      -- Nodes `[121]`--`[122]`: the no-two-carrier branch contradicts the
      -- selected burden/deficit and rate facts.
      Route8NoTwoCarrierContradiction data object
  | .route8PressureDescent, object =>
      -- Node `[123]`: the pressure-descent join carries the finite exit-(4)
      -- descent theorem and the route-8 carrier contradiction on one ledger.
      Route8PressureDescent data object
  | .route8TerminalResidual, object =>
      -- Node `[123]`: the incoming pressure residual still presents the
      -- terminal two-carrier route-8 obstruction.
      Route8TerminalResidual data object
  | .route8TerminalNoGo, object =>
      -- Node `[124]`: terminal two-carrier route-8 no-go through Q5
      -- carrier-deletion and the committed no-exit-(4) fact.
      Route8TerminalNoGo data object
  | .largeBudgetRoute8Closed, _object =>
      False
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
      -- Node `[129]`, exactly `def:baseline-spine-demand`: the already-built
      -- active family together with one concrete declared, independently
      -- target-testable spine family, its canonical deficit, and the bound
      -- `E_spine <= C_E n`.  This has no window-package premise: that package
      -- belongs exclusively to `[21]`.
      (Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold ∧
        ∃ (Coordinate : Type u) (family : Finset Coordinate)
          (coordinateSupport : Coordinate → Finset object.Vertex),
          (∀ declared : Graph.DeclaredQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object family
              coordinateSupport,
            declared.toRankQuotient.FunctionalOn ↑family →
              declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
            Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
              2 ^ (family.card + Graph.spineDeficit object.vertexCount
                data.threshold family.card) ∧
            Graph.spineDeficit object.vertexCount data.threshold family.card ≤
              data.surplusScale * object.vertexCount)
  | .canonicalPairLedger, object =>
      ∃ (active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold)
        (certificate : Graph.HasSparsePairDEBlocker
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
            (object.portPairSchedule data.threshold)),
        let activation := Graph.pairResponseActivation active
        let pairs := object.portPairSchedule data.threshold
        pairs = object.portPairSchedule data.threshold ∧
          pairs.card = (object.degreeSurplus data.threshold).choose 2 ∧
          let recorded := Graph.recordSparsePairDEBlocker activation pairs certificate
          (recorded.blockedPairs data.threshold).card +
                (recorded.unblockedPairs data.threshold).card = pairs.card ∧
            (recorded.canonicalIncidenceLedger data.threshold).card =
              (recorded.blockedPairs data.threshold).card ∧
            (recorded.blockedPairs data.threshold).card =
              (recorded.canonicalBlockerSet data.threshold).sum
                (recorded.blockerMultiplicity data.threshold) ∧
            ∃ pair ∈ pairs, (recorded.blockers pair).Nonempty
  | .sparsePairExit, object =>
      Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
  | .canonicalBlockerRoute, object =>
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
          Graph.HasSparsePairDEBlocker
            (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
            (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
              (object.portPairSchedule data.threshold)
  | .dependentPairFamily, object =>
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        let activation := Graph.pairResponseActivation active
        let pairs := object.portPairSchedule data.threshold
        ∃ attempt :
            let family := activation.pairFamily pairs
            let coordinateSupport : object.PairCoordinate →
                Finset object.Vertex := by
              letI := object.vertices.decEq
              exact Graph.DeclaredSignature.Coordinate.support
            Graph.AttemptedQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object family
              coordinateSupport,
            let family := activation.pairFamily pairs
            ¬ Set.InjOn attempt.label ↑family
  | .independentPairFamily, object =>
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        let activation := Graph.pairResponseActivation active
        let pairs := object.portPairSchedule data.threshold
        ∀ attempt :
            let family := activation.pairFamily pairs
            let coordinateSupport : object.PairCoordinate →
                Finset object.Vertex := by
              letI := object.vertices.decEq
              exact Graph.DeclaredSignature.Coordinate.support
            Graph.AttemptedQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object family
              coordinateSupport,
          let family := activation.pairFamily pairs
          Set.InjOn attempt.label ↑family
  | .mixedSparseSpineDependence, object => by
      classical
      exact ∃ (active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold)
        (Coordinate : Type u) (family : Finset Coordinate)
        (coordinateSupport : Coordinate → Finset object.Vertex),
        (∀ declared : Graph.DeclaredQuotient
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object family
            coordinateSupport,
          declared.toRankQuotient.FunctionalOn ↑family →
            declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
          Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
            2 ^ (family.card + Graph.spineDeficit object.vertexCount
              data.threshold family.card) ∧
          Graph.spineDeficit object.vertexCount data.threshold family.card ≤
            data.surplusScale * object.vertexCount ∧
          let activation := Graph.pairResponseActivation active
          let pairs := object.portPairSchedule data.threshold
          let pairFamily := activation.pairFamily pairs
          let mixedFamily : Finset (Sum Coordinate object.PairCoordinate) :=
            family.image Sum.inl ∪ pairFamily.image Sum.inr
          let mixedSupport : Sum Coordinate object.PairCoordinate →
              Finset object.Vertex :=
            Sum.elim coordinateSupport (by
              letI := object.vertices.decEq
              exact Graph.DeclaredSignature.Coordinate.support)
          let Determines := fun
              (attempt : Graph.AttemptedQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object
                mixedFamily mixedSupport)
              (coordinate : Sum Coordinate object.PairCoordinate)
              (determiners : Set (Sum Coordinate object.PairCoordinate)) =>
            ∀ left right,
              (∀ determiner ∈ determiners,
                attempt.value left (attempt.label determiner) =
                  attempt.value right (attempt.label determiner)) →
                attempt.value left (attempt.label coordinate) =
                  attempt.value right (attempt.label coordinate)
          ∀ attempt : Graph.AttemptedQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              mixedFamily mixedSupport,
            (∃ coordinate ∈ mixedFamily,
              ∃ determiners : Set (Sum Coordinate object.PairCoordinate),
                determiners ⊆ ↑mixedFamily ∧ determiners.Finite ∧
                  coordinate ∉ determiners ∧
                    Determines attempt coordinate determiners) →
            ¬ Set.InjOn attempt.label ↑mixedFamily →
            Graph.SparseSurplusExit
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object ∨
              ∃ pair ∈ pairs,
                ((∃ left right, attempt.Identifies left right ∧
                    left.boundaryDegreeProfile ≠
                      right.boundaryDegreeProfile) ∨
                  (∃ left right, attempt.Identifies left right ∧
                    Graph.Response.TargetDefect
                      (Graph.HasCycleWithLength data.LengthOK) left right) ∨
                  Graph.Strategy.InterfaceReplacement.ReplacementSupport
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object
                    attempt.support)
  | .exactCubicBaselineBudget, object =>
      Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
          (2 * object.vertexCount) ^
            Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ∧
        (2 * Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
            object.vertexCount.choose 2 →
          (object.vertexCount - 1) ^
              Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
            Graph.cubicBaselineBudget object.vertexCount data.threshold *
              (2 * (data.threshold + 1)) ^
                Graph.cubicBaselineEdgeCount object.vertexCount data.threshold)
  | .incrementalSkeletonRoom, object =>
      Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
          object.edgeCount ∧
        Graph.skeletonBudget object ≤
          Graph.cubicBaselineBudget object.vertexCount data.threshold *
            object.vertexCount ^
              (object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) ∧
        2 * (object.edgeCount -
              Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) ≤
          object.degreeSurplus data.threshold + 2
  | .skeletonDominates, object =>
      Nat.card (Graph.PackedWindowRealization.Skeleton
          object.vertexCount object.edgeCount) = Graph.skeletonBudget object ∧
        ∀ (State : Type u)
          (stateOf : Graph.PackedWindowRealization.Skeleton
            object.vertexCount object.edgeCount → State),
          Nat.card (Set.range stateOf) ≤ Graph.skeletonBudget object
  | .sparseUpperEnvelope, object =>
      (object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount) ∧
        ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            (object.windowRemainderIncidences packing).card +
                (2 * (data.windowOrder - 1) * packing.card +
                  (object.crossWindowIncidences packing).card) =
              data.threshold * (data.windowOrder * packing.card) +
                object.ambientSurplus (object.windowSupport packing)
                  data.threshold
  | .capacityTokenLedger, object =>
      ∃ (Coordinate Chord : Type u)
        (activation : object.DemandActivation Coordinate Chord)
        (presentation : object.CarrierPresentation Coordinate Chord)
        (packing : Finset (Finset object.Vertex)),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          ((object.primitiveCarrier data.threshold).card =
              object.vertexCount + 2 * object.edgeCount +
                object.degreeSurplus data.threshold ∧
            (object.primitiveCarrier data.threshold).card ≤
              object.primitiveCarrierSupply data.threshold) ∧
          Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement object
            data.threshold data.windowOrder activation presentation packing
  | .roleFibrePartition, object =>
      -- `lem:exact-surplus-pair-charge-partition` with the classwise and
      -- subtype budgets, at the object's own capacity-token ledger.
      Graph.RoleFibrePartitionStatement object data.threshold data.windowOrder
  | .fibrePressure, object =>
      -- `lem:capacity-token-high-load` with
      -- `cor:forced-homogeneous-same-token-scale` and the two sharp budgets,
      -- existential in the object's own capacity-token ledger at every declared
      -- presentation.
      Graph.FibrePressureStatement object data.threshold data.windowOrder
  | .spineSurplusEstimate, object =>
      -- The actual node-`[138]` conclusion, derived from the concrete
      -- node-`[129]` deficit and node-`[131]` entropy ledger.
      object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt object.vertexCount
  | .sparsePressureNearCubic, object =>
      object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt object.vertexCount
  | .sparsePressureOverload, object =>
      -- `prop:single-graph-sparse-pressure-routing` (b) with
      -- `cor:coupled-single-graph-overload-budget`.
      Graph.SparsePressureOverloadStatement object data.threshold data.windowOrder
  | .windowClassOverload, object =>
      -- Node `[139]`, yes: the overload occurs at a window-incidence token.
      Graph.SparsePressureOverloadInClass object data.threshold data.windowOrder
        .windowIncidence
  | .windowClassAbsent, object =>
      -- Node `[139]`, no.
      Graph.SparsePressureOverloadOutsideClass object data.threshold data.windowOrder
        .windowIncidence
  | .remainderClassOverload, object =>
      -- Node `[141]`, yes: the overload occurs at a remainder-surplus token.
      Graph.SparsePressureOverloadInClass object data.threshold data.windowOrder
        .remainderSurplus
  | .remainderClassAbsent, object =>
      -- Node `[141]`, no: after the inherited non-window residual, the same
      -- selected overload token is necessarily primitive.
      Graph.SparsePressureOverloadInClass object data.threshold data.windowOrder
        .primitiveCarrier
  | .windowIncidenceAudit, object =>
      -- Node `[140]`.
      Graph.ClassAuditStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) .windowIncidence
  | .remainderSurplusAudit, object =>
      -- Node `[142]`.
      Graph.ClassAuditStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) .remainderSurplus
  | .primitiveCarrierAudit, object =>
      -- Node `[143]`.
      Graph.ClassAuditStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) .primitiveCarrier
  | .primitiveClassOverload, object =>
      -- Node `[143]`'s class verdict, derived from the two negative arms.
      Graph.SparsePressureOverloadInClass object data.threshold data.windowOrder
        .primitiveCarrier
  | .quantitativeOverload, object =>
      -- `cor:quantitative-homogeneous-overload`.
      Graph.QuantitativeOverloadStatement object data.threshold data.windowOrder
  | .homogeneousCapsHold, object =>
      -- The subbranch hypothesis of
      -- `thm:homogeneous-overload-geometric-closure`.
      Graph.HomogeneousCapsHold object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))
  | .homogeneousBottleneckPattern, object =>
      -- Its complement, normalized to the positive same-token bottleneck
      -- pattern the paper routes at node `[144]`.
      Graph.HomogeneousBottleneckPatternStatement object data.threshold
        data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))
  | .bottleneckRouting, object =>
      -- `thm:homogeneous-overload-geometric-closure`'s first assertion:
      -- `lem:same-token-bottleneck-routing` at every declared routed
      -- bottleneck of the object.
      Graph.BottleneckRoutingStatement object
        (Graph.MinimumDegreeAtLeast data.threshold) data.LengthOK
        data.windowOrder
  | .typeBHandoff, object =>
      -- and, at a survivor, the outcome itself: every declared routed
      -- bottleneck produces admissible decorated Type B handoff fan data.
      -- `prop:nonnear-cubic-sharp-overload-routing` opens *"if a sparse surplus
      -- exit occurs, there is nothing to route; otherwise..."*, and node `[125]`
      -- has already excluded that arm.
      Graph.TypeBHandoffStatement object
        (Graph.MinimumDegreeAtLeast data.threshold) data.LengthOK
        data.windowOrder
  | .homogeneousBottleneck, object =>
      -- `cor:homogeneous-same-token-caps-close` at the counted `L_geom`, with
      -- `thm:homogeneous-overload-geometric-closure`'s edge-count half.
      Graph.HomogeneousCapsCloseStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))
  | .sparseSurplusSurvivor, object =>
      -- `def:named-surplus-exits`: none of the five conclusions occurs, and
      -- `lem:replacement` at the same selection: no proper support carries a
      -- replacement either.  Both halves come from the node-`[1]`--`[4]`
      -- selection entry, and both are what node `[132]`'s blocker arm needs, so
      -- neither is left to be assumed downstream.
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object ∧
        ∀ support : Finset object.Vertex,
          ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object support
  | .activeSurplusDemands, object =>
      -- `def:active-surplus-demands` with `lem:surviving-active-family`.
      Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold
  | .hotColdPartition, object =>
      HotColdWindowStatement data object

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
  | .exactResponseProfile => "exactResponseProfile"
  | .admissibleRankQuotient => "admissibleRankQuotient"
  | .functionalRankQuotient => "functionalRankQuotient"
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
  | .entropyPackageDemand => "entropyPackageDemand"
  | .entropyCapActive => "entropyCapActive"
  | .largeBudgetResidual => "largeBudgetResidual"
  | .netChargeLarge => "netChargeLarge"
  | .netChargeSmall => "netChargeSmall"
  | .netChargeCap => "netChargeCap"
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
  | .typeAUnsaturatedDischarge => "typeAUnsaturatedDischarge"
  | .typeAPortReturn => "typeAPortReturn"
  | .typeAVisibleEntry => "typeAVisibleEntry"
  | .typeAVisibleFirstExcess => "typeAVisibleFirstExcess"
  | .typeAVisibleEntryClause => "typeAVisibleEntryClause"
  | .typeAExitOneReturn => "typeAExitOneReturn"
  | .typeAExitOneFree => "typeAExitOneFree"
  | .typeAExitTwoTheta => "typeAExitTwoTheta"
  | .typeAExitTwoFree => "typeAExitTwoFree"
  | .typeAExitThreeCollision => "typeAExitThreeCollision"
  | .typeAExitThreeFree => "typeAExitThreeFree"
  | .typeASaturatedExitEntry => "typeASaturatedExitEntry"
  | .typeAExitSevenHandoff => "typeAExitSevenHandoff"
  | .typeAExitSevenFree => "typeAExitSevenFree"
  | .coldFailureCycle => "coldFailureCycle"
  | .coldFailureDefect => "coldFailureDefect"
  | .coldFailureCompression => "coldFailureCompression"
  | .coldFailureHandoff => "coldFailureHandoff"
  | .coldFailureRouting => "coldFailureRouting"
  | .coldExchangeBound => "coldExchangeBound"
  | .coldWindowLedgerSplit => "coldWindowLedgerSplit"
  | .coldRoute8Below => "coldRoute8Below"
  | .coldRoute8AtOrAbove => "coldRoute8AtOrAbove"
  | .coldHotEntropyOverflow => "coldHotEntropyOverflow"
  | .coldHotEntropyCap => "coldHotEntropyCap"
  | .coldMass => "coldMass"
  | .coldAmbientCubic => "coldAmbientCubic"
  | .coldStubExcess => "coldStubExcess"
  | .coldGermCandidates => "coldGermCandidates"
  | .coldSelectedBranchExcess => "coldSelectedBranchExcess"
  | .coldAmbientCubicStubExcess => "coldAmbientCubicStubExcess"
  | .coldHandoffTransfer => "coldHandoffTransfer"
  | .coldGermExtraction => "coldGermExtraction"
  | .coldPositiveGerm => "coldPositiveGerm"
  | .coldGermRouted => "coldGermRouted"
  | .coldTerminalResidual => "coldTerminalResidual"
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
  | .typeBB2Choice => "typeBB2Choice"
  | .typeBDisjointLedger => "typeBDisjointLedger"
  | .typeBSelectedFanCharge => "typeBSelectedFanCharge"
  | .typeBOverlapObstruction => "typeBOverlapObstruction"
  | .fanCertificateResidualMass => "fanCertificateResidualMass"
  | .typeBOverlapObstructionMass => "typeBOverlapObstructionMass"
  | .typeBExclusionResidualMass => "typeBExclusionResidualMass"
  | .typeBBridgeMass => "typeBBridgeMass"
  | .typeBBridgeSublinear => "typeBBridgeSublinear"
  | .branchKillClosed => "branchKillClosed"
  | .typeBExclusionCharge => "typeBExclusionCharge"
  | .typeBExcluded => "typeBExcluded"
  | .typeBExclusionResidual => "typeBExclusionResidual"
  | .typeAExitFour => "typeAExitFour"
  | .typeAExitFourPeeled => "typeAExitFourPeeled"
  | .typeAExitFourFiniteDescent => "typeAExitFourFiniteDescent"
  | .typeASaturatedHandoffVisible => "typeASaturatedHandoffVisible"
  | .typeASaturatedHandoffSilent => "typeASaturatedHandoffSilent"
  | .typeASaturatedHandoffExitFour => "typeASaturatedHandoffExitFour"
  | .typeASaturatedHandoffExitFourFree =>
      "typeASaturatedHandoffExitFourFree"
  | .typeAExitFourReceiverDischarged => "typeAExitFourReceiverDischarged"
  | .typeAExitFourFree => "typeAExitFourFree"
  | .typeAExitFive => "typeAExitFive"
  | .typeAExitFiveFree => "typeAExitFiveFree"
  | .typeAExitSix => "typeAExitSix"
  | .typeAExitSixFree => "typeAExitSixFree"
  | .typeAExitSixProper => "typeAExitSixProper"
  | .typeAExitSixGlobal => "typeAExitSixGlobal"
  | .typeAExitSevenProduced => "typeAExitSevenProduced"
  | .route8Residual => "route8Residual"
  | .route8ResidualProfile => "route8ResidualProfile"
  | .route8GlobalSqueeze => "route8GlobalSqueeze"
  | .route8BasinBurden => "route8BasinBurden"
  | .route8LargeBudgetDeficit => "route8LargeBudgetDeficit"
  | .route8CarrierCore => "route8CarrierCore"
  | .route8SmallCoreCollapse => "route8SmallCoreCollapse"
  | .route8TwoCarrierReduction => "route8TwoCarrierReduction"
  | .route8CarrierDeletionWitnesses => "route8CarrierDeletionWitnesses"
  | .route8PrivateCarrierBudget => "route8PrivateCarrierBudget"
  | .route8NoTwoCarrierContradiction => "route8NoTwoCarrierContradiction"
  | .route8PressureDescent => "route8PressureDescent"
  | .route8TerminalResidual => "route8TerminalResidual"
  | .route8TerminalNoGo => "route8TerminalNoGo"
  | .largeBudgetRoute8Closed => "largeBudgetRoute8Closed"
  | .sparseSlackSurplus => "sparseSlackSurplus"
  | .activeSurplusFamily => "activeSurplusFamily"
  | .sparsePortActivation => "sparsePortActivation"
  | .baselineSpineDemand => "baselineSpineDemand"
  | .canonicalPairLedger => "canonicalPairLedger"
  | .sparsePairExit => "sparsePairExit"
  | .canonicalBlockerRoute => "canonicalBlockerRoute"
  | .sparseUpperEnvelope => "sparseUpperEnvelope"
  | .capacityTokenLedger => "capacityTokenLedger"
  | .roleFibrePartition => "roleFibrePartition"
  | .fibrePressure => "fibrePressure"
  | .spineSurplusEstimate => "spineSurplusEstimate"
  | .sparsePressureNearCubic => "sparsePressureNearCubic"
  | .sparsePressureOverload => "sparsePressureOverload"
  | .windowClassOverload => "windowClassOverload"
  | .windowClassAbsent => "windowClassAbsent"
  | .remainderClassOverload => "remainderClassOverload"
  | .remainderClassAbsent => "remainderClassAbsent"
  | .windowIncidenceAudit => "windowIncidenceAudit"
  | .remainderSurplusAudit => "remainderSurplusAudit"
  | .primitiveCarrierAudit => "primitiveCarrierAudit"
  | .primitiveClassOverload => "primitiveClassOverload"
  | .quantitativeOverload => "quantitativeOverload"
  | .homogeneousCapsHold => "homogeneousCapsHold"
  | .homogeneousBottleneckPattern => "homogeneousBottleneckPattern"
  | .bottleneckRouting => "bottleneckRouting"
  | .typeBHandoff => "typeBHandoff"
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
example : label .hotColdPartition = "hotColdPartition" := rfl
example : label .densityCap = "densityCap" := rfl
example : label .remainderNormalized = "remainderNormalized" := rfl
example : label .boundaryDemand = "boundaryDemand" := rfl
example : label .stubSupply = "stubSupply" := rfl
example : label .wedgeSupply = "wedgeSupply" := rfl
example : label .curvatureDemandFloor = "curvatureDemandFloor" := rfl
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
example : label .entropyPackageDemand = "entropyPackageDemand" := rfl
example : label .entropyCapActive = "entropyCapActive" := rfl
example : label .largeBudgetResidual = "largeBudgetResidual" := rfl
example : label .netChargeLarge = "netChargeLarge" := rfl
example : label .netChargeSmall = "netChargeSmall" := rfl
example : label .netChargeCap = "netChargeCap" := rfl
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
example : label .typeAUnsaturatedDischarge = "typeAUnsaturatedDischarge" := rfl
example : label .typeAPortReturn = "typeAPortReturn" := rfl
example : label .typeAVisibleEntry = "typeAVisibleEntry" := rfl
example : label .typeAVisibleFirstExcess = "typeAVisibleFirstExcess" := rfl
example : label .typeAVisibleEntryClause = "typeAVisibleEntryClause" := rfl
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
example : label .coldFailureDefect = "coldFailureDefect" := rfl
example : label .coldFailureCompression = "coldFailureCompression" := rfl
example : label .coldFailureHandoff = "coldFailureHandoff" := rfl
example : label .coldFailureRouting = "coldFailureRouting" := rfl
example : label .coldExchangeBound = "coldExchangeBound" := rfl
example : label .coldWindowLedgerSplit = "coldWindowLedgerSplit" := rfl
example : label .coldHandoffTransfer = "coldHandoffTransfer" := rfl
example : label .coldGermExtraction = "coldGermExtraction" := rfl
example : label .coldPositiveGerm = "coldPositiveGerm" := rfl
example : label .coldGermRouted = "coldGermRouted" := rfl
example : label .coldTerminalResidual = "coldTerminalResidual" := rfl
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
example : label .typeBB2Choice = "typeBB2Choice" := rfl
example : label .typeBDisjointLedger = "typeBDisjointLedger" := rfl
example : label .typeBSelectedFanCharge =
    "typeBSelectedFanCharge" := rfl
example : label .typeBOverlapObstruction = "typeBOverlapObstruction" := rfl
example : label .fanCertificateResidualMass = "fanCertificateResidualMass" := rfl
example : label .typeBOverlapObstructionMass = "typeBOverlapObstructionMass" := rfl
example : label .typeBExclusionResidualMass = "typeBExclusionResidualMass" := rfl
example : label .typeBBridgeMass = "typeBBridgeMass" := rfl
example : label .typeBBridgeSublinear = "typeBBridgeSublinear" := rfl
example : label .branchKillClosed = "branchKillClosed" := rfl
example : label .typeBExclusionCharge = "typeBExclusionCharge" := rfl
example : label .typeBExcluded = "typeBExcluded" := rfl
example : label .typeBExclusionResidual = "typeBExclusionResidual" := rfl
example : label .typeAExitFour = "typeAExitFour" := rfl
example : label .typeAExitFourPeeled = "typeAExitFourPeeled" := rfl
example : label .typeAExitFourFiniteDescent =
    "typeAExitFourFiniteDescent" := rfl
example : label .typeASaturatedHandoffVisible =
    "typeASaturatedHandoffVisible" := rfl
example : label .typeASaturatedHandoffSilent =
    "typeASaturatedHandoffSilent" := rfl
example : label .typeASaturatedHandoffExitFour =
    "typeASaturatedHandoffExitFour" := rfl
example : label .typeASaturatedHandoffExitFourFree =
    "typeASaturatedHandoffExitFourFree" := rfl
example : label .typeAExitFourReceiverDischarged =
    "typeAExitFourReceiverDischarged" := rfl
example : label .typeAExitFourFree = "typeAExitFourFree" := rfl
example : label .typeAExitFive = "typeAExitFive" := rfl
example : label .typeAExitFiveFree = "typeAExitFiveFree" := rfl
example : label .typeAExitSix = "typeAExitSix" := rfl
example : label .typeAExitSixFree = "typeAExitSixFree" := rfl
example : label .typeAExitSixProper = "typeAExitSixProper" := rfl
example : label .typeAExitSixGlobal = "typeAExitSixGlobal" := rfl
example : label .typeAExitSevenProduced = "typeAExitSevenProduced" := rfl
example : label .route8Residual = "route8Residual" := rfl
example : label .route8ResidualProfile = "route8ResidualProfile" := rfl
example : label .route8GlobalSqueeze = "route8GlobalSqueeze" := rfl
example : label .route8BasinBurden = "route8BasinBurden" := rfl
example : label .route8LargeBudgetDeficit = "route8LargeBudgetDeficit" := rfl
example : label .route8CarrierCore = "route8CarrierCore" := rfl
example : label .route8SmallCoreCollapse =
    "route8SmallCoreCollapse" := rfl
example : label .route8TwoCarrierReduction =
    "route8TwoCarrierReduction" := rfl
example : label .route8CarrierDeletionWitnesses =
    "route8CarrierDeletionWitnesses" := rfl
example : label .route8PrivateCarrierBudget =
    "route8PrivateCarrierBudget" := rfl
example : label .route8NoTwoCarrierContradiction =
    "route8NoTwoCarrierContradiction" := rfl
example : label .route8PressureDescent =
    "route8PressureDescent" := rfl
example : label .route8TerminalResidual =
    "route8TerminalResidual" := rfl
example : label .route8TerminalNoGo =
    "route8TerminalNoGo" := rfl
example : label .largeBudgetRoute8Closed =
    "largeBudgetRoute8Closed" := rfl
example : label .sparseSlackSurplus = "sparseSlackSurplus" := rfl
example : label .activeSurplusFamily = "activeSurplusFamily" := rfl
example : label .sparsePortActivation = "sparsePortActivation" := rfl
example : label .baselineSpineDemand = "baselineSpineDemand" := rfl
example : label .canonicalPairLedger = "canonicalPairLedger" := rfl
example : label .sparsePairExit = "sparsePairExit" := rfl
example : label .canonicalBlockerRoute = "canonicalBlockerRoute" := rfl
example : label .sparseUpperEnvelope = "sparseUpperEnvelope" := rfl
example : label .capacityTokenLedger = "capacityTokenLedger" := rfl
example : label .roleFibrePartition = "roleFibrePartition" := rfl
example : label .fibrePressure = "fibrePressure" := rfl
example : label .spineSurplusEstimate = "spineSurplusEstimate" := rfl
example : label .sparsePressureNearCubic = "sparsePressureNearCubic" := rfl
example : label .sparsePressureOverload = "sparsePressureOverload" := rfl
example : label .windowClassOverload = "windowClassOverload" := rfl
example : label .windowClassAbsent = "windowClassAbsent" := rfl
example : label .remainderClassOverload = "remainderClassOverload" := rfl
example : label .remainderClassAbsent = "remainderClassAbsent" := rfl
example : label .windowIncidenceAudit = "windowIncidenceAudit" := rfl
example : label .remainderSurplusAudit = "remainderSurplusAudit" := rfl
example : label .primitiveCarrierAudit = "primitiveCarrierAudit" := rfl
example : label .primitiveClassOverload = "primitiveClassOverload" := rfl
example : label .quantitativeOverload = "quantitativeOverload" := rfl
example : label .homogeneousCapsHold = "homogeneousCapsHold" := rfl
example : label .homogeneousBottleneckPattern = "homogeneousBottleneckPattern" := rfl
example : label .bottleneckRouting = "bottleneckRouting" := rfl
example : label .typeBHandoff = "typeBHandoff" := rfl
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
example : label .admissibleRankQuotient = "admissibleRankQuotient" := rfl
example : label .functionalRankQuotient = "functionalRankQuotient" := rfl
example : label .barrierEnumeration = "barrierEnumeration" := rfl
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
  | .barrierEnumeration => 211
  | .windowPackageSeparated => 35
  | .forcedCurvatureCost => 37
  | .remainderEntropyHigh => 38
  | .remainderEntropyLow => 39
  | .entropyPackageDemand => 40
  | .entropyCapActive => 41
  | .largeBudgetResidual => 42
  | .netChargeLarge => 146
  | .netChargeSmall => 147
  | .netChargeCap => 145
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
  | .typeAUnsaturatedDischarge => 148
  | .typeAPortReturn => 121
  | .typeAVisibleEntry => 56
  | .typeAVisibleFirstExcess => 57
  | .typeAVisibleEntryClause => 122
  | .typeAExitOneReturn => 58
  | .typeAExitOneFree => 59
  | .typeAExitTwoTheta => 60
  | .typeAExitTwoFree => 61
  | .typeAExitThreeCollision => 62
  | .typeAExitThreeFree => 63
  | .typeASaturatedExitEntry => 123
  | .typeAExitSevenHandoff => 124
  | .typeAExitSevenFree => 125
  | .coldFailureCycle => 64
  | .coldFailureDefect => 65
  | .coldFailureCompression => 66
  | .coldFailureHandoff => 67
  | .coldFailureRouting => 68
  | .coldExchangeBound => 177
  | .coldWindowLedgerSplit => 178
  | .coldRoute8Below => 212
  | .coldRoute8AtOrAbove => 213
  | .coldHotEntropyOverflow => 214
  | .coldHotEntropyCap => 215
  | .coldMass => 216
  | .coldAmbientCubic => 217
  | .coldStubExcess => 218
  | .coldGermCandidates => 219
  | .coldSelectedBranchExcess => 179
  | .coldAmbientCubicStubExcess => 180
  | .coldPositiveGerm => 182
  | .coldHandoffTransfer => 69
  | .coldGermExtraction => 70
  | .coldGermRouted => 71
  | .coldTerminalResidual => 183
  | .coldBranchClosed => 176
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
  | .typeBB2Choice => 149
  | .typeBDisjointLedger => 150
  | .typeBSelectedFanCharge => 175
  | .typeBOverlapObstruction => 84
  | .fanCertificateResidualMass => 186
  | .typeBOverlapObstructionMass => 187
  | .typeBExclusionResidualMass => 188
  | .typeBBridgeMass => 85
  | .typeBBridgeSublinear => 189
  | .branchKillClosed => 191
  | .typeBExclusionCharge => 164
  | .typeBExcluded => 166
  | .typeBExclusionResidual => 167
  | .typeAExitFour => 94
  | .typeAExitFourPeeled => 151
  | .typeAExitFourFiniteDescent => 153
  | .typeASaturatedHandoffVisible => 154
  | .typeASaturatedHandoffSilent => 155
  | .typeASaturatedHandoffExitFour => 156
  | .typeASaturatedHandoffExitFourFree => 157
  | .typeAExitFourReceiverDischarged => 152
  | .typeAExitFourFree => 95
  | .typeAExitFive => 96
  | .typeAExitFiveFree => 97
  | .typeAExitSix => 98
  | .typeAExitSixFree => 99
  | .typeAExitSixProper => 100
  | .typeAExitSixGlobal => 101
  | .typeAExitSevenProduced => 158
  | .route8Residual => 102
  | .route8ResidualProfile => 159
  | .route8GlobalSqueeze => 160
  | .route8BasinBurden => 161
  | .route8LargeBudgetDeficit => 162
  | .route8CarrierCore => 163
  | .route8SmallCoreCollapse => 168
  | .route8TwoCarrierReduction => 169
  | .route8CarrierDeletionWitnesses => 170
  | .route8PrivateCarrierBudget => 171
  | .route8NoTwoCarrierContradiction => 172
  | .route8PressureDescent => 173
  | .route8TerminalResidual => 185
  | .route8TerminalNoGo => 174
  | .largeBudgetRoute8Closed => 190
  | .sparseSlackSurplus => 109
  | .activeSurplusFamily => 110
  | .sparsePortActivation => 111
  | .baselineSpineDemand => 112
  | .canonicalPairLedger => 113
  | .sparsePairExit => 143
  | .canonicalBlockerRoute => 144
  | .sparseUpperEnvelope => 129
  | .capacityTokenLedger => 114
  | .roleFibrePartition => 115
  | .fibrePressure => 116
  | .spineSurplusEstimate => 126
  | .sparsePressureNearCubic => 127
  | .sparsePressureOverload => 128
  | .windowClassOverload => 130
  | .windowClassAbsent => 131
  | .remainderClassOverload => 132
  | .remainderClassAbsent => 133
  | .windowIncidenceAudit => 134
  | .remainderSurplusAudit => 135
  | .primitiveCarrierAudit => 136
  | .primitiveClassOverload => 139
  | .quantitativeOverload => 137
  | .homogeneousCapsHold => 140
  | .homogeneousBottleneckPattern => 141
  | .bottleneckRouting => 142
  | .typeBHandoff => 184
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
  | .admissibleRankQuotient => 208
  | .functionalRankQuotient => 209
  | .targetRankCircuit => 210

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
  | 37 => .forcedCurvatureCost
  | 38 => .remainderEntropyHigh
  | 39 => .remainderEntropyLow
  | 40 => .entropyPackageDemand
  | 41 => .entropyCapActive
  | 42 => .largeBudgetResidual
  | 146 => .netChargeLarge
  | 147 => .netChargeSmall
  | 145 => .netChargeCap
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
  | 148 => .typeAUnsaturatedDischarge
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
  | 177 => .coldExchangeBound
  | 178 => .coldWindowLedgerSplit
  | 212 => .coldRoute8Below
  | 213 => .coldRoute8AtOrAbove
  | 214 => .coldHotEntropyOverflow
  | 215 => .coldHotEntropyCap
  | 216 => .coldMass
  | 217 => .coldAmbientCubic
  | 218 => .coldStubExcess
  | 219 => .coldGermCandidates
  | 179 => .coldSelectedBranchExcess
  | 180 => .coldAmbientCubicStubExcess
  | 182 => .coldPositiveGerm
  | 183 => .coldTerminalResidual
  | 69 => .coldHandoffTransfer
  | 70 => .coldGermExtraction
  | 71 => .coldGermRouted
  | 176 => .coldBranchClosed
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
  | 149 => .typeBB2Choice
  | 150 => .typeBDisjointLedger
  | 175 => .typeBSelectedFanCharge
  | 84 => .typeBOverlapObstruction
  | 186 => .fanCertificateResidualMass
  | 187 => .typeBOverlapObstructionMass
  | 188 => .typeBExclusionResidualMass
  | 85 => .typeBBridgeMass
  | 189 => .typeBBridgeSublinear
  | 191 => .branchKillClosed
  | 164 => .typeBExclusionCharge
  | 166 => .typeBExcluded
  | 167 => .typeBExclusionResidual
  | 94 => .typeAExitFour
  | 151 => .typeAExitFourPeeled
  | 153 => .typeAExitFourFiniteDescent
  | 154 => .typeASaturatedHandoffVisible
  | 155 => .typeASaturatedHandoffSilent
  | 156 => .typeASaturatedHandoffExitFour
  | 157 => .typeASaturatedHandoffExitFourFree
  | 152 => .typeAExitFourReceiverDischarged
  | 95 => .typeAExitFourFree
  | 96 => .typeAExitFive
  | 97 => .typeAExitFiveFree
  | 98 => .typeAExitSix
  | 99 => .typeAExitSixFree
  | 100 => .typeAExitSixProper
  | 101 => .typeAExitSixGlobal
  | 158 => .typeAExitSevenProduced
  | 102 => .route8Residual
  | 159 => .route8ResidualProfile
  | 160 => .route8GlobalSqueeze
  | 161 => .route8BasinBurden
  | 162 => .route8LargeBudgetDeficit
  | 163 => .route8CarrierCore
  | 168 => .route8SmallCoreCollapse
  | 169 => .route8TwoCarrierReduction
  | 170 => .route8CarrierDeletionWitnesses
  | 171 => .route8PrivateCarrierBudget
  | 172 => .route8NoTwoCarrierContradiction
  | 173 => .route8PressureDescent
  | 185 => .route8TerminalResidual
  | 174 => .route8TerminalNoGo
  | 190 => .largeBudgetRoute8Closed
  | 109 => .sparseSlackSurplus
  | 110 => .activeSurplusFamily
  | 111 => .sparsePortActivation
  | 112 => .baselineSpineDemand
  | 113 => .canonicalPairLedger
  | 143 => .sparsePairExit
  | 144 => .canonicalBlockerRoute
  | 129 => .sparseUpperEnvelope
  | 114 => .capacityTokenLedger
  | 115 => .roleFibrePartition
  | 116 => .fibrePressure
  | 130 => .windowClassOverload
  | 131 => .windowClassAbsent
  | 132 => .remainderClassOverload
  | 133 => .remainderClassAbsent
  | 134 => .windowIncidenceAudit
  | 135 => .remainderSurplusAudit
  | 136 => .primitiveCarrierAudit
  | 139 => .primitiveClassOverload
  | 137 => .quantitativeOverload
  | 140 => .homogeneousCapsHold
  | 141 => .homogeneousBottleneckPattern
  | 142 => .bottleneckRouting
  | 184 => .typeBHandoff
  | 118 => .homogeneousBottleneck
  | 119 => .sparseSurplusSurvivor
  | 120 => .activeSurplusDemands
  | 121 => .typeAPortReturn
  | 122 => .typeAVisibleEntryClause
  | 123 => .typeASaturatedExitEntry
  | 124 => .typeAExitSevenHandoff
  | 125 => .typeAExitSevenFree
  | 126 => .spineSurplusEstimate
  | 127 => .sparsePressureNearCubic
  | 128 => .sparsePressureOverload
  | 200 => .hotColdPartition
  | 201 => .dependentPairFamily
  | 202 => .independentPairFamily
  | 203 => .mixedSparseSpineDependence
  | 204 => .exactCubicBaselineBudget
  | 205 => .incrementalSkeletonRoom
  | 206 => .skeletonDominates
  | 207 => .exactResponseProfile
  | 208 => .admissibleRankQuotient
  | 209 => .functionalRankQuotient
  | 210 => .targetRankCircuit
  | 211 => .barrierEnumeration
  | _ => .selection

theorem ofIdx_idx (k : Key) : ofIdx (idx k) = k := by
  cases k <;> rfl

theorem idx_injective : Function.Injective idx :=
  Function.LeftInverse.injective ofIdx_idx

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys.  The name carries the key's audit index as its final
component, so distinctness is inherited from `idx_injective` instead of being
re-derived by a pairwise comparison of the audit labels. -/
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
  | .entropyPackageDemand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyPackageDemand") 40
  | .entropyCapActive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "entropyCapActive") 41
  | .largeBudgetResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "largeBudgetResidual") 42
  | .netChargeLarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeLarge") 146
  | .netChargeSmall =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeSmall") 147
  | .netChargeCap =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "netChargeCap") 145
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
  | .typeAUnsaturatedDischarge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAUnsaturatedDischarge") 148
  | .typeAPortReturn =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAPortReturn") 121
  | .typeAVisibleEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAVisibleEntry") 56
  | .typeAVisibleFirstExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAVisibleFirstExcess") 57
  | .typeAVisibleEntryClause =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAVisibleEntryClause") 122
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
  | .typeAExitSevenFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitSevenFree") 125
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
  | .coldExchangeBound =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldExchangeBound") 177
  | .coldWindowLedgerSplit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldWindowLedgerSplit") 178
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
  | .coldSelectedBranchExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldSelectedBranchExcess") 179
  | .coldAmbientCubicStubExcess =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldAmbientCubicStubExcess") 180
  | .coldHandoffTransfer =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldHandoffTransfer") 69
  | .coldGermExtraction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermExtraction") 70
  | .coldPositiveGerm =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldPositiveGerm") 182
  | .coldGermRouted =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGermRouted") 71
  | .coldTerminalResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldTerminalResidual") 183
  | .coldBranchClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldBranchClosed") 176
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
  | .typeBB2Choice =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBB2Choice") 149
  | .typeBDisjointLedger =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBDisjointLedger") 150
  | .typeBSelectedFanCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBSelectedFanCharge") 175
  | .typeBOverlapObstruction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBOverlapObstruction") 84
  | .fanCertificateResidualMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "fanCertificateResidualMass") 186
  | .typeBOverlapObstructionMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBOverlapObstructionMass") 187
  | .typeBExclusionResidualMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBExclusionResidualMass") 188
  | .typeBBridgeMass =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBBridgeMass") 85
  | .typeBBridgeSublinear =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBBridgeSublinear") 189
  | .branchKillClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "branchKillClosed") 191
  | .typeBExclusionCharge =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBExclusionCharge") 164
  | .typeBExcluded =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBExcluded") 166
  | .typeBExclusionResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeBExclusionResidual") 167
  | .typeAExitFour =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeAExitFour") 94
  | .typeAExitFourPeeled =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourPeeled") 151
  | .typeAExitFourFiniteDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourFiniteDescent") 153
  | .typeASaturatedHandoffVisible =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffVisible") 154
  | .typeASaturatedHandoffSilent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffSilent") 155
  | .typeASaturatedHandoffExitFour =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffExitFour") 156
  | .typeASaturatedHandoffExitFourFree =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeASaturatedHandoffExitFourFree") 157
  | .typeAExitFourReceiverDischarged =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitFourReceiverDischarged") 152
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
  | .typeAExitSevenProduced =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitSevenProduced") 158
  | .route8Residual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Residual") 102
  | .route8ResidualProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8ResidualProfile") 159
  | .route8GlobalSqueeze =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8GlobalSqueeze") 160
  | .route8BasinBurden =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8BasinBurden") 161
  | .route8LargeBudgetDeficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8LargeBudgetDeficit") 162
  | .route8CarrierCore =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8CarrierCore") 163
  | .route8SmallCoreCollapse =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8SmallCoreCollapse") 168
  | .route8TwoCarrierReduction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8TwoCarrierReduction") 169
  | .route8CarrierDeletionWitnesses =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8CarrierDeletionWitnesses") 170
  | .route8PrivateCarrierBudget =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8PrivateCarrierBudget") 171
  | .route8NoTwoCarrierContradiction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8NoTwoCarrierContradiction") 172
  | .route8PressureDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8PressureDescent") 173
  | .route8TerminalResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8TerminalResidual") 185
  | .route8TerminalNoGo =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8TerminalNoGo") 174
  | .largeBudgetRoute8Closed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "largeBudgetRoute8Closed") 190
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
  | .windowClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowClassOverload") 130
  | .windowClassAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowClassAbsent") 131
  | .remainderClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "remainderClassOverload") 132
  | .remainderClassAbsent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderClassAbsent") 133
  | .windowIncidenceAudit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "windowIncidenceAudit") 134
  | .remainderSurplusAudit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "remainderSurplusAudit") 135
  | .primitiveCarrierAudit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "primitiveCarrierAudit") 136
  | .primitiveClassOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "primitiveClassOverload") 139
  | .quantitativeOverload =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "quantitativeOverload") 137
  | .homogeneousCapsHold =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "homogeneousCapsHold") 140
  | .homogeneousBottleneckPattern =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "homogeneousBottleneckPattern") 141
  | .bottleneckRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "bottleneckRouting") 142
  | .typeBHandoff =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBHandoff") 184
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
  | .admissibleRankQuotient =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "admissibleRankQuotient") 208
  | .functionalRankQuotient =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "functionalRankQuotient") 209
  | .targetRankCircuit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "targetRankCircuit") 210

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

/-- The residual domain of a minimum-degree cycle spine. -/
abbrev Input (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :=
  Core.Strategy.ProblemInput
    (problem BranchState Presentation presentation data)

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

end Hypostructure.Graph.Strategy.Spine
