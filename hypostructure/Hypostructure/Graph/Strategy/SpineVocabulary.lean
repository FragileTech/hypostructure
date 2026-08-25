import Mathlib.Combinatorics.SimpleGraph.Metric
import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.FiniteEdgeBudget
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.RemainderGlue
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.WindowStubStructure
import Hypostructure.Graph.BarrierOverlapSystem
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
import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.Route8Deficit
import Hypostructure.Graph.Route8Pressure
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.TraceBasinAlternatives
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
import Hypostructure.Graph.WindowCurvatureEnumeration
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
import Hypostructure.Graph.BlockedClass
import Hypostructure.Graph.CanonicalRealization
import Hypostructure.Graph.TwoStrandEnumeration

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
  /-- The paper's registered cubic baseline. -/
  threshold_eq_three : threshold = 3
  /-- Stirling's `⌈e⌉` against the registered baseline; see the note above. -/
  three_le_threshold : 3 ≤ threshold
  /-- The accepted cycle lengths the counterexample must avoid. -/
  LengthOK : Nat → Prop
  /-- The order of the induced obstruction window.  For `thm:p13free` this is
  the induced-path order; nothing here knows its value. -/
  windowOrder : Nat
  windowOrder_pos : 0 < windowOrder
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
  The boundary-degree profile alphabet is not registered as a free carrier:
  `T(p)` has `threshold` canonically ordered vertices and each internal degree
  is below `threshold`, so the alphabet is the derived type
  `Fin threshold → Fin threshold`.  The `P₁₃` label is likewise derived as
  `Graph.WindowCurvature.Label windowOrder`.  The other five coordinates are
  framework finite alphabets.  Consequently the routing alphabet, and hence
  `Q_geom`, is determined by the problem's threshold and window order.

  `Q_geom` is registered as a number so strategy arithmetic never evaluates
  the potentially enormous `Fintype` enumeration. -/
  routingLabelBound : Nat
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
  /-- The registered fixed response-coordinate signature. -/
  coldSignature : Graph.ColdCorridor.DeclaredSignature
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

/-- The paper's bounded-port boundary profile alphabet, derived from the
registered baseline rather than supplied by a problem. -/
abbrev Data.BoundaryProfile (data : Data.{u}) : Type :=
  Fin data.threshold → Fin data.threshold

/-- Finiteness of the derived profile alphabet. -/
@[reducible] noncomputable def Data.boundaryProfileFintype (data : Data.{u}) :
    Fintype data.BoundaryProfile := inferInstance

/-- The derived alphabet is inhabited because every admitted presentation has
positive baseline degree. -/
@[reducible] def Data.boundaryProfileInhabited (data : Data.{u}) :
    Inhabited data.BoundaryProfile := by
  have positive : 0 < data.threshold := lt_of_lt_of_le (by omega) data.three_le_threshold
  exact ⟨fun _ => ⟨0, positive⟩⟩

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
  /-- The registered problem presentation identifies the spine threshold with
  the paper's cubic baseline. -/
  | cubicBaseline
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
  /-- Node `[11]`, `lem:degree-profile-fibres`: every target-complete
  identification of two boundaried pieces stays inside one boundary-degree
  fibre. -/
  | degreeProfileFibres
  /-- Node `[12]`, `lem:context-universality`: every target-complete
  identification has the same target response in every outside context. -/
  | targetCompleteContextUniversality
  /-- Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller
  boundary-signature-preserving replacement with one-way obstruction
  inclusion. -/
  | replacementExclusion
  /-- Node `[14]`: no proper atom admits a nontrivial target-complete
  compression (`cor:uncompressible`). -/
  | uncompressible
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
  /-- Node `[31]`, `def:admissible-rank-quotient` at the remainder of every
  maximal packing: a rank-reducing admissible rank quotient of the raw
  curvature family is represented by a strictly smaller proper representative
  or by a strictly smaller admissible closed representative. -/
  | admissibleRankQuotient
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
  That certificate is the object nodes `[36]`, `[38]` and `[40]` route. -/
  | branchDependence
  /-- Node `[35]`, `lem:separated-testers`: corresponding internal wedges in
  vertex-disjoint isomorphic rooted balls can be tested only by the outside
  side of their boundaried decomposition; any quotient identifying the two
  wedge labels is context-universal or has a concrete target-defect witness. -/
  | separatedTesters
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
  /-- The `[113]`-tested quotient-freeness of the unified census: no entry's
  selected basin carries the plain trace-response quotient (the cased
  exit-`(5)` state).  The yes arm makes every unified entry route-8 or
  alternative-(a); the no arm is the manuscript's profile-record residual. -/
  | route8QuotientFree
  /-- The exact negation, retained as the tested residual state
  (`def:typeA-two-terminal-pressure-records`' profile lane). -/
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
  | coldFailureDefect
  | coldFailureCompression
  | coldFailureHandoff
  | coldFailureRouting
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
  `prop:p13-density`'s "since all target-complete window states are realized by
  labelled near-cubic skeletons under `def:near-cubic-spine`": the canonical
  multi-scale package of the fixed maximal packing is a family of independently
  target-testable coordinates, i.e. its full package code is realized canonically
  by the labelled skeletons of the current object's class `𝒢_{n,m}`. -/
  | windowPackageRealized
  /-- The complementary arm of the `[21]` realization decision: the fixed
  maximal packing's full package code is *not* realized canonically by the
  labelled skeletons of the current object's class — the residual on which the
  manuscript's `[21]` sentence fails, carried as a branch of its own. -/
  | windowPackageUnrealized
  /-- Node `[159]`: the no-arm of `[158]`, after comparison with the labelled
  skeleton class: the canonical window-package demand strictly exceeds the
  exact skeleton budget. -/
  | densePackingOverflow
  /-- On the `[21]` unrealized residual: `prop:negative-net-charge`'s exact
  large-budget net-deficiency comparison holds at the fixed maximal packing —
  the manuscript's `τ(θ) < 1/4` deficiency reading with the exact `√n`
  allowance, i.e. the inequality node `[56]` supplies to `[57]`--`[62]`. -/
  | denseDeficiencyBelow
  /-- Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact
  allowance, on which the net-charge collision does not fire. -/
  | denseDeficiencyAtOrAbove
  /-- Node `[167]`, the stub structure of the ambient-cubic cold windows: at
  most two endpoints carry `δ − 1` external stubs and every other window vertex
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
  /-- `lem:refined-minimality-swap`, size-reducing case (node `[165]`): some
  neutral germ's corridor piece has a canonical representative with strictly
  fewer internal vertices, so the exchange is a strictly smaller counterexample. -/
  | coldCanonicalSwapSmaller
  /-- The exact complement: every neutral germ's canonical representative has
  the same internal size as its corridor piece — the same-size tie-break of node
  `[166]`. -/
  | coldCanonicalSwapSameSize
  /-- Node `[169]`, `def:blocked-class`: on the trivial neutral germ residual the
  object's own labelled skeleton lies in the blocked class `𝓑(𝒫)` of the fixed
  maximal packing (near-cubic, windows present, no accepted cycle through a
  window), and `card 𝓑(𝒫) ≤ skeletonBudget`. -/
  | blockedClassMember
  /-- Node `[170]`, `lem:scale-additivity`: on the blocked class of the fixed
  packing the conditional savings of the barrier states add at every fixed
  scale -- the barrier code is injective, every conditional fibre is within the
  surviving count `F_{a,b}` of the registered barrier list, and the outside code
  against the a-priori range is dominated by the labelled skeleton class. -/
  | blockedScaleAdditive
  /-- Node `[170]`, the exact complement (`lem:barrier-failure-overlap`): the
  conditional saving fails to add at some fixed scale, so the current
  conditional fibre contains a minimal barrier overlap obstruction. -/
  | blockedBarrierOverlap
  /-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii): on the absorbed-germ
  residual no selected branch-excess half-edge has a subcubic first-failure
  support — every selected corridor meets a vertex of degree above the
  threshold, a heavy centre, and is decorated handoff fan data for Type B. -/
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
  | coldSelectedBranchExcess
  | coldAmbientCubicStubExcess
  | coldHandoffTransfer
  | coldGermExtraction
  | coldPositiveGerm
  | coldGermRouted
  | coldBranchClosed
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
  /-- Node `[76]`/`[85]`, closed arm: the selected Type B ledger gives
  nonnegative net charge. -/
  | typeBExcluded
  /-- Node `[76]`/`[85]`, surviving arm: the Type B exclusion hypotheses are not
  all discharged on the selected B2 branch. -/
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
  /-- Node `[107]`, yes arm: the selected saturated-handoff residual, after
  exits `(4)`--`(6)` have failed, produces the exit-`(7)` decorated handoff
  envelope.  Node `[108]` records the handoff, and node `[65]` commits its
  admissibility interface. -/
  | typeAExitSevenProduced
  /-- Node `[110]`, exit `(8)`: the selected route-8 residual satisfies the
  silent-core residual profile.  This is a semantic fact about the selected
  residual state, not an indexed carrier or basin transport object. -/
  | route8ResidualProfile
  /-- Node `[111]`: the selected route-`8` packing determines the canonical
  Type A subcollection whose saturated receivers survive only through route
  `8`, together with the cleared value of `D_A` on that collection. -/
  | route8GlobalSqueeze
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
  /-- Nodes `[121]`--`[122]`: the no-two-carrier branch contradicts the
  route-`8` burden/deficit and registered rate facts. -/
  | route8NoTwoCarrierContradiction
  /-- Node `[124]`: the terminal two-carrier route-`8` no-go.  Carrier-deletion
  witnesses become canonical Q5 exit-`(4)` witnesses, contradicting the
  no-exit-`(4)` fact of the same true route-`8` residual. -/
  | route8TerminalNoGo
  /-- Nodes `[111]`--`[113]` and `[120]`: the object-level census of the
  extracted Type A collection `𝒳_A` — the deficit `|R| ≤ N_basin + s·|∂R|`
  (`lem:typeA-route8-burden` in `def:typeA-large-budget-deficit`) and the
  private-carrier rate `((δ+1)s+1)·|∂R| < (δ+1)·|R|` (`τ < 3/13`), at the fixed
  maximal packing. -/
  | route8Census
  /-- The later unified-demand deficit reading used at node `[123]`,
  `|R| ≤ N_basin + s·|∂R| + F·s·T(n)` — `def:typeA-large-budget-deficit` with
  `lem:typeA-route8-burden` and the Type B bridge mass of
  `prop:typeB-bridge-sublinear` (`o(|R|)`, the registered `F·s·T(n)`). -/
  | route8Deficit
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
  node `[111]`, whose sole output is `route8GlobalSqueeze`. -/
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
  /-- Node `[123]`, `def:typeA-open-window-blocker` with
  `lem:typeA-open-window-blocker-count`: every open demand unit of the
  committed absorption is assigned a packed window through a boundary
  incidence of its component support, and the open demand is exactly the
  window-blocker load partition `𝖯_open = Σ_P B_open(P)`. -/
  | route8WindowBlockers
  /-- Node `[181]`: the explicit residual left by node `[123]` after exact
  peeling accounting, the maximal 2/3-demand ledger, demand absorption, and
  packed-window blocker accounting. -/
  | route8PeeledDemandResidual
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
  /-- Node `[123]`, `lem:typeA-visible-entry` at the unified collection: a
  visible excess load of a collection piece carries the canonical exit-`(4)`
  witness (clause (Q1) of `def:typeA-exit4-family`), because exits
  `(1)`--`(3)`, `(5)`, `(6)` are standing-invariant contradictions and the
  collection produces no Type B handoff (`rem:unified-covers-exit4`). -/
  | route8VisibleExitFourRouting
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
  /-- Node `[131]`, yes arm: `prop:sparse-entropy-sandwich`'s entropy count at
  the full pair schedule holds — the mixed spine/pair family's `2^k` code is
  realized among the labelled skeletons of the current object. -/
  | freePairEntropySandwich
  /-- Node `[131]`, complementary arm: the residual on which that count fails
  (the free-pair code is not realized by the skeleton class), carried as a
  branch of its own. -/
  | freePairCodeUnrealized
  /-- Node `[137]`, yes arm of the entropy count at every declared capacity
  presentation: `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)` for the ledger's free side. -/
  | blockedPairEntropySandwich
  /-- Node `[137]`, complementary arm: at some declared presentation the free
  side's code is not realized by the skeleton class; carried as a branch. -/
  | blockedPairCodeUnrealized
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
  /-- Node `[140]`, the window-incidence geometric audit: a token of `𝔗_W` whose
  load exceeds `Cap_hom(L_geom)` carries a role-homogeneous `L_geom`-matching or
  `L_geom`-star, at the counted routing-label alphabet of
  `def:same-token-routing-germs`. -/
  | windowIncidenceAudit
  /-- Node `[142]`, the remainder-surplus geometric audit, at `𝔗_R`. -/
  | remainderSurplusAudit
  /-- Node `[143]`, the primitive-carrier geometric audit, at `𝔗_prim`. -/
  | primitiveCarrierAudit
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
  /-- Node `[144]`, `lem:same-token-bottleneck-routing` itself: the concrete
  homogeneous pattern in the current object's canonical capacity presentation
  yields a sparse-surplus exit or the common Type B fan-ledger entry. -/
  | bottleneckRouting
  /-- Node `[144]`, the survivor specialization of the preceding fact: the
  sparse-exit arm is impossible, so the same current object is entered directly
  in the Type B fan ledger. -/
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

/-- **The bookkeeping enlargement `C ∪ Z`.**

The paper's connected determination support `Z` is `quotient.support`.  This
union is used only at node `[40]` to retain the already-recorded piece `C`
while witnessing that the certificate reaches outside it.  In particular, it
is not the support classified by node `[41]` and it is not the domain of the
closed exact profile at node `[43]`. -/
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

/-- **`C ∪ Z ⊋ C` when the certificate reaches outside `C`**, the bookkeeping
witness retained by node `[40]`. -/
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
    (object.internalEdgeCount (object.remainderSupport packing))
    (object.remainderSupport packing).card


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

/-- The per-window width of the separated multi-scale package of
`lem:p13-window-package`: the certified table's aggregate safe/flat ratio,
compounded across the selected dyadic scales and only then floored — the
manuscript's `(c₁₃ − o(1)) log₂ n` bits per packed window. -/
noncomputable def windowPackageBits (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact Nat.log2
    ((Core.Finite.CertifiedTableAggregation.safeProduct data.windowBarrier.table ^
        data.separatedScaleCount object.vertexCount - 1) /
      Core.Finite.CertifiedTableAggregation.flatProduct data.windowBarrier.table ^
        data.separatedScaleCount object.vertexCount)

/-- The manuscript fixes one maximal packing before splitting it.  This is the
canonical finite choice of that packing, hence every later key names the same
family without transporting a witness outside the ledger. -/
noncomputable def canonicalWindowPacking (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) :=
  Classical.choose (object.exists_windowPacking_card_eq data.windowOrder)

/-- **The code of the canonical entropy comparison retained by a window
family** (`def:cold-window-ledger`, `def:remainder-entropy`,
`def:curvature-target-rank`): the full canonical package of every window of the
family (`windowPackageBits` per window, `lem:p13-window-package`), the
remainder states of the fixed maximal packing's remainder, and the exact code of
its raw curvature tests (`c_Ω` bits per test of `r_Ω(R)`), multiplied — the
number of target-complete states the comparison has to distinguish for that
family. -/
noncomputable def retainedCode (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Nat :=
  2 ^ (windowPackageBits data object * family.card) *
      remainderStates data object (canonicalWindowPacking data object) *
    2 ^ (data.curvatureCost *
      remainderCurvatureTargetRank data object (canonicalWindowPacking data object))

/-! The realization test of node `[158]` and the retained-code predicate of
node `[22]` are separate.  The first is exactly the single
window-package inequality displayed in `def:window-realization-test`; the
latter additionally retains the remainder and curvature code. -/

/-- **`def:window-realization-test`, nodes `[158]`--`[159]`.**  The canonical
window-package states of a family are realized by labelled skeletons.  This is
only the paper's package-count clause; the stronger retained-code clause is
`WindowFamilyRealized` below and belongs to the hot/cold ledger. -/
def WindowPackageRealized (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Prop :=
  ∃ (State : Type u)
    (stateOf : Graph.PackedWindowRealization.Skeleton
      object.vertexCount object.edgeCount → State),
    2 ^ (windowPackageBits data object * family.card) ≤
      Nat.card (Set.range stateOf)

/-- **`def:cold-window-ledger` / `def:curvature-target-rank`: a window family
retained in the canonical entropy comparison.**  The comparison's code for the
family — its full canonical window packages together with the remainder states
and the exact curvature code of the fixed packing (`retainedCode`) — is
realized canonically by the labelled skeletons of the current object's own
class `𝒢_{n,m}`: an assignment of target-complete states to skeletons whose
range has at least the family's window package states (`lem:p13-window-package`,
the live-hot comparison of nodes `[22]`--`[23]`) and at least the retained
code.  This is `def:target-rank`'s "independently
target-testable … arising canonically from graphs in the labelled class", the
exact-code equality `def:curvature-target-rank` says is retained on the surviving
hot residual, and precisely the premise `lem:independent-target-entropy`
consumes; its failure is what makes a window cold. -/
def WindowFamilyRealized (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Prop :=
  ∃ (State : Type u)
    (stateOf : Graph.PackedWindowRealization.Skeleton
      object.vertexCount object.edgeCount → State),
    2 ^ (windowPackageBits data object * family.card) ≤ Nat.card (Set.range stateOf) ∧
      retainedCode data object family ≤ Nat.card (Set.range stateOf)

/-- Retention is monotone: a subfamily of a retained family is retained (its
package code and its retained code are both no larger). -/
theorem WindowFamilyRealized.mono {data : Data.{u}} {object : Graph.FiniteObject.{u}}
    {smaller larger : Finset (Finset object.Vertex)} (subset : smaller ⊆ larger)
    (realized : WindowFamilyRealized data object larger) :
    WindowFamilyRealized data object smaller := by
  obtain ⟨State, stateOf, packageLe, codeLe⟩ := realized
  have cardLe := Finset.card_le_card subset
  refine ⟨State, stateOf, ?_, ?_⟩
  · exact le_trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ cardLe)) packageLe
  · refine le_trans ?_ codeLe
    unfold retainedCode
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ cardLe)))

/-- The manuscript's canonical entropy comparison retains a canonical maximal
retained subfamily of the fixed maximal packing; the choice function below is
that lexicographic tie-break.  When the comparison realizes no family's code —
not even the empty family's remainder-and-curvature code — every packed window is
cold: `def:curvature-target-rank`'s "its failure is the complementary cold
residual". -/
theorem exists_maximal_windowFamilyRealized (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    ∃ hot : Finset (Finset object.Vertex),
      hot ⊆ canonicalWindowPacking data object ∧
        (WindowFamilyRealized data object hot ∨
          (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
        ∀ other : Finset (Finset object.Vertex),
          other ⊆ canonicalWindowPacking data object →
            WindowFamilyRealized data object other → other.card ≤ hot.card := by
  classical
  by_cases emptyRealized : WindowFamilyRealized data object ∅
  · obtain ⟨hot, memHot, maximal⟩ := Finset.exists_max_image
      ((canonicalWindowPacking data object).powerset.filter
        (WindowFamilyRealized data object)) Finset.card
      ⟨∅, by simp [Finset.mem_filter, emptyRealized]⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at memHot
    refine ⟨hot, memHot.1, Or.inl memHot.2, fun other subset realized => ?_⟩
    exact maximal other (by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨subset, realized⟩)
  · refine ⟨∅, Finset.empty_subset _, Or.inr ⟨rfl, emptyRealized⟩,
      fun other _subset realized => ?_⟩
    -- A realized family's code dominates the empty family's code, so the empty
    -- family would be realized too.
    exfalso
    obtain ⟨State, stateOf, packageLe, codeLe⟩ := realized
    refine emptyRealized ⟨State, stateOf, ?_, le_trans ?_ codeLe⟩
    · simp only [Finset.card_empty, Nat.mul_zero, pow_zero]
      exact le_trans Nat.one_le_two_pow packageLe
    · simp only [retainedCode, Finset.card_empty, Nat.mul_zero, pow_zero, Nat.one_mul]
      refine Nat.mul_le_mul_right _ ?_
      calc remainderStates data object (canonicalWindowPacking data object)
          = 1 * remainderStates data object (canonicalWindowPacking data object) := by
            rw [Nat.one_mul]
        _ ≤ 2 ^ (windowPackageBits data object * other.card) *
              remainderStates data object (canonicalWindowPacking data object) :=
            Nat.mul_le_mul_right _ Nat.one_le_two_pow

/-- `𝒫_hot`: the canonical maximal subfamily of the fixed packing retained in
the canonical entropy comparison. -/
noncomputable def canonicalHotWindows (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) :=
  Classical.choose (exists_maximal_windowFamilyRealized data object)

/-- `𝒫_cold`: the packed windows not retained in the comparison. -/
noncomputable def canonicalColdWindows (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  exact canonicalWindowPacking data object \ canonicalHotWindows data object

/-- **The joint package demand of nodes `[52]`--`[53]`.**  The window
coordinates of `lem:p13-window-package` retained in the comparison — the hot
windows, at the registered rate — and the remainder states of
`def:remainder-entropy`, multiplied, at the fixed maximal packing: the number of
target-complete states the branch has to distinguish (`prop:two-budget` (a),
`eq:feasibility`, the window-plus-remainder accounting of `prop:p13-density`).
The forced curvature cost of `cor:forced-curvature-cost` is the sharpening of
`def:Theta` that `rem:closure-robust` says the closure does not need: the
curvature patterns are realized by remainder graphs, i.e. by members of the
remainder class already counted, so it is not a further independent factor of
the demand; it stays on the ledger as `K .forcedCurvatureCost`.  `[53]` compares
exactly this demand against the labelled skeleton budget. -/
noncomputable def jointPackageDemand (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Nat :=
  2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        (canonicalHotWindows data object).card) *
    remainderStates data object (canonicalWindowPacking data object)

/-- The hot/cold partition created at node `[22]`, `def:cold-window-ledger`:
`hot` is a maximal retained subfamily of the fixed maximal packing and `cold`
is its complement.  The equivalences prevent a consumer from substituting an
arbitrary partition. -/
def IsHotColdWindowPartition (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing hot cold : Finset (Finset object.Vertex)) : Prop :=
    object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    (∀ support : Finset object.Vertex,
      object.InducesWindow data.windowOrder support →
        ∃ member ∈ packing, ¬ Disjoint support member) ∧
    (hot ⊆ packing ∧
      (WindowFamilyRealized data object hot ∨
        (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
      ∀ other : Finset (Finset object.Vertex), other ⊆ packing →
        WindowFamilyRealized data object other → other.card ≤ hot.card) ∧
    (∀ window, window ∈ cold ↔ window ∈ packing ∧ window ∉ hot) ∧
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
  2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        (canonicalHotWindows data object).card) ≤
      Graph.skeletonBudget object

def BarrierOverflowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.skeletonBudget object <
    2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
      (canonicalHotWindows data object).card)

/-! ## Nodes `[170]`--`[172]`: the barrier states of the blocked class

`lem:scale-additivity` reads the `(a,b)`-barrier state of a packed window at a
separated dyadic scale as a function of the labelled skeleton
(`Graph/BarrierOverlapSystem.lean`), and `lem:blocked-graphs-compress` encodes a
member of `𝓑(𝒫)` as its outside edges together with all those states.  The
a-priori range `W_{a,b}` and the surviving set `F_{a,b}` are the two columns of
the *registered* certified barrier table (`data.windowBarrier`), and the
aggregate saving `c₁₃ = Σ_{a,b} γ_{a,b}` is that table's registered
`binaryRateFloor` (`data.windowRate`); no constant is written here. -/

/-- The packed windows at their labelled positions. -/
noncomputable def blockedWindowLabels (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    Finset (Finset (Fin object.vertexCount)) :=
  Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object)

/-- `𝓑(𝒫)` at the object, the class `def:blocked-class` fixes. -/
@[reducible] noncomputable def blockedClassAt (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Type :=
  Graph.BlockedClass.Blocked object.vertexCount object.edgeCount data.threshold
    data.windowOrder data.LengthOK (blockedWindowLabels data object)

/-- The exposure coordinates of `lem:blocked-graphs-compress`: one per packed
window per separated dyadic scale. -/
@[reducible] noncomputable def blockedCoordinate (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Type :=
  Graph.BarrierSystem.Coordinate (blockedWindowLabels data object)
    (data.separatedScaleCount object.vertexCount)

/-- The registered barrier table's own leg pair `(a,b)` of a row. -/
noncomputable def barrierLegs (data : Data.{u}) :
    data.windowBarrier.Index -> Nat × Nat :=
  fun row =>
    (data.windowBarrier.table.counts.leftLength row,
      data.windowBarrier.table.counts.rightLength row)

/-- `lem:blocked-graphs-compress`'s encoding map at the object. -/
noncomputable def blockedBarrierCode (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    blockedClassAt data object ->
      Finset (Sym2 (Fin object.vertexCount)) ×
        (blockedCoordinate data object ->
          Graph.BarrierSystem.RowStates data.windowOrder data.windowBarrier.Index) :=
  fun member =>
    Graph.BarrierSystem.code data.windowOrder (blockedWindowLabels data object)
      (data.separatedScaleCount object.vertexCount) (barrierLegs data)
      member.1.1.1

/-- `F_{a,b}` over the whole registered barrier list: the surviving states. -/
noncomputable def blockedSurvivingCount (data : Data.{u}) : Nat := by
  letI := data.windowBarrier.indexFintype
  exact Core.Finite.CertifiedTableAggregation.flatProduct data.windowBarrier.table

/-- `W_{a,b}` over the whole registered barrier list: the a-priori range. -/
noncomputable def blockedAprioriCount (data : Data.{u}) : Nat := by
  letI := data.windowBarrier.indexFintype
  exact Core.Finite.CertifiedTableAggregation.safeProduct data.windowBarrier.table

/-- **The canonical encoding order of `lem:blocked-graphs-compress`**: "scale by
scale from `2^{j₁}` to `2^{j_L}` and window by window".  The scale is the major
key, so every coordinate of a smaller scale — and, at the tested scale, every
window before this one — is exposed first.  This is the order
`def:barrier-overlap-system` conditions on. -/
noncomputable def blockedEncodingRank (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : blockedCoordinate data object -> Nat :=
  fun coordinate =>
    (Fintype.equivFin _ coordinate.1).1 +
      coordinate.2.1 * Fintype.card {window // window ∈ blockedWindowLabels data object}

theorem blockedEncodingRank_injective (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    Function.Injective (blockedEncodingRank data object) := by
  classical
  rintro ⟨leftWindow, leftScale⟩ ⟨rightWindow, rightScale⟩ same
  simp only [blockedEncodingRank] at same
  have leftLt : (Fintype.equivFin _ leftWindow).1 <
      Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    (Fintype.equivFin _ leftWindow).2
  have rightLt : (Fintype.equivFin _ rightWindow).1 <
      Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    (Fintype.equivFin _ rightWindow).2
  have positive : 0 < Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) leftLt
  have modEq := congrArg (· % Fintype.card {window // window ∈ blockedWindowLabels data object}) same
  have divEq := congrArg (· / Fintype.card {window // window ∈ blockedWindowLabels data object}) same
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt leftLt,
    Nat.mod_eq_of_lt rightLt] at modEq
  simp only [Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt leftLt,
    Nat.div_eq_of_lt rightLt, Nat.zero_add] at divEq
  have windowEq : leftWindow = rightWindow :=
    (Fintype.equivFin _).injective (Fin.ext modEq)
  have scaleEq : leftScale = rightScale := Fin.ext divEq
  rw [windowEq, scaleEq]

/-- **`lem:scale-additivity`, node `[170]`, verbatim.**  The lemma's dichotomy is
one clause: "the `(a,b)`-barrier state of `P` at scale `2^j` lies in a set of
relative size at most `F_{a,b}/W_{a,b}` of its a-priori range … *or* the current
graph is closed by `lem:system-increment-arithmetic`", and its proof repeats it —
"if every conditional fibre has relative size at most `F_{a,b}/W_{a,b}`,
multiplication of the conditional fibre sizes gives the claimed saving;
otherwise `lem:barrier-failure-overlap` supplies a minimal local overlap
obstruction".

So this is exactly `def:barrier-overlap-system`'s conditional fibre
(`Graph.BarrierSystem.ConditionalFibre`), conditional on the edges outside
the window interiors and on every barrier state exposed before the coordinate in
the canonical encoding order `blockedEncodingRank` (scale by scale, window by
window), bounded by the surviving count of the registered barrier list.

The lemma's conclusion is the second conjunct: "hence the conditional savings
`γ_{a,b}` add over the barriers `(a,b)`, over the `L` scales, and over the `p`
windows".  `γ_{a,b} = log₂(W_{a,b}/F_{a,b})` counts *independently
target-testable coordinates* (`lem:p13-window-package`: "for one window the
package supplies `(Σγ − o(1))log₂n` independently target-testable
coordinates"), so the savings add to `c₁₃·L` per packed window — the registered
`windowPackageBits` — and `lem:blocked-graphs-compress` is exactly
`card 𝓑(𝒫) · 2^{c₁₃p₁₃log₂n} ≤ card 𝒢_{n,m}`.  The class on the right is the
*near-cubic* one, `𝒢^{δ≥3}_{n,m}`: `rem:blocked-class-checks` (a) — "the entropy
step therefore has to be read in the class of labelled graphs with minimum
degree at least three … this is the structure not charged by `C(C(n,2),m)`".
No numeral occurs: the rate is the certified table's own compounded floor. -/
def BlockedScaleAdditivityStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ (member₀ : blockedClassAt data object)
      (coordinate : blockedCoordinate data object),
    Nat.card (Graph.BarrierSystem.ConditionalFibre (blockedBarrierCode data object)
        (blockedEncodingRank data object) member₀ coordinate) ≤
      blockedSurvivingCount data) ∧
    Nat.card (blockedClassAt data object) *
        2 ^ (windowPackageBits data object *
          (canonicalWindowPacking data object).card) ≤
      Nat.card (Graph.BlockedClass.NearCubicSkeleton object.vertexCount
        object.edgeCount data.threshold)

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

/-- **`prop:negative-net-charge`'s large-budget net-deficiency comparison, exact,
at the fixed maximal packing.**  With `p = |𝒫|` and `|R| = n − order·p`, this is
`discharge·(δ·order·p + T(n)) < discharge·2(order−1)·p + |R|`, the strict cap node
`[56]` hands to `[57]`--`[62]`; at the manuscript's values it reads
`4·def⁺(R) < |R|` up to the exact `T(n)` allowance, i.e. `τ(θ) < 1/4`. -/
def DenseDeficiencyBelowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.dischargeScale *
      (data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) +
        data.spineScale * Core.ceilSqrt object.vertexCount) <
    data.dischargeScale *
        (2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card) +
      (object.vertexCount - data.windowOrder * (canonicalWindowPacking data object).card)

/-- **Node `[146]`, `θ < 1/78`, in the exact form the route-8 carrier collision
consumes.**  `def:cold-window-ledger`'s `τ(θ) < 3/13` is the private-carrier
rate of `rem:route8-carrier-margin` read on the near-cubic spine with its
`o(|R|)` allowances made explicit: with `stubs = δ·order − 2(order−1)` external
stubs per packed window, `|∂R| ≤ stubs·p + σ_W ≤ stubs·p + T(n)`, `|R| = n −
order·p`, and the Type B bridge mass `F·s·T(n)` of `prop:typeB-bridge-sublinear`
on the ambient side,
`(δ·s + 1)·(stubs·p + T(n)) + δ·F·s·T(n) < δ·(n − order·p)`;
at the manuscript's `δ = 3`, `s = 4`, `order = 13` this is `13·(15p + o(n)) <
3·|R| − o(n)`, i.e. `θ < 1/78` up to the `o(1)`. -/
def ColdRoute8BelowStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  (data.threshold * data.dischargeScale + 1) *
      (coldExternalStubCount data * (canonicalWindowPacking data object).card +
        data.surplusThreshold object.vertexCount) +
    data.threshold * (data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount) <
  data.threshold *
    (object.vertexCount - data.windowOrder * (canonicalWindowPacking data object).card)

def ColdRoute8AtOrAboveStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ ColdRoute8BelowStatement data object

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

/-- `X_cold`: the union of the ambient-cubic cold windows of the fixed
packing, "with their internal path edges retained". -/
noncomputable def coldAmbientCubicSupport (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex := by
  classical
  exact ((canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)).biUnion id

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

/-- The exact `o(1)` slack the cold branch hands to `prop:p13-density` at node
`[24]`: on the bounded arm `C ≤ (1 + B_cold)·σ(G)`, so the window-only cap
carries `2·(1 + B_cold)·rate·scaleCount·T(n)`. -/
noncomputable def Data.densitySlack (data : Data.{u}) : Nat :=
  2 * (1 + Graph.ColdCorridor.overlapBound data.threshold data.coldSignature)

/-- Node `[153]`, the exact finite dichotomy behind `lem:cold-germ-extraction`'s
"positive for all sufficiently large `n`": the selected branch-excess mass of the
cold family exceeds the two `o(n)` slacks (the non-ambient-cubic loss and the
candidate loss, each at most `perWindow · σ(G)`). -/
noncomputable def ColdMassLinearStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let perWindow := Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data)
  exact (perWindow + Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
      object.degreeSurplus data.threshold < perWindow * cold.card

/-- The complementary arm of node `[153]`: the cold mass is within the two
slacks, `C ≤ 2σ(G)` after cancelling the positive per-window excess. -/
noncomputable def ColdMassBoundedStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let perWindow := Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data)
  exact perWindow * cold.card ≤
    (perWindow + Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
      object.degreeSurplus data.threshold

/-- Graph realization of the paper's second representative `E` on the same
two labelled cut vertices as the corridor piece, with internally disjoint
ambient realization.  This is vocabulary inside the semantic ledger value;
it introduces no proof-data channel. -/
def SecondStrandGraphRealizedStatement (data : Data.{u})
    {object : Graph.FiniteObject.{u}}
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) : Prop :=
  germ.atom.interface.vertexCount = 2 ∧
    ∃ embedding :
        (germ.atom.interface.Vertex ⊕ germ.canonical.Internal) ↪ object.Vertex,
      (∀ boundary : germ.atom.interface.Vertex,
        embedding (.inl boundary) =
          germ.atom.pieceIntoAmbient (.inl boundary)) ∧
      germ.canonical.graph.map embedding ≤ object.graph ∧
      ∀ internal : germ.canonical.Internal,
        embedding (.inr internal) ∉ germ.support

/-- The literal retained datum of `def:cold-corridor-first-failure`.

For every selected branch-excess half-edge that actually enters the outside
graph, the proposition retains the paper's corridor presentation and its F5
configuration.  In particular the configuration's table record is tied field
by field to the retained presentation.  The repeated arm retains the first
equal-state interval and the canonical cut-state representative; the terminal
arm retains the graph-realized second completion strand.  No default record,
fixed prefix, or self-representative is admitted by this statement. -/
noncomputable def ColdCorridorStateStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ∃ incidence : Eligible →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
    ∀ epsilon : Eligible,
      let germ := incidence epsilon
      ∃ (component : Finset object.Vertex)
        (corridor : Graph.ColdCorridor.Corridor object windows component)
        (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
        (index : corridor.Segment → presentation.Segment),
        Graph.ColdCorridor.IsOutsideComponent object windows component ∧
          corridor.entryStub = (epsilon.1.2, epsilon.1.1) ∧
          Function.Injective index ∧
          (∀ left right : corridor.Segment,
            presentation.state (index left) = presentation.state (index right) →
              ∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
                presentation.support coordinate ⊆
                    ↑(presentation.activeInterface (index left)) →
                  presentation.reading (index left) coordinate =
                    presentation.reading (index right) coordinate) ∧
          (∀ segments : Fin (Graph.ColdCorridor.stateBound data.coldSignature + 1) →
              corridor.Segment,
            ∃ left right, left ≠ right ∧
              presentation.state (index (segments left)) =
                presentation.state (index (segments right))) ∧
          (∀ (boundary : Graph.Boundary)
              (carrier : presentation.Segment → Graph.BoundaryPiece boundary)
              (left right : corridor.Segment),
            (¬ presentation.FirstFailureResponse
                (Graph.HasCycleWithLength data.LengthOK) carrier
                  (index left) (index right) →
              presentation.state (index left) = presentation.state (index right) →
                Graph.Response.ContextEquivalent
                  (Graph.HasCycleWithLength data.LengthOK)
                  (carrier (index left)) (carrier (index right))) ∧
            (presentation.state (index left) = presentation.state (index right) →
              ¬ Graph.Response.ContextEquivalent
                  (Graph.HasCycleWithLength data.LengthOK)
                  (carrier (index left)) (carrier (index right)) →
                presentation.FirstFailureResponse
                  (Graph.HasCycleWithLength data.LengthOK) carrier
                    (index left) (index right))) ∧
          germ.atom.interface.vertexCount = 2 ∧
          germ.support.card ≤
            Graph.ColdCorridor.exchangeBound data.coldSignature ∧
          (∀ vertex ∈ germ.support,
            vertex ∈ (corridor.inside.1.support.map
              (fun inner => inner.1)).toFinset) ∧
          ((Graph.ColdCorridor.Corridor.TerminalCorridor corridor
                data.coldSignature ∧
              germ.support = corridor.prefixSupport corridor.statesRead ∧
              SecondStrandGraphRealizedStatement data germ ∧
              let terminal : corridor.Segment :=
                ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
              germ.record.boundaryDegrees =
                  presentation.boundaryDegrees (index terminal) ∧
                germ.record.stubs = presentation.halfEdges (index terminal) ∧
                germ.record.offsets = presentation.offsets (index terminal) ∧
                germ.record.state = presentation.state (index terminal) ∧
                germ.record.truth = false) ∨
            ∃ left right : corridor.Segment,
              left.1 < right.1 ∧
              presentation.state (index left) = presentation.state (index right) ∧
              (∀ earlierLeft earlierRight : corridor.Segment,
                earlierLeft.1 < earlierRight.1 →
                  earlierRight.1 < right.1 →
                    presentation.state (index earlierLeft) ≠
                      presentation.state (index earlierRight)) ∧
              germ.support =
                ((((corridor.inside.1.drop left.1).take
                    (right.1 - left.1)).support.map
                      (fun inner => inner.1)).toFinset) ∧
              germ.canonical =
                (Graph.CanonicalPiece.cutStateRepresentative
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  germ.piece).toPiece ∧
              germ.record.boundaryDegrees =
                presentation.boundaryDegrees (index left) ∧
              germ.record.stubs = presentation.halfEdges (index left) ∧
              germ.record.offsets = presentation.offsets (index left) ∧
              germ.record.state = presentation.state (index left) ∧
              germ.record.truth = false)

/-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii): every selected
branch-excess half-edge of the ambient-cubic cold windows has a first-failure
exchange germ whose support meets a vertex of degree above the threshold (by
node `[10]` a heavy centre with all neighbours at the threshold), so no
candidate germ is subcubic: the half-edge is decorated handoff fan data. -/
noncomputable def AbsorbedGermFanDataStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ∃ state : ColdCorridorStateStatement data object,
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    ∀ epsilon : Eligible,
      ∃ vertex ∈ (incidence epsilon).support,
        data.threshold < object.degree vertex

/-- Node `[175]`, `lem:absorbed-germ-fan-data`, the per-half-edge dichotomy on
the absorbed-configuration residual.  For every selected branch-excess
half-edge `ε` of an ambient-cubic cold window, with first-failure support `J`
(the support of its first-failure exchange germ), exactly one of:
(i) `J` contains no vertex of degree above the threshold — then `J` is
subcubic and `ε`'s germ is one of the candidates of `lem:cold-germ-extraction`,
so it is charged in full and routed (F1)--(F5) as in
`lem:cold-corridor-first-failure` (node `[176]`); or
(ii) `J` contains a vertex `z` of degree above the threshold — then, since the
vertices above the threshold are independent (node `[10]`), every neighbour of
`z` has degree exactly the threshold: `z` is a heavy centre (node `[177]`).
The two cases are exclusive by the degree comparison at `z`. -/
noncomputable def AbsorbedGermSplitStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ∃ state : ColdCorridorStateStatement data object,
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    let candidates :=
      ((Finset.univ : Finset Eligible).filter fun epsilon =>
        ∀ vertex ∈ (incidence epsilon).support,
          object.degree vertex ≤ data.threshold).image incidence
    ∀ epsilon : Eligible,
      let germ := incidence epsilon
      ((∀ vertex ∈ germ.support,
          object.degree vertex ≤ data.threshold) ∧ germ ∈ candidates) ∨
        ∃ centre ∈ germ.support, data.threshold < object.degree centre ∧
          ∀ neighbour : object.Vertex, object.graph.Adj centre neighbour →
            object.degree neighbour = data.threshold

/-- The exact family witness produced by `lem:cold-germ-extraction`: an actual
candidate family of the current object, its positive disjoint subfamily, and
the manuscript's charged-count inequality.  This is a proposition used inside
semantic ledger values, not a transport carrier. -/
noncomputable def ColdGermFamilyWitness (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (candidates disjointFamily : Finset
      (Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ∃ state : ColdCorridorStateStatement data object,
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    let routedCandidates :=
      ((Finset.univ : Finset Eligible).filter fun epsilon =>
        ∀ vertex ∈ (incidence epsilon).support,
          object.degree vertex ≤ data.threshold).image incidence
    candidates = routedCandidates ∧
      Graph.ColdCorridor.CandidateGermFamily data.coldSignature data.threshold
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object candidates ∧
        Graph.ColdCorridor.ExtractedGermFamily data.coldSignature data.threshold
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object candidates disjointFamily ∧
        let perWindow := Graph.ColdCorridor.branchExcessOf
          (coldExternalStubCount data)
        perWindow * cubic.card ≤
          data.threshold * (Graph.ColdCorridor.stateBound data.coldSignature + 1) *
              candidates.card +
            Graph.ColdCorridor.overlapBound data.threshold data.coldSignature *
              object.degreeSurplus data.threshold

/-- `lem:cold-germ-extraction` on the current residual.  The selected
half-edge count pays for an actual candidate family; the framework-local
greedy extraction then returns a positive disjoint family. -/
noncomputable def ColdGermCandidatesStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ candidates disjointFamily,
    ColdGermFamilyWitness data object candidates disjointFamily

/-- One germ of the literal positive disjoint family retained by the incoming
`K .coldGermCandidates` fact.  Downstream cold nodes use this predicate so a
neutral or symmetric germ cannot be fabricated outside the extracted family. -/
noncomputable def ActiveColdGermStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) : Prop :=
  ∃ candidates disjointFamily,
    ColdGermFamilyWitness data object candidates disjointFamily ∧
      germ ∈ disjointFamily

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
noncomputable def ColdFailureRoutingStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ColdAmbientCubicStubExcessStatement data object ∧
    ∃ state : ColdCorridorStateStatement data object,
      let incidence : Eligible →
          Graph.ColdCorridor.BoundedGerm data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object :=
        Classical.choose state
      let candidates :=
        ((Finset.univ : Finset Eligible).filter fun epsilon =>
          ∀ vertex ∈ (incidence epsilon).support,
            object.degree vertex ≤ data.threshold).image incidence
      (∀ germ ∈ candidates,
        (candidates.filter fun other =>
          ¬ Disjoint germ.support other.support).card ≤
            Graph.ColdCorridor.extractionDenominator data.threshold
              data.coldSignature - 1) ∧
      let perWindow := Graph.ColdCorridor.branchExcessOf
        (coldExternalStubCount data)
      perWindow * cubic.card ≤
        data.threshold * (Graph.ColdCorridor.stateBound data.coldSignature + 1) *
            candidates.card +
          Graph.ColdCorridor.overlapBound data.threshold data.coldSignature *
            object.degreeSurplus data.threshold

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
conclusion `d_G(z) ≥ 4` at a surviving first separator.  It is recorded through
the registered threshold as `data.threshold < d_G(z)`; the cubic-baseline
identity makes this exactly the manuscript's inequality, rather than a second
hard-coded degree convention.

*The absorbing predicate* is `def:typeB-fan-safe` clause (ii), the label
collision of `lem:labels`: exit `(3)`, which the branch reaching node `[107]`
has already denied and which the row therefore reads rather than restates.

*The two admissibility predicates* are node `[14]`'s hereditary
target-uncompressibility and the `P₁₃`-freeness of the counted core. -/

/-- The registered high-degree set at a surviving first separator:
`lem:typeA-cubic-switch-absorption`. -/
abbrev handoffHighDegree (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    object.Vertex → Prop :=
  fun vertex => data.threshold < object.degree vertex

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

/-- The counted core satisfies the paper's single compound core-safety clause:
it is `P₁₃`-free and has no internal sub-support of minimum degree at least the
registered baseline.  Keeping the conjunction in the existing predicate avoids
introducing a second certificate carrier for `lem:decorated-fan-admissibility`. -/
abbrev handoffWindowFree (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    Finset object.Vertex → Prop :=
  fun support =>
    (∀ window : Finset object.Vertex, window ⊆ support →
      ¬ object.InducesWindow data.windowOrder window) ∧
    ∀ internal : Finset object.Vertex, internal ⊆ support →
      ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce internal)

/-- The exact case-(ii) witness of `lem:absorbed-germ-fan-data` for one selected
branch-excess half-edge: a high centre on its first-failure support, its cubic
neighbourhood, and the two distinct corridor incidences and simple tails at
that centre.  The tails land in the selected packed-window union, exactly as
the corridor construction proves.  In particular this proposition does **not**
misdeclare that union to be the `P₁₃`-free remainder core of a
`DecoratedHandoff.Envelope`; the manuscript supplies fan data here, not a Type A
exit-`(7)` core.  The indices remain part of the proposition so later Type B
decisions classify the same literal corridor datum. -/
noncomputable def AbsorbedGermFanEnvelopeWitness (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (centre : object.Vertex) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact (∃ state : ColdCorridorStateStatement data object,
      ∃ epsilon : Eligible, germ = Classical.choose state epsilon) ∧
    centre ∈ germ.support ∧
    data.threshold < object.degree centre ∧
      (∀ neighbour : object.Vertex, object.graph.Adj centre neighbour →
        object.degree neighbour = data.threshold) ∧
      ∃ first second : object.Vertex,
        first ≠ second ∧
          object.graph.Adj centre first ∧
          object.graph.Adj centre second ∧
          ∃ left right : List object.Vertex,
            left.head? = some first ∧
            right.head? = some second ∧
            left.IsChain object.graph.Adj ∧
            right.IsChain object.graph.Adj ∧
            left.Nodup ∧
            right.Nodup ∧
            (∃ terminal, left.getLast? = some terminal ∧
              terminal ∈ Graph.ColdCorridor.windowsOf object cubic) ∧
            (∃ terminal, right.getLast? = some terminal ∧
              terminal ∈ Graph.ColdCorridor.windowsOf object cubic) ∧
            (∀ vertex ∈ left,
              vertex ∈ Graph.ColdCorridor.windowsOf object cubic ∨
                  vertex = centre →
                left.getLast? = some vertex) ∧
            (∀ vertex ∈ right,
              vertex ∈ Graph.ColdCorridor.windowsOf object cubic ∨
                  vertex = centre →
                right.getLast? = some vertex) ∧
            Graph.DecoratedHandoff.FanSafe object data.LengthOK
              (handoffAbsorbing data object
                (canonicalWindowPacking data object)) centre first second ∧
            Graph.DecoratedHandoff.FanSafe object data.LengthOK
              (handoffAbsorbing data object
                (canonicalWindowPacking data object)) centre second first

/-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii), the decorated handoff fan
data at the heavy centre.  For every selected branch-excess half-edge `ε` of an
ambient-cubic cold window, choose the heavy vertex `z` supplied by case (ii) of
the first-failure split.  Every neighbour of `z` is cubic, and the two distinct
corridor incidences at `z`, together with the corridor tails on their two sides,
form the geometric decorated handoff fan data used by the Type B calculation.
This is the indexed case-(ii) datum; it does not invent a Type A core, a
canonical negative remainder support, or a zero-surplus hypothesis. -/
noncomputable def AbsorbedGermFanEnvelopeStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}
  exact ∃ state : ColdCorridorStateStatement data object,
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    ∀ epsilon : Eligible,
      ∃ centre, AbsorbedGermFanEnvelopeWitness data object
        (incidence epsilon) centre

/-- **The ordinary Type B support of node `[64]`** (`def:admissible` with
`σ(X) > 0`): a connected piece of the remainder of a maximal packing carrying
negative net charge and positive assigned surplus, together with a clause `P`
about the packing and the piece.  A support is data and cannot travel, so each
`[64]`-entry fact is stated at every such support the object carries. -/
def TypeBSupportWith (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (P : Finset (Finset object.Vertex) → Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces (object.remainderSupport packing),
        let piece := object.pieceSupport (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          0 < object.ambientSurplus piece data.threshold ∧
          P packing piece

/-- **`def:typeB-assigned-ledger`: the assigned centres `H_X` of a connected
Type B support `X = (Y_X, H_X)`.**  `Y_X` is the counted remainder core (a
canonical piece of the remainder) and `H_X` the high-degree fan centres whose
surplus units are assigned to `X`.  There are exactly two ways the manuscript
produces one, and both enter the same nodes `[67]`--`[85]` (Part VI's ordinary
entry `[64]`/`[65]` and its dashed handoff input `[66]`):

* the ordinary Type B support of node `[64]` (`def:admissible` with `σ(X) > 0`):
  `H_X` is the piece's own set of high centres (`def:canonical-decomp`);
* the decorated handoff fan envelope of `def:decorated-fan-envelope` reached
  from exit `(7)` at `[108]`: `Y_X` is the Type A support (`σ(Y_X) = 0`) and
  `H_X` its decorations, each with a nonempty assigned first-neighbour set of
  actual neighbours (`lem:decorated-fan-admissibility`). -/
def TypeBAssignedCentres (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece centres : Finset object.Vertex) : Prop :=
  (object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      0 < object.ambientSurplus piece data.threshold ∧
      centres = Graph.TypeBRefinedSupport.centres object data.threshold piece) ∨
  (object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      object.ambientSurplus piece data.threshold = 0 ∧
      ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
          (handoffHighDegree data object) (handoffAbsorbing data object packing),
        envelope.core = piece ∧ envelope.decorations = centres ∧
          centres.Nonempty ∧
          ∀ centre ∈ centres,
            (envelope.assigned centre).Nonempty ∧
              ∀ first ∈ envelope.assigned centre, object.graph.Adj centre first)

/-- **A Type B fan support with its assigned centres**, the common notion nodes
`[71]`--`[75]` are stated on: a canonical piece `Y_X` of the remainder of a
maximal packing together with assigned centres `H_X` in either of the two
manuscript forms, and a clause `P` about the packing, the core and the centres.
A support is data and cannot travel, so each fact is stated at every such
support the object carries. -/
def TypeBFanSupportWith (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (P : Finset (Finset object.Vertex) → Finset object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces (object.remainderSupport packing),
        let piece := object.pieceSupport (object.remainderSupport packing) component
        ∃ centres : Finset object.Vertex,
          TypeBAssignedCentres data object packing piece centres ∧
            P packing piece centres

/-- **Node `[65]`, the common Type B entry.**  The manuscript has two literal
input forms at this node.  The ordinary `[64]` lane and the Type A exit-`(7)`
lane already carry a canonical assigned support.  Node `[177]` instead carries
the indexed decorated handoff fan data of every selected cold half-edge; its
lemma does not manufacture a maximal packing or a canonical negative remainder
piece.  Keeping the alternatives in the semantic value of the one common key
makes `[177] → [65]` a direct ledger edge rather than a conversion interface. -/
def TypeBFanEntryStatement (data : Data.{u}) (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    centres.Nonempty ∧
      ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) ∨
  AbsorbedGermFanEnvelopeStatement data object

/-- Node `[68]`, yes arm, for the indexed `[177]` input.  The complete family
of decorated handoff witnesses is retained, and one of its actual centres is
heavy.  This is the paper's test `d_G(h) > 4`, written relative to the registered
baseline rather than with an EG-specific numeral. -/
noncomputable def AbsorbedGermFanHeavyCentreStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        data.threshold + 1 < object.degree centre

/-- Node `[68]`, no arm, for the indexed `[177]` input.  For every selected
half-edge the preserved decorated handoff witness can be chosen with its centre
at the unique high-but-not-heavy degree, namely `threshold + 1`. -/
noncomputable def AbsorbedGermFanDegreeFourCentresStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        object.degree centre = data.threshold + 1

/-- Node `[68]`, yes arm, on either of the two paper-prescribed Type B inputs. -/
def TypeBFanHeavyCentreStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    ∃ centre ∈ centres, data.threshold + 1 < object.degree centre) ∨
  AbsorbedGermFanHeavyCentreStatement data object

/-- Node `[68]`, no arm, on either of the two paper-prescribed Type B inputs. -/
def TypeBFanDegreeFourCentresStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    ∀ centre ∈ centres, object.degree centre = data.threshold + 1) ∨
  AbsorbedGermFanDegreeFourCentresStatement data object

/-- Node `[69]` on the indexed `[177]` lane.  The original absorbed-germ
witness and its indices remain the carrier; at the heavy centre selected by
`[68]`, `cor:heavy-center-local-dichotomy` supplies exactly the same local
alternative as on an ordinary Type B support. -/
noncomputable def AbsorbedGermFanLocalDichotomyStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        data.threshold + 1 < object.degree centre ∧
        ((∃ left right : object.Vertex,
            Graph.FanCompatible object centre left right) ∨
          (object.degree centre - 2 ≤
              (Graph.triangularEndpoints object centre).card ∧
            3 ≤ (Graph.triangularEndpoints object centre).card))

/-- Node `[79]` on the indexed `[177]` lane.  For every selected cold
half-edge, the degree-`threshold + 1` decorated centre chosen by `[68]` carries
`cor:degree-four-local-activation` and the exact registered-scale fan profile.
No canonical remainder piece is inserted into this statement. -/
noncomputable def AbsorbedGermFanDegreeFourProfileStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
          object.degree centre = data.threshold + 1 ∧
          ((∃ left right : object.Vertex,
              Graph.FanCompatible object centre left right) ∨
            data.threshold - 1 ≤
              (Graph.triangularEndpoints object centre).card) ∧
          object.degree centre - data.threshold = 1 ∧
          ∀ fanEnvelope : Finset object.Vertex,
            Graph.TypeBFanIncidence.closedCount object data.threshold
                fanEnvelope centre ≤ data.threshold + 1 ∧
              Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                  data.dischargeScale fanEnvelope centre =
                (data.dischargeScale : Int) *
                    (Graph.TypeBFanIncidence.closedCount object data.threshold
                      fanEnvelope centre : Int) -
                  (data.dischargeScale : Int) * (data.threshold : Int) +
                  ((data.threshold : Int) + 2)

/-- Node `[69]` on either paper-prescribed Type B carrier. -/
def TypeBFanLocalDichotomyStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
        (∃ left right : object.Vertex,
          Graph.FanCompatible object centre left right) ∨
        (object.degree centre - 2 ≤
            (Graph.triangularEndpoints object centre).card ∧
          3 ≤ (Graph.triangularEndpoints object centre).card)) ∨
    AbsorbedGermFanLocalDichotomyStatement data object

/-- Node `[79]` on either paper-prescribed Type B carrier. -/
noncomputable def TypeBFanDegreeFourProfileStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        object.degree centre = data.threshold + 1 ∧
        ((∃ left right : object.Vertex,
            Graph.FanCompatible object centre left right) ∨
          data.threshold - 1 ≤ (Graph.triangularEndpoints object centre).card) ∧
        object.degree centre - data.threshold = 1 ∧
        ∀ fanEnvelope : Finset object.Vertex,
          Graph.TypeBFanIncidence.closedCount object data.threshold
              fanEnvelope centre ≤ data.threshold + 1 ∧
            Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                data.dischargeScale fanEnvelope centre =
              (data.dischargeScale : Int) *
                  (Graph.TypeBFanIncidence.closedCount object data.threshold
                    fanEnvelope centre : Int) -
                (data.dischargeScale : Int) * (data.threshold : Int) +
                ((data.threshold : Int) + 2)) ∨
    AbsorbedGermFanDegreeFourProfileStatement data object

/-- Node `[70]` on the indexed `[177]` lane.  The fan-certificate cap is
pointwise and therefore applies directly to every actual decorated centre;
the corridor/envelope indices are retained and no canonical support is
manufactured. -/
noncomputable def AbsorbedGermFanCertificateCapStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∀ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤ Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Node `[70]` on either paper-prescribed Type B carrier. -/
noncomputable def TypeBFanCertificateCapStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        ∀ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder) ∨
    AbsorbedGermFanCertificateCapStatement data object

/-- Node `[71]`/`[80]`, yes arm, on the indexed `[177]` lane.  The complete
absorbed family is retained, and every actual centre witnessing one of its
selected corridor entries carries the paper's fan-certificate labelling and
the cap already proved at `[70]`. -/
noncomputable def AbsorbedGermFanCertificateMarkedStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∃ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤ Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Node `[71]`/`[80]`, no arm, on the indexed `[177]` lane.  The full
absorbed family remains available and one of its literal corridor-indexed
centres has no fan-certificate labelling. -/
noncomputable def AbsorbedGermFanCertificateResidualStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre)

/-- Nodes `[71]`/`[80]`, yes arm, on either paper-prescribed Type B input. -/
noncomputable def TypeBFanCertificateMarkedStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        ∃ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder) ∨
    AbsorbedGermFanCertificateMarkedStatement data object

/-- Nodes `[71]`/`[80]`, no arm, on either paper-prescribed Type B input. -/
noncomputable def TypeBFanCertificateResidualStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre)) ∨
    AbsorbedGermFanCertificateResidualStatement data object

/-- Node `[74]`/`[82]` on the indexed `[177]` lane.  The marked absorbed
family is retained while the hybrid B1 calculation is recorded at each actual
centre selected by its corridor witness. -/
noncomputable def AbsorbedGermFanHybridEntryStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∀ envelope windowSupport : Finset object.Vertex,
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
          Graph.TypeBHybridIncidence.windowIncidences object data.threshold
                envelope windowSupport centre +
              Graph.TypeBHybridIncidence.nonWindowIncidences object
                data.threshold envelope windowSupport centre =
            (data.threshold - 1) *
              Graph.TypeBFanIncidence.closedCount object data.threshold envelope centre ∧
          2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                  data.dischargeScale envelope centre ≤
              (data.dischargeScale : Int) *
                ((Graph.TypeBHybridIncidence.windowIncidences object
                    data.threshold envelope windowSupport centre : Int) +
                  (Graph.TypeBHybridIncidence.nonWindowIncidences object
                    data.threshold envelope windowSupport centre : Int)) ∧
          Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
                data.dischargeScale envelope windowSupport centre ≤
              (data.dischargeScale : Int) *
                (Graph.TypeBHybridIncidence.nonWindowIncidences object
                  data.threshold envelope windowSupport centre : Int) ∧
          (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
              envelope centre →
            0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
              data.dischargeScale envelope centre)

/-- Node `[74]`/`[82]` on either paper-prescribed Type B carrier. -/
noncomputable def TypeBFanHybridEntryStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre →
          ∀ envelope windowSupport : Finset object.Vertex,
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
            Graph.TypeBHybridIncidence.windowIncidences object data.threshold
                  envelope windowSupport centre +
                Graph.TypeBHybridIncidence.nonWindowIncidences object
                  data.threshold envelope windowSupport centre =
              (data.threshold - 1) *
                Graph.TypeBFanIncidence.closedCount object data.threshold
                  envelope centre ∧
            2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                    data.dischargeScale envelope centre ≤
                (data.dischargeScale : Int) *
                  ((Graph.TypeBHybridIncidence.windowIncidences object
                      data.threshold envelope windowSupport centre : Int) +
                    (Graph.TypeBHybridIncidence.nonWindowIncidences object
                      data.threshold envelope windowSupport centre : Int)) ∧
            Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
                  data.dischargeScale envelope windowSupport centre ≤
                (data.dischargeScale : Int) *
                  (Graph.TypeBHybridIncidence.nonWindowIncidences object
                    data.threshold envelope windowSupport centre : Int) ∧
            (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
                envelope centre →
              0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                data.dischargeScale envelope centre)) ∨
    AbsorbedGermFanHybridEntryStatement data object

/-- Node `[72]`/`[81]`, direct-cycle arm, on the indexed `[177]` lane. -/
noncomputable def AbsorbedGermFanDirectCycleStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Graph.TypeBDirectCycle.DirectCycleConfiguration object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) centre

/-- Node `[72]`/`[81]`, direct-cycle-free arm, on the indexed `[177]` lane. -/
noncomputable def AbsorbedGermFanDirectCycleFreeStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder data.LengthOK
          (canonicalWindowPacking data object) centre

/-- Node `[72]`/`[81]`, direct-cycle arm, on either Type B carrier. -/
noncomputable def TypeBFanDirectCycleStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          Graph.TypeBDirectCycle.DirectCycleConfiguration object
            data.windowOrder data.LengthOK packing centre) ∨
    AbsorbedGermFanDirectCycleStatement data object

/-- Node `[72]`/`[81]`, direct-cycle-free arm, on either Type B carrier. -/
noncomputable def TypeBFanDirectCycleFreeStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun packing _piece centres =>
      ∀ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre →
          Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
            data.LengthOK packing centre) ∨
    AbsorbedGermFanDirectCycleFreeStatement data object

/-- Node `[72]`/`[81]`, B2 yes arm, on the literal indexed `[177]` fan datum.
For every retained cold-corridor witness, its actual heavy centre admits the
paper's candidate entry on that same first-failure support.  The singleton is
the one centre whose discarded half-edge is being charged; no decorated Type A
core is manufactured. -/
noncomputable def AbsorbedGermFanB2ChoiceStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
          data.dischargeScale packing germ.support {centre} {centre}

/-- Node `[72]`/`[81]`, B2 no arm, on the literal indexed `[177]` fan datum.
The published failure is the paper's genuine minimal overlap obstruction on
the same first-failure support and its actual heavy centre. -/
noncomputable def AbsorbedGermFanB2ObstructionStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale packing germ.support {centre})

/-- Nodes `[74]`/`[82]` on the indexed `[177]` lane.  This is the literal
successful B2(a)--(c) datum on the first-failure support: it retains the
chosen `DisjointChoice`, hence all of its candidate and pairwise-disjoint
carrier fields, and records the candidate's nonnegative augmented payment.
It deliberately does not manufacture a canonical remainder piece or assert
the post-ledger Type A component conclusions that require one. -/
noncomputable def AbsorbedGermFanB2PaidStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanB2ChoiceStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∃ choice : Graph.TypeBRefinedSupport.DisjointChoice object
            data.threshold data.dischargeScale packing germ.support {centre} {centre},
          ∀ member : centre ∈ ({centre} : Finset object.Vertex),
            (choice.entry centre member).EntryRefines data.threshold
              data.dischargeScale germ.support centre

/-- Node `[84]` on the indexed `[177]` B2-failure lane.  The mass estimate is
attached to the same corridor indices, actual heavy centre, first-failure
support, and minimal overlap obstruction; no canonical support is substituted. -/
noncomputable def AbsorbedGermFanB2ObstructionMassStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale packing germ.support {centre}) ∧
        ∀ envelope : Finset object.Vertex,
          Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
              data.dischargeScale envelope centre ≤
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold)

/-- Node `[75]`/`[84]` on the indexed `[177]` certificate-residual lane. -/
noncomputable def AbsorbedGermFanCertificateResidualMassStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanEnvelopeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) ∧
        ∀ envelope : Finset object.Vertex,
          Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
              data.dischargeScale envelope centre ≤
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold)

/-- Node `[75]`/`[84]`, certificate-residual mass, on either Type B carrier. -/
noncomputable def TypeBFanCertificateResidualMassStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) ∧
          ∀ envelope : Finset object.Vertex,
            Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
                data.dischargeScale envelope centre ≤
              data.bridgeMassFactor * data.dischargeScale *
                (object.degree centre - data.threshold)) ∨
    AbsorbedGermFanCertificateResidualMassStatement data object

/-- The assigned centres of either manuscript form are high centres, and they
include every high centre of the counted core (`def:typeB-assigned-ledger`):
for the ordinary support they are exactly the core's high centres; for a
decorated handoff envelope the core has `σ = 0`, hence no high centre, and the
decorations are high by `def:decorated-fan-envelope`. -/
theorem TypeBAssignedCentres.high (data : Data.{u}) (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  intro centre member
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, _, envelope, _, rfl, _, _⟩
  · exact (Graph.TypeBRefinedSupport.mem_centres.mp member).2
  · exact envelope.decorations_high centre member

theorem TypeBAssignedCentres.centres_subset (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    Graph.TypeBRefinedSupport.centres object data.threshold piece ⊆ centres := by
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, zero, _⟩
  · exact Finset.Subset.refl _
  · intro centre member
    exfalso
    obtain ⟨inPiece, high⟩ := Graph.TypeBRefinedSupport.mem_centres.mp member
    have : object.degree centre - data.threshold = 0 := by
      unfold Graph.FiniteObject.ambientSurplus at zero
      exact Finset.sum_eq_zero_iff.mp zero centre inPiece
    exact absurd high (by
      show ¬ data.threshold < object.degree centre
      omega)

/-- **The assigned Type B support as the B2 ledger reads it**: a canonical piece
of the remainder of a maximal packing (`CanonicalPiece`, whose vertex set is
the counted core `Y_X`) with assigned centres `H_X` in either manuscript form,
and a clause `P` about the packing, the piece and the centres. -/
def TypeBAssignedLedgerWith (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (P : (packing : Finset (Finset object.Vertex)) →
      Graph.TypeBRefinedSupport.CanonicalPiece object packing →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ canonicalPiece : Graph.TypeBRefinedSupport.CanonicalPiece object packing,
        ∃ centres : Finset object.Vertex,
          TypeBAssignedCentres data object packing canonicalPiece.vertices centres ∧
            P packing canonicalPiece centres

/-- Node `[72]`/`[81]`, B2 yes arm, on either paper-prescribed Type B input. -/
noncomputable def TypeBB2ChoiceStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
    Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale packing canonicalPiece.vertices centres centres) ∨
  AbsorbedGermFanB2ChoiceStatement data object

/-- Node `[72]`/`[81]`, B2 no arm, on either paper-prescribed Type B input. -/
noncomputable def TypeBB2ObstructionStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
      data.threshold data.dischargeScale packing canonicalPiece.vertices
      centres)) ∨
  AbsorbedGermFanB2ObstructionStatement data object

/-- **A decorated handoff fan envelope is produced at a support.**  The test
node `[107]` splits on: `def:decorated-fan-envelope`'s data, with the Type A
support as the counted core and at least one high-degree decoration. -/
def HandoffProduced (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty

/-- **The envelope produced is admissible Type B fan-envelope data**
(`lem:decorated-fan-admissibility`).  This is the handoff interface, and by
`rem:typeA-typeB-stratification` it uses no conclusion of
`lem:typeB-exclusion`. -/
def HandoffAdmissible (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

/-- **The literal Type B handoff conclusion of
`lem:same-token-bottleneck-routing`.**

Node `[144]` produces the decorated fan envelope at the two separated
connector tails.  As on the existing Type-A exit-`(7)` lane, admissibility is
proved by the downstream Type B handoff row; it is not a premise silently
inserted into the producer.  In particular `[144]` does not assert that the
selected port supports already form a connected remainder core.  The paper
does not prove that assertion in the same-token lemma, and its connector tails
only land in `T(p)` and `T(q)` at this stage. -/
def SameTokenTypeBHandoffStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        HandoffProduced data object packing core

/-- `def:decorated-fan-envelope`, the selected-handoff instance of
`def:typeB-assigned-ledger`, and `lem:decorated-fan-admissibility`: the complete
envelope, its high-degree centre set, each centre's nonempty assigned
first-neighbour support, and the admissibility data consumed by the Type B
calculation.  The paper's separate multi-core grouped-envelope support is
formed later from the actual post-ledger component family. -/
def DecoratedTypeBAssignedSupport (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty ∧
      (∀ centre ∈ envelope.decorations,
        Graph.IsHighCentre object data.threshold centre) ∧
      (∀ centre ∈ envelope.decorations,
        (envelope.assigned centre).Nonempty ∧
          ∀ first ∈ envelope.assigned centre,
            object.graph.Adj centre first) ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

/-- Exit `(6)` at the selected Type A support and receiver: some eligible
silent routed load of the receiver has a selected trace basin at which an
equality of declared coordinates of `ρ_u(B_u)` becomes target-complete only
after adjoining a larger connected support (`def:typeA-trace-basin` (c),
identified with exit `(6)` by `lem:typeA-reduced-silent-residual`).  The
eligible loads are exactly those tested by exit `(5)` on the same peeling set. -/
def ExitSixDelocalizes (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ∃ load : object.Vertex,
    (((∃ package :
          Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
            data.dischargeScale receiver peeled,
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
            receiver peeled,
          ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver package.outside
              peeled,
            witness.load = selected) ∧
          load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
            data.threshold data.dischargeScale receiver package.outside
            peeled) ∨
      (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
          data.dischargeScale receiver peeled ∧
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
            receiver peeled,
          witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
            data.dischargeScale receiver peeled) ∧
        load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
          data.dischargeScale receiver peeled)) ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold
            receiver load = some basin ∧
          Graph.Route8.TraceBasin.TraceDelocalization object piece
            data.threshold data.LengthOK receiver load basin)

/-- The exact selected saturated Type A state after exits `(4)`, `(5)`, and
`(6)` have failed, with one additional local clause on its selected packing and
support.  This is a fact-schema abbreviation only: rows still read it from the
incoming `ExactLedger` and commit descendants through `Decision.run` or
`factOnly`. -/
abbrev SelectedNoExitSixWith (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      Finset object.Vertex → Prop) : Prop :=
  let exitFiveAt := fun (piece : Finset object.Vertex)
      (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
    ∃ load : object.Vertex,
      (((∃ package :
            Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver peeled,
          (¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver peeled,
            ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                data.threshold data.dischargeScale receiver package.outside
                peeled,
              witness.load = selected) ∧
            load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver package.outside
              peeled) ∨
        (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
            data.dischargeScale receiver peeled ∧
          (¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
              data.dischargeScale receiver peeled) ∧
          load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
            data.dischargeScale receiver peeled)) ∧
        ∃ basin : Finset object.Vertex,
          Graph.Route8.TraceBasin.select? object piece data.threshold
              receiver load = some basin ∧
            Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
              piece data.threshold data.LengthOK receiver load basin)
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
                        data.threshold data.dischargeScale receiver peeled,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside peeled,
                        witness.load = load) ∨
                    (Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ¬ ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold data.dischargeScale receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                          data.threshold data.dischargeScale receiver peeled)) ∧
                  ¬ exitFiveAt piece receiver peeled ∧
                  ¬ ExitSixDelocalizes data object piece receiver peeled ∧
                  extra packing piece)

/-- The same selected no-exit-`(6)` residual, but with the selected receiver
and current peeling set exposed to the next local route-`8` fact.  This is a
schema helper only: the framework still carries the full `ExactLedger`, and
rows still read the predecessor facts by key. -/
abbrev SelectedNoExitSixReceiverWith (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      (piece : Finset object.Vertex) → object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  let exitFiveAt := fun (piece : Finset object.Vertex)
      (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
    ∃ load : object.Vertex,
      (((∃ package :
            Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver peeled,
          (¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver peeled,
            ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                data.threshold data.dischargeScale receiver package.outside
                peeled,
              witness.load = selected) ∧
            load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver package.outside
              peeled) ∨
        (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
            data.dischargeScale receiver peeled ∧
          (¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
              data.dischargeScale receiver peeled) ∧
          load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
            data.dischargeScale receiver peeled)) ∧
        ∃ basin : Finset object.Vertex,
          Graph.Route8.TraceBasin.select? object piece data.threshold
              receiver load = some basin ∧
            Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
              piece data.threshold data.LengthOK receiver load basin)
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
                        data.threshold data.dischargeScale receiver peeled,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside peeled,
                        witness.load = load) ∨
                    (Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ¬ ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold data.dischargeScale receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                          data.threshold data.dischargeScale receiver peeled)) ∧
                  ¬ exitFiveAt piece receiver peeled ∧
                  ¬ ExitSixDelocalizes data object piece receiver peeled ∧
                  extra packing piece receiver peeled)

/-- The selected silent-core residual profile at exit `(8)`.  It exposes the
same selected saturated residual state as `[109]`, with the selected receiver
and current peeling set in scope for later semantic facts, and asserts that no
decorated handoff fan is produced. -/
abbrev SilentCoreResidualProfile (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun packing piece _receiver _peeled =>
      ¬ HandoffProduced data object packing piece)

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

/-- Residual C, node `[55]`: `prop:two-budget`'s "in every case the surviving
residual is subsequently passed to the large-budget net-charge analysis" — the
`[53]`-no arm (the joint package fits the skeleton budget) and the low-entropy
arm; the `[53]`-yes arm is the terminal `[54]` on every residual. -/
abbrev LargeBudgetResidual (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  (jointPackageDemand data object ≤ Graph.skeletonBudget object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
          data.windowOrder data.threshold
          (object.positiveDeficiency (object.remainderSupport packing)
            data.threshold)
          (object.internalEdgeCount (object.remainderSupport packing))
          (object.remainderSupport packing).card)

/-- The exact component predicate used by node `[111]` to form `𝒳_A`.

`SilentFirst` is the absence of the visible-overload lane (exits `(1)`--`(3)`),
and every unpaid silent load is already an indexed target-complete-minimal trace
basin entry, which is the absence of exits `(4)`--`(7)`.  This predicate defines
the route-`8` collection; it contains no numerical burden from `[112]`. -/
abbrev Route8Survives (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport packing)) : Prop :=
  let piece := object.pieceSupport (object.remainderSupport packing) component
  object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
    object.ambientSurplus piece data.threshold = 0 ∧
    Graph.Route8Deficit.SilentFirst object piece data.threshold
      data.dischargeScale ∧
    ∀ receiver : object.Vertex,
      receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale →
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
            data.LengthOK receiver load ∧
          ¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver ∅,
            witness.load = load

open scoped Classical in
/-- **`prop:typeB-bridge-sublinear`'s hypotheses on this branch**, in the
`[113]`-tested form: (i) every negative positive-surplus canonical piece
carries the flat off-centre routing/unsaturation pair
(`lem:typeB-postledger-core-hygiene`'s region, `lem:typeA-receiver-loads` /
`lem:typeA-unsaturated-discharge` read off the centres), and (ii) the
negative zero-surplus handoff pieces carry the grouped decorated-envelope
fan-assignment data of `def:typeB-assigned-ledger`: a high-degree centre
family, per-piece absorbed cores with the off-absorbed pair, and the absorbed
cardinalities covered by the centres' cubic-closed counts
(`lem:decorated-envelope-deficit-bound`'s hypotheses).  The census `[123]`
cases on this statement exactly as `[113]` cases on its deficit reading. -/
def TypeBSublinearHypotheses (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    (∀ component ∈ object.canonicalPieces (object.remainderSupport packing),
      let piece := object.pieceSupport (object.remainderSupport packing)
        component
      object.NegativeNetCharge piece data.threshold data.dischargeScale →
      0 < object.ambientSurplus piece data.threshold →
      Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
        data.threshold data.dischargeScale) ∧
    ∃ handoffPieces : Finset (Graph.SupportComponents.Connected.Component
        object (object.remainderSupport packing)),
      (∀ component,
        component ∈ handoffPieces ↔
          component ∈ object.canonicalPieces (object.remainderSupport packing) ∧
            (let piece := object.pieceSupport (object.remainderSupport packing)
              component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              HandoffProduced data object packing piece)) ∧
      ∃ centres : Finset object.Vertex,
        (∀ centre ∈ centres, data.threshold < object.degree centre) ∧
        ∃ fanEnvelope : object.Vertex → Finset object.Vertex,
        ∃ absorbedAt : Finset object.Vertex → Finset object.Vertex,
          (∀ component ∈ handoffPieces,
            let piece := object.pieceSupport (object.remainderSupport packing)
              component
            absorbedAt piece ⊆ piece ∧
              (∀ vertex ∈ piece \ absorbedAt piece,
                object.internalDegree piece vertex ≤ data.threshold) ∧
              (∀ vertex ∈ piece \ absorbedAt piece,
                object.internalDegree piece vertex = data.threshold →
                ∃ receiver : object.Vertex,
                  object.traceReceiver? piece data.threshold vertex =
                      some receiver ∧
                    object.IsReceiver piece data.threshold receiver ∧
                      receiver ∉ absorbedAt piece) ∧
              ∀ receiver ∈ object.receivers piece data.threshold \
                  absorbedAt piece,
                1 + object.restrictedLoad piece (absorbedAt piece)
                    data.threshold receiver ≤
                  data.dischargeScale *
                    object.missingPorts piece data.threshold receiver) ∧
          ∑ component ∈ handoffPieces,
              (absorbedAt (object.pieceSupport
                (object.remainderSupport packing) component)).card ≤
            ∑ centre ∈ centres,
              Graph.TypeBFanIncidence.closedCount object data.threshold
                (fanEnvelope centre) centre

/-- The canonical component collection `\tilde{\mathcal X}` of
`def:typeA-unified-negative`. -/
noncomputable def route8UnifiedComponents (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) := by
  classical
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  exact (object.canonicalPieces support).filter fun component =>
    let piece := object.pieceSupport support component
    object.ambientSurplus piece data.threshold = 0 ∧
      object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      ¬ HandoffProduced data object packing piece

/-- The paper's unified indexed collection `\tilde\Xi`: saturated receivers
and unpaid silent loads of the supports in `\tilde{\mathcal X}`. -/
noncomputable def route8UnifiedEntries (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.Route8Census.Index object) :=
  Graph.Route8Census.entriesOfComponents object
    (canonicalWindowPacking data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale

/-- The `[113]`-tested quotient-freeness of the unified census
(`def:typeA-trace-basin` (b) at every unified entry's selected basin): the
plain trace-response quotient — the cased exit-`(5)` state of the ratified
calibration — occurs at no entry.  Tested, never refuted from the invariants;
the no arm retains its literal negation as the manuscript's profile-record
residual lane. -/
def Route8QuotientFreeStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (∀ index ∈ route8UnifiedEntries data object,
      ∀ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin →
          ¬ ∃ retained,
            Graph.Route8.TraceBasin.TraceResponseQuotient object index.1
              data.threshold data.LengthOK index.2.1 index.2.2 basin retained) ∧
    -- the same clause-(b) state at every candidate extracted core of the
    -- bridge pieces (`lem:typeB-bridge-with-route8-core`'s deleted regions):
    -- on the free arm every negative no-handoff core of a deleted region is
    -- exactly a member of `route8ExtractedCores`.
    ∀ component ∈ (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).filter
          fun component =>
            object.NegativeNetCharge
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component)
                data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component)
                data.threshold,
      let deleted := object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component \
        Graph.TypeBRefinedSupport.centres object data.threshold
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component)
      ∀ core ∈ (object.canonicalPieces deleted).image
          (object.pieceSupport deleted),
        object.NegativeNetCharge core data.threshold data.dischargeScale →
        ¬ HandoffProduced data object (canonicalWindowPacking data object)
          core →
        ∀ receiver ∈ object.receivers core data.threshold,
          ∀ load ∈ Graph.VisibleEntry.excessBasinReduced object core
              data.threshold data.dischargeScale receiver ∅,
            ∀ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object core data.threshold
                  receiver load = some basin →
                ¬ ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object core
                    data.threshold data.LengthOK receiver load basin retained

open scoped Classical in
/-- **`def:typeA-pressure-ledger` with `lem:typeA-pressure-ledger-no-overcount`
and `lem:typeA-pressure-records-canonical`**, on the unified collection: a
2/3-demand ledger over `Ξ̃` pinning every minimal entry that holds at least
`δ` private essential incidences (clause (L1); a minimal entry below that
bound is the terminal two-support obstruction, closed on the other arm of
the dichotomy), chosen maximizing first `N₃`, then `N₂`; its assigned
incidences satisfy the raw no-overcount `3N₃ + 2N₂ ≤ e(R, W)` and the defect
form `3Ñ ≤ e(R, W) + 𝖯_ext`; and every target-defect entry left in
`Ξ₂ ∪ Ξ_res` carries its canonical actual or profile demand record. -/
noncomputable def Route8DemandLedgerStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∃ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P ∧
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) ∧
      (3 * P.three.card + 2 * P.two.card ≤
        object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object))) ∧
      (3 * entries.card ≤
        object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
          P.externalDefect) ∧
      ∀ index ∈ P.two ∪ P.residual,
        Graph.Route8.TraceBasin.TraceLocalTargetDefect object index.1
            data.threshold data.LengthOK index.2.1 index.2.2
            (Graph.Route8Census.basin object data.threshold index) →
          Graph.Route8.TraceBasin.CanonicalDemandRecord object
            (Graph.Route8Census.basin object data.threshold index)
            data.LengthOK

/-- **`def:typeA-unified-negative`**, on the literal active remainder.

The component filter is exactly
`σ(X) = 0`, `N₀(X) < 0`, and no decorated Type B handoff.  The natural-number
summand is the discharge-cleared value `s·δ(X) = |V(X)| - s·def⁺(X)`; its
strict positivity is recorded for every member, exactly as in the definition.
No large-budget lower bound, entry classification, carrier theorem, or peeling
invariant is part of this schema. -/
abbrev Route8UnifiedNegative (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let unified := route8UnifiedComponents data object
  ∃ collection : Finset (Finset object.Vertex),
    collection = unified.image (object.pieceSupport support) ∧
      (∀ piece ∈ collection,
        object.ambientSurplus piece data.threshold = 0 ∧
          object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          ¬ HandoffProduced data object packing piece ∧
          0 < piece.card -
            data.dischargeScale * object.positiveDeficiency piece data.threshold) ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          ∑ piece ∈ collection,
            (piece.card -
              data.dischargeScale * object.positiveDeficiency piece data.threshold)

/-- The exact route-8/target-defect classification of one unified entry.

The selected trace basin is either target-complete-minimal, with the canonical
exit-(4) family absent, or alternative (a) is the sole surviving failure and
its load has the canonical exit-(4) witness.  The common lower bound
`alpha >= 2` is `lem:typeA-unified-carriers`. -/
abbrev Route8UnifiedEntryFacts (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let basin := Graph.Route8Census.basin object data.threshold index
  let entry := (Graph.Route8Census.presented object data.threshold data.LengthOK
    index).toEntry (Graph.HasCycleWithLength data.LengthOK)
  Graph.Route8.TraceBasin.select? object index.1 data.threshold index.2.1
      index.2.2 = some basin ∧
    2 ≤ entry.alpha ∧
    (Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∨
      (Graph.Route8.TraceBasin.TraceLocalTargetDefect object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        (¬ ∃ retained,
          Graph.Route8.TraceBasin.TraceResponseQuotient object index.1
            data.threshold data.LengthOK index.2.1 index.2.2 basin retained) ∧
        ¬ Graph.Route8.TraceBasin.TraceDelocalization object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        ¬ Graph.Route8.TraceBasin.TraceSurvivingSeparator object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold data.dischargeScale
            index.2.1 ∅,
          witness.load = index.2.2))

/-- **`lem:typeA-unified-deficit`** (node `[123]`): the unified collection
carries the whole large-budget deficit, cleared of denominators. -/
abbrev Route8UnifiedDeficitFact (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let components := route8UnifiedComponents data object
  support.card ≤
    Graph.TypeBEnvelopeCharge.route8Deficit object support data.threshold
        data.dischargeScale components +
      data.dischargeScale * (Graph.Route8Census.supply object packing).card +
      2 * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount)

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers` and
`def:typeA-pressure-ledger`** (node `[123]`): the exact per-entry census. -/
abbrev Route8UnifiedEntryCensusFact (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ index ∈ route8UnifiedEntries data object,
    Route8UnifiedEntryFacts data object index

/-- **`lem:typeB-bridge-with-route8-core`'s canonical collection `𝒜_X`** (the
appendix rows for nodes `[74]`/`[76]`/`[85]`: "after any route-8 non-window
core is extracted into `D_A`"), on the literal active remainder.

For every negative positive-surplus canonical piece `X`, the deleted region
`X ∖ centres(X)` — the piece with its high centres deleted, the region
discharged by `Graph.TypeBBridgeMass.bridge_mass_of_centre_deletion` — is
decomposed into its own canonical connected components, and the collection
keeps exactly the components carrying `def:typeA-unified-negative`'s clauses at
the extracted core: `σ = 0`, `N₀ < 0`, no decorated Type B handoff, and every
indexed entry of the core in the quotient-free lane (the `[104]` calibration's
plain trace-response-quotient state occurs at no entry; a component carrying a
profile-record entry is not a route-8 core and stays with the bridge
residual). -/
noncomputable def route8ExtractedCores (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  exact ((object.canonicalPieces support).filter fun component =>
      object.NegativeNetCharge (object.pieceSupport support component)
          data.threshold data.dischargeScale ∧
        0 < object.ambientSurplus (object.pieceSupport support component)
          data.threshold).biUnion
    fun component =>
      let deleted := object.pieceSupport support component \
        Graph.TypeBRefinedSupport.centres object data.threshold
          (object.pieceSupport support component)
      ((object.canonicalPieces deleted).image
          (object.pieceSupport deleted)).filter fun core =>
        object.ambientSurplus core data.threshold = 0 ∧
          object.NegativeNetCharge core data.threshold data.dischargeScale ∧
          ¬ HandoffProduced data object packing core ∧
          ∀ receiver ∈ object.receivers core data.threshold,
            ∀ load ∈ Graph.VisibleEntry.excessBasinReduced object core
                data.threshold data.dischargeScale receiver ∅,
              ∀ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.select? object core data.threshold
                    receiver load = some basin →
                  ¬ ∃ retained,
                    Graph.Route8.TraceBasin.TraceResponseQuotient object core
                      data.threshold data.LengthOK receiver load basin retained

/-- **`def:typeA-unified-entries` at the extracted cores**: the indexed entries
`(Y, w, u)` of the members of `𝒜_X` — every receiver of the core with each of
its unpaid excess loads at the empty peeling, exactly the loads
`Graph.TypeBBridgeMass.bridge_mass_of_centre_deletion`'s staged discharge of
the deleted region counts. -/
noncomputable def route8ExtractedEntries (data : Data.{u})
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.Route8Census.Index object) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (route8ExtractedCores data object).biUnion fun core =>
    (object.receivers core data.threshold).biUnion fun receiver =>
      (Graph.VisibleEntry.excessBasinReduced object core data.threshold
        data.dischargeScale receiver ∅).image
        fun load => (core, receiver, load)

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the
extracted route-8 cores** (node `[123]`): the exact per-entry census, in the
same schema as the unified collection's own census. -/
abbrev Route8ExtractedEntryCensusFact (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ index ∈ route8ExtractedEntries data object,
    Route8UnifiedEntryFacts data object index

/-- **`D_A(𝒜_X)` summed over the bridge pieces**
(`lem:typeB-bridge-with-route8-core` / `lem:decorated-envelope-with-route8-core`:
"Summing over `Y ∈ 𝒜_X` gives the route-8 core contribution `−D_A(𝒜_X)`"):
the cleared route-8 deficit of the extracted cores, in `route8Deficit`'s own
summand shape. -/
noncomputable def route8ExtractedDeficit (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Nat :=
  ∑ core ∈ route8ExtractedCores data object,
    (core.card -
      data.dischargeScale * object.positiveDeficiency core data.threshold)

/-- **The repaired failed-stage arm of `thm:large-budget-route8-only`** (node
`[123]`): a recorded target-defect peel chain, its exact reduced/full
stage accounting, and failure of the sufficient stage rate.  This is routed
to node `[181]`; it is not a contradiction. -/
abbrev Route8StageRateFailedFact (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let entries := route8UnifiedEntries data object
  let bridgeSlack := 2 * (data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount)
  ∃ chain : List (Graph.Route8Census.Index object),
    Graph.Route8Pressure.PeelChain object packing entries data.threshold
        data.dischargeScale bridgeSlack data.LengthOK chain ∧
      Graph.Route8Pressure.StageAccounting object packing entries
        (route8UnifiedComponents data object) data.threshold
        data.dischargeScale bridgeSlack chain ∧
      ¬ Graph.Route8Pressure.StageRate object packing data.threshold
          data.dischargeScale bridgeSlack chain.toFinset

open scoped Classical in
/-- **`def:typeA-pressure-absorbers` with
`lem:typeA-pressure-absorber-no-overcount`**, on the committed maximal
2/3-demand ledger: the demand units `𝒰_press` of the unpaid classes carry a
type-(A1)/(A2) absorption — a single-use assignment of fresh boundary
incidences of the cut of `R` to the absorbed units, disjoint from every
ledger assignment, together with a disjoint type-(A2) dependence set; with
the type-(A2) set held, no fresh single-use assignment absorbs more units —
whose open remainder `𝖯_open = |𝒰_press ∖ 𝒰_abs|` satisfies the
subtraction-free display `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`, the manuscript's
`3Ñ − 𝖯_open ≤ def⁺(R) + B_dep`. -/
noncomputable def Route8DemandAbsorptionStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∀ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P →
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) →
      3 * P.three.card + 2 * P.two.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) →
      3 * entries.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
            P.externalDefect →
      ∃ (A : Graph.DemandPartition.Absorption P
            (Graph.Route8Census.Index object × Nat))
        (dep : Finset (Graph.Route8Census.Index object × Nat)),
        A.absorbed ⊆ P.demandUnits ∧
          (∀ υ ∈ A.absorbed, A.absorber υ ∈
            Graph.Route8Census.supply object
              (canonicalWindowPacking data object)) ∧
          dep ⊆ P.demandUnits ∧
          Disjoint A.absorbed dep ∧
          (∀ B : Graph.DemandPartition.Absorption P
              (Graph.Route8Census.Index object × Nat),
            B.absorbed ⊆ P.demandUnits →
            (∀ υ ∈ B.absorbed, B.absorber υ ∈
              Graph.Route8Census.supply object
                (canonicalWindowPacking data object)) →
            Disjoint B.absorbed dep →
            B.absorbed.card ≤ A.absorbed.card) ∧
          3 * entries.card ≤
            object.boundaryIncidence
              (object.remainderSupport (canonicalWindowPacking data object)) +
              dep.card + (P.demandUnits \ (A.absorbed ∪ dep)).card

open scoped Classical in
/-- **`def:typeA-open-window-blocker` with
`lem:typeA-open-window-blocker-count`**, on the committed ledger and
absorption: every open demand unit is assigned a packed window — its entry's
support is a component of the `P₁₃`-free remainder, so a boundary incidence
of the entry leaves `R` into the packed-window support `W` — and the open
demand is exactly the window-blocker load partition
`𝖯_open = Σ_P B_open(P)`.  The concrete lexicographic blocker choice is a
classical witness, as everywhere in this lane. -/
noncomputable def Route8WindowBlockersStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∀ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P →
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) →
      3 * P.three.card + 2 * P.two.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) →
      3 * entries.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
            P.externalDefect →
      ∀ (A : Graph.DemandPartition.Absorption P
            (Graph.Route8Census.Index object × Nat))
        (dep : Finset (Graph.Route8Census.Index object × Nat)),
        A.absorbed ⊆ P.demandUnits →
        (∀ υ ∈ A.absorbed, A.absorber υ ∈
          Graph.Route8Census.supply object
            (canonicalWindowPacking data object)) →
        dep ⊆ P.demandUnits →
        Disjoint A.absorbed dep →
        ∃ blocker : Graph.Route8Census.Index object × Nat →
            Finset object.Vertex,
          (∀ υ ∈ P.demandUnits \ (A.absorbed ∪ dep),
            blocker υ ∈ canonicalWindowPacking data object) ∧
          (P.demandUnits \ (A.absorbed ∪ dep)).card =
            ∑ window ∈ canonicalWindowPacking data object,
              ((P.demandUnits \ (A.absorbed ∪ dep)).filter
                fun υ => blocker υ = window).card

/-- **Node `[181]`, the explicit peeled target-defect demand residual.**  The
failed peeling stage keeps its exact accounting, and the full unified entries
have been passed through the maximal 2/3-demand ledger, maximal absorption,
and exact packed-window blocker partition.  No smallness or same-window cap is
asserted here. -/
noncomputable def Route8PeeledDemandResidualStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8StageRateFailedFact data object ∧
    Route8DemandLedgerStatement data object ∧
    Route8DemandAbsorptionStatement data object ∧
    Route8WindowBlockersStatement data object

/-- Node `[111]`, `def:typeA-large-budget-deficit`: extract the canonical
collection `𝒳_A` of Type A pieces all of whose saturated receivers survive in
the route-`8` residual, and name its deficit.  The value below is the cleared
quantity `s · D_A(𝒳_A)`, with `s = data.dischargeScale`; it is exactly
`Graph.TypeBEnvelopeCharge.route8Deficit` on the component collection.  The
basin burden and the large-budget lower bound belong to `[112]` and `[113]` and
are deliberately absent here. -/
abbrev Route8GlobalSqueeze (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ collection : Finset (Finset object.Vertex),
    collection = routeEight.image (object.pieceSupport support) ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          Graph.TypeBEnvelopeCharge.route8Deficit object support
            data.threshold data.dischargeScale routeEight

/-- Node `[112]`, `lem:typeA-route8-burden`, cleared by the registered scale.

`basinCount` is exactly
`Σ_{X ∈ 𝒳_A} Σ_w |𝒰_X(w)|`; membership in `Route8Survives` supplies the
selected target-complete-minimal basin attached to every indexed unpaid silent
load.  The final inequality is therefore
`s · D_A(𝒳_A) ≤ N_basin(𝒳_A)`.  The large-budget lower bound belongs only to
node `[113]`. -/
abbrev Route8BasinBurden (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ basinCount : Nat,
    basinCount =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale receiver).card ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          Graph.TypeBEnvelopeCharge.route8Deficit object support
            data.threshold data.dischargeScale routeEight ∧
          scaledDeficit ≤ basinCount

/-- Node `[113]`, `def:typeA-large-budget-deficit`, in exact finite form.

The paper's inequality
`D_A(𝒳_A) ≥ (1/4 - τ_win)|R| - o(|R|)` is cleared by the registered discharge
scale `s`: `|R| ≤ s D_A(𝒳_A) + s |∂R| + o(|R|)`.  The first summand below is
exactly `s D_A(𝒳_A)`, `boundaryIncidence` is the finite stub supply defining
`τ_win`, and the registered Type B bridge allowance is the explicit finite
representative of the sublinear term.  The canonical packing and
`Route8Survives` filter are definitionally the collection fixed at `[111]`; no
upstream burden fact is republished inside this key.

The manuscript's later unified-demand correction observes that this fact does
not follow merely from `LargeBudgetResidual`: target-defect Type A supports may
carry the missing mass.  Consequently node `[113]` is tested exactly, and its
complement is routed to node `[123]` rather than being fabricated. -/
abbrev Route8LargeBudgetDeficit (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  support.card ≤
    Graph.TypeBEnvelopeCharge.route8Deficit object support
        data.threshold data.dischargeScale routeEight +
      data.dischargeScale * object.boundaryIncidence support +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount

/-- Node `[114]`: every indexed entry of the selected canonical route-`8`
collection passes to the essential carrier core of its graph-derived
trace-basin reading.  The quantifiers below are the actual `(X,w,u,B_u)`
indices of `[111]`--`[112]`; no arbitrary `PresentedEntry` can be supplied by a
caller.  The large-budget inequality remains available from the literal
`[113]` ledger ancestry and is not republished inside this key. -/
abbrev Route8CarrierCore (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∀ component ∈ routeEight,
    let piece := object.pieceSupport support component
    ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale,
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        let index : Graph.Route8Census.Index object := (piece, receiver, load)
        let presented := Graph.Route8Census.presented object data.threshold
          data.LengthOK index
        (presented.toEntry
          (Graph.HasCycleWithLength data.LengthOK)).CarrierCoreFacts

/-- Node `[114]`, `def:typeA-true-route8-residual`, on the exact collection
selected at `[111]`.

The first conjunct is clause (R3), the literal admissible silent-core profile
already committed at `[110]`.  For every actual `(X,w,u,B_u)` index, membership
in `saturatedReceivers` exposes (R1); `SilentFirst` records the absence of the
visible exits (1)--(3); and `TargetCompleteMinimal` at the canonical selected
basin records both the absence of the trace-response exits (4)--(7) and (R4).
The carrier-core fact committed immediately before this one stays in the
incoming ledger and is not republished here. -/
abbrev Route8TrueResidual (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  SilentCoreResidualProfile data object ∧
    ∀ component ∈ routeEight,
      let piece := object.pieceSupport support component
      Graph.Route8Deficit.SilentFirst object piece data.threshold
          data.dischargeScale ∧
        ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
            data.threshold data.dischargeScale,
          object.IsReceiver piece data.threshold receiver ∧
            object.Saturated piece data.threshold data.dischargeScale receiver ∧
            ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
                data.dischargeScale receiver,
              let index : Graph.Route8Census.Index object :=
                (piece, receiver, load)
              let basin := Graph.Route8Census.basin object data.threshold index
              Graph.Route8.TraceBasin.select? object piece data.threshold
                    receiver load = some basin ∧
                Graph.Route8.TraceBasin.TargetCompleteMinimal object piece
                    data.threshold data.LengthOK receiver load basin ∧
                  ¬ ∃ witness : Graph.ExitFour.Witness
                      (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                      receiver ∅,
                    witness.load = load

/-- Node `[114]`, `lem:typeA-carrier-cut-parity`, at the exact indexed entries
selected by `[111]` and restricted to their canonical essential carrier cores.

`CoordinateEvent` is the graph-derived simple cycle obtained by adjoining the
root edge to an edge-rooted return (and is already a simple cycle when the
event began as one).  The two edge hypotheses below are therefore the paper's
literal mixed-event hypothesis: one event edge has both ends in `B_u`, and one
event edge has an end outside `X`.  Membership in `retained essentialCore` is
exactly survival in `rho_u(B_u)|_{C_ess(xi)}`.  The conclusion counts the
distinct boundary incidences recorded by the coordinate that lie in
`C_ess(xi)`; it makes no assertion about non-mixed coordinates. -/
abbrev Route8CarrierCutParity (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∀ component ∈ routeEight,
    let piece := object.pieceSupport support component
    ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale,
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        let index : Graph.Route8Census.Index object := (piece, receiver, load)
        let basin := Graph.Route8Census.basin object data.threshold index
        let presented := Graph.Route8Census.presented object data.threshold
          data.LengthOK index
        let entry := presented.toEntry
          (Graph.HasCycleWithLength data.LengthOK)
        ∀ coordinate ∈ entry.retained entry.essentialCore,
          ∀ event : Graph.Route8.CoordinateEvent object,
            presented.event? coordinate = some event →
              (∃ left right : object.Vertex,
                s(left, right) ∈ event.walk.edges ∧
                  left ∈ basin ∧ right ∈ basin) →
              (∃ left right : object.Vertex,
                s(left, right) ∈ event.walk.edges ∧
                  (left ∉ piece ∨ right ∉ piece)) →
              2 ≤ (entry.car coordinate ∩ entry.essentialCore).card

/-- Node `[115]`, yes arm, on the literal collection selected at `[111]`.
There is an actual `(X,w,u,B_u)` entry whose canonical essential incidence
core has cardinality at most one. -/
abbrev Route8SmallCoreEntry (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8CarrierCore data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∃ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∃ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∃ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
            (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1

/-- Node `[115]`, no arm, on the same literal collection.  This is the exact
negation of `Route8SmallCoreEntry` after the inherited `[114]` fact has been
kept in the monotone ledger. -/
abbrev Route8NoSmallCoreEntry (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8CarrierCore data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∀ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          ¬ ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
            (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1

/-- Node `[116]`: for the selected small-core entry, the exact trace-basin
failure alternatives corresponding, in order, to exits `(4)`--`(7)`. -/
abbrev Route8SmallCoreCollapse (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  Route8SmallCoreEntry data object ∧
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∃ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∃ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∃ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          let basin := Graph.Route8Census.basin object data.threshold index
          ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
              (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1 ∧
            (Graph.Route8.TraceBasin.TraceLocalTargetDefect object piece
                data.threshold data.LengthOK receiver load basin ∨
              (∃ retained,
                Graph.Route8.TraceBasin.TraceResponseQuotient object piece
                  data.threshold data.LengthOK receiver load basin retained) ∨
              Graph.Route8.TraceBasin.TraceDelocalization object piece
                data.threshold data.LengthOK receiver load basin ∨
              Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
                data.threshold data.LengthOK receiver load basin)

/-- Node `[118]`: the actual selected two-support census entry together with
the declared deletion witnesses forced by its canonical essential core.

The presented reading, entry family, core family, and selected index are all
the graph-owned `Route8Census` data of the active object.  This is clause (T5)
of `def:typeA-terminal-two-carrier`; no arbitrary presentation or abstract
index family can be supplied by a caller. -/
abbrev Route8CarrierDeletionWitnesses (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  let entries := Graph.Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  ∃ index ∈ entries,
    let presented := Graph.Route8Census.presented object data.threshold
      data.LengthOK index
    let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
    Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
        data.threshold data.dischargeScale data.LengthOK index ∧
      Graph.Route8.TwoCarrierDeletionWitnesses (Target :=
        Graph.HasCycleWithLength data.LengthOK) entry.carriers
        entry.coordinates entry.car entry.state entries
        (Graph.Route8Census.core object data.threshold data.LengthOK)
        (data.threshold - 1) index

/-- Nodes `[119]`--`[120]`: the selected private-carrier budget stage on the
same route-`8` residual. -/
abbrev Route8PrivateCarrierBudget (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  let entries := Graph.Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  data.threshold * entries.card ≤
    (Graph.Route8Census.supply object packing).card

/-- Nodes `[121]`--`[122]`: the selected no-two-carrier contradiction stage. -/
abbrev Route8NoTwoCarrierContradiction (data : Data.{u})
    (_object : Graph.FiniteObject.{u}) : Prop := False

/-- Node `[124]`: terminal two-carrier route-`8` no-go.

This is exactly `thm:typeA-two-carrier-nogo` on the selected object: assuming
the actual [118] deletion-witness package produces a canonical Q5 exit-`(4)`
witness, contradicting the no-exit-`(4)` clause already recorded by the true
route-`8` residual.  The row proving this implication reads clauses (T2) and
(T3) from the incoming `ExactLedger`; they are not copied into this fact. -/
abbrev Route8TerminalNoGo (data : Data.{u})
    (_object : Graph.FiniteObject.{u}) : Prop := False

/-- **Nodes `[131]`/`[137]`, `prop:sparse-entropy-sandwich-with-blockers`'s
entropy count, at the full pair schedule** (`prop:sparse-entropy-sandwich`,
`cor:sparse-pair-entropy-saturation`): the mixed family `ℐ_spine ∪ ℛ_Π` of the
node-`[129]` baseline spine demand and all `C(σ,2)` pair coordinates realizes
its full code among the labelled skeletons of the current object,
`2^{|ℐ_spine| + C(σ,2)} ≤ C(N,m)` (`lem:independent-target-entropy` with
`lem:skeleton-dominates`).  The spine family is the one `def:baseline-spine-demand`
names: it survives every functional admissible rank quotient and its deficit
`E_spine ≤ C_E n` is admissible for the cubic baseline. -/
def FreePairEntropySandwichStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
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
        data.surplusScale * object.vertexCount ∧
      2 ^ (family.card + (object.degreeSurplus data.threshold).choose 2) ≤
        Graph.skeletonBudget object ∧
      2 ^ (object.degreeSurplus data.threshold).choose 2 ≤
        2 ^ Graph.spineDeficit object.vertexCount data.threshold family.card *
          object.vertexCount ^
            (object.edgeCount -
              Graph.cubicBaselineEdgeCount object.vertexCount data.threshold)

/-- The exact count-failure arm paired with node `[131]`'s sandwich.  It keeps
the baseline family selected from the incoming `[129]` fact and records that
this mixed family does not realize its full code. -/
def FreePairCodeUnrealizedStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
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
        data.surplusScale * object.vertexCount ∧
      ¬ 2 ^ (family.card + (object.degreeSurplus data.threshold).choose 2) ≤
        Graph.skeletonBudget object

/-- **Node `[137]`, `prop:sparse-entropy-sandwich-with-blockers` at the exact
node-`[136]` presentation.**  The presentation and every accounting identity
needed to recognize it are copied from the incoming `ExactLedger`; the entropy
count therefore concerns the free side of that very `Θ_cap`, not an arbitrary
or empty presentation. -/
def BlockedPairEntropySandwichStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold)
      (capacity : Graph.CapacityPresentation object data.threshold
        data.windowOrder),
    capacity.activation =
        (Graph.recordSparsePairDEBlockers
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK)
          (Graph.pairResponseActivation active)
          (object.portPairSchedule data.threshold)) ∧
      (object.primitiveCarrier data.threshold).card =
        object.vertexCount + 2 * object.edgeCount +
          object.degreeSurplus data.threshold ∧
      (object.primitiveCarrier data.threshold).card ≤
        object.primitiveCarrierSupply data.threshold ∧
      Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement object
        data.threshold data.windowOrder capacity.activation capacity.carrier
        capacity.packing ∧
      (object.portPairSchedule data.threshold).card =
        (object.degreeSurplus data.threshold).choose 2 ∧
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
          data.surplusScale * object.vertexCount ∧
        2 ^ (family.card +
            (Graph.freeSide object.vertexPairDecidableEq
              (object.portPairSchedule data.threshold)
            capacity.tokenOrder capacity.Eligible
            capacity.eligibleDecidable).card) ≤
          Graph.skeletonBudget object

/-- The paired count-failure arm, retaining the same concrete node-`[136]`
presentation and node-`[129]` baseline family. -/
def BlockedPairCodeUnrealizedStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold)
      (capacity : Graph.CapacityPresentation object data.threshold
        data.windowOrder),
    capacity.activation =
        (Graph.recordSparsePairDEBlockers
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK)
          (Graph.pairResponseActivation active)
          (object.portPairSchedule data.threshold)) ∧
      (object.primitiveCarrier data.threshold).card =
        object.vertexCount + 2 * object.edgeCount +
          object.degreeSurplus data.threshold ∧
      (object.primitiveCarrier data.threshold).card ≤
        object.primitiveCarrierSupply data.threshold ∧
      Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement object
        data.threshold data.windowOrder capacity.activation capacity.carrier
        capacity.packing ∧
      (object.portPairSchedule data.threshold).card =
        (object.degreeSurplus data.threshold).choose 2 ∧
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
            data.surplusScale * object.vertexCount ∧
          ¬ 2 ^ (family.card +
            (Graph.freeSide object.vertexPairDecidableEq
              (object.portPairSchedule data.threshold)
              capacity.tokenOrder capacity.Eligible
              capacity.eligibleDecidable).card) ≤
            Graph.skeletonBudget object

/-- **The canonical representative of a germ's corridor piece**
(`def:cold-corridor-first-failure`: "the canonical representative determined by
the repeated cold corridor state"; `def:proper-quotient-representative`): the
`Precedes`-least canonical piece with the corridor piece's boundary-degree
profile, its target response against every outside context, and its
completions' baseline (`Graph/CanonicalRealization`). -/
noncomputable def germCanonicalRepresentative (data : Data.{u})
    {object : Graph.FiniteObject.{u}}
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) :
    Graph.CanonicalPiece germ.atom.interface :=
  Graph.CanonicalPiece.cutStateRepresentative
    (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant germ.piece

/-- The finite range used by the manuscript's two-strand kernel census.  At
the registered `P₁₃` window this is `3·13 + 1 = 40`, so the semantic node
invokes exactly `survivors 13 40` without installing an application-owned
numeric field. -/
def twoStrandEnumerationBound (data : Data.{u}) : Nat :=
  3 * data.windowOrder + 1

/-- The literal graph-realized symmetric-strand witness of nodes
`[163]`--`[168]`, stated over one germ of the incoming extracted family.

`Q` and `E` are neutral and equal-length; `E` is embedded in the ambient graph
as the second internally-disjoint representative.  Its two cut coordinates
attach to one ambient-cubic cold window and each attachment has two distinct
outside stubs.  The recorded offsets give `d`, the common internal size gives
`ℓ`, and the two graph cycles imply the exact numerical closing test used by
`Graph.TwoStrand`.  No witness is stored beside the ledger: this entire
existential is the semantic proposition of its key. -/
noncomputable def GenuineSecondStrandConfiguration (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (config : Graph.TwoStrand.Configuration) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  exact ActiveColdGermStatement data object germ ∧
    germ.Neutral ∧ germ.increment = 0 ∧
    SecondStrandGraphRealizedStatement data germ ∧
    config.length = germ.piece.internalVertexCount + 1 ∧
    config.gap = Nat.dist (germ.record.offsets 0).1 (germ.record.offsets 1).1 ∧
    config.gap < data.windowOrder ∧
    (∃ window ∈ cubic,
      ∃ left right : object.Vertex,
        left ∈ window ∧ right ∈ window ∧ left ≠ right ∧
        (∃ x y : germ.atom.interface.Vertex,
          x ≠ y ∧
          germ.atom.pieceIntoAmbient (.inl x) = left ∧
          germ.atom.pieceIntoAmbient (.inl y) = right) ∧
        (∃ leftFirst leftSecond : object.Vertex,
          leftFirst ∈ object.externalNeighbours window left ∧
          leftSecond ∈ object.externalNeighbours window left ∧
          leftFirst ≠ leftSecond) ∧
        (∃ rightFirst rightSecond : object.Vertex,
          rightFirst ∈ object.externalNeighbours window right ∧
          rightSecond ∈ object.externalNeighbours window right ∧
          rightFirst ≠ rightSecond)) ∧
    (config.DyadicallyClosed → germ.Realizing)

/-- Node `[163]`, yes-arm: some neutral equal-length germ of the active
extracted family has its second representative graph-realized.  The finite
closing-length data and endpoint-stub conclusions belong to `[167]` and
`[168]`; they are deliberately not bundled into this branch test. -/
noncomputable def GenuineSecondStrandStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    ActiveColdGermStatement data object germ ∧
      germ.Neutral ∧
      germ.increment = 0 ∧
      SecondStrandGraphRealizedStatement data germ

/-- Node `[163]`, no-arm: on the same incoming extracted-family witness, no
neutral zero-increment germ has a graph-realized second strand.  Such a germ's
second representative is therefore the canonical replacement case of
`[165]`--`[166]`; canonical order itself is not the branch test. -/
noncomputable def CanonicalNeutralConfigurationStatement (data : Data.{u})
    (object : Graph.FiniteObject.{u}) : Prop :=
  ColdGermCandidatesStatement data object ∧
    ¬ GenuineSecondStrandStatement data object

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
      (¬ Graph.HasCycleWithLength data.LengthOK object ∧
        ∀ smaller : Graph.FiniteObject.{u},
          (progress BranchState Presentation presentation data).Smaller
            smaller object →
          Graph.MinimumDegreeAtLeast data.threshold smaller →
          Graph.HasCycleWithLength data.LengthOK smaller)
  | .cubicBaseline, _object => data.threshold = 3
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
  | .degreeProfileFibres, object =>
      ∀ (support : Finset object.Vertex)
        (left right : Graph.BoundaryPiece
          (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
            support)),
        Graph.Response.TargetComplete
            Graph.BoundaryPiece.boundaryDegreeProfile
            (Graph.HasCycleWithLength data.LengthOK) left right →
          left.boundaryDegreeProfile = right.boundaryDegreeProfile
  | .targetCompleteContextUniversality, object =>
      ∀ (support : Finset object.Vertex)
        (left right : Graph.BoundaryPiece
          (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
            support)),
        Graph.Response.TargetComplete
            Graph.BoundaryPiece.boundaryDegreeProfile
            (Graph.HasCycleWithLength data.LengthOK) left right →
          Graph.Response.ContextEquivalent
            (Graph.HasCycleWithLength data.LengthOK) left right
  | .replacementExclusion, object =>
      (∀ support : Finset object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object support)
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
  | .localAlgebra, object =>
      ∀ support : Finset object.Vertex,
        object.InducesWindow data.windowOrder support →
          ((Graph.WindowCurvature.Labels data.windowOrder).card = 399 ∧
            (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
              [13, 60, 122, 122, 63, 17, 2])
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
      -- `prop:p13-density` at node `[24]`, "after closure": the live-hot cap
      -- `2·rate·scaleCount·|𝒫_hot| ≤ (scaleCount + 1)(δn + T(n))` plus the
      -- cold-mass identity `|𝒫| = |𝒫_hot| + C` on the arm where the cold
      -- branch does not force a germ, `C ≤ 2σ(G) ≤ 2T(n)`.  Its asymptotic
      -- form is exactly `θ ≤ (δ/2)/rate + o(1)`, the manuscript's
      -- `θ_win = 1.5/118.108581006…`; the `o(1)` is the
      -- `(scaleCount + 1)/scaleCount` factor, the `T(n)` term, and the cold
      -- slack `4·rate·scaleCount·T(n)`, all exact here.
      (2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
          object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount object + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount) +
        data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
          data.surplusThreshold object.vertexCount)
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
                2 * object.positiveDeficiency support data.threshold) ∧
        (∀ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing →
          data.threshold * (object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card) ≤
              object.internalWedgeCount (object.remainderSupport packing) +
                2 * (data.threshold * (data.windowOrder * packing.card) +
                  data.surplusThreshold object.vertexCount))
  | .exactResponseProfile, object =>
      -- `def:exact-response-profile` at the remainder of every maximal packing.
      -- The declared raw curvature coordinates (clause (D4)) are the internal
      -- length-two wedges of `R`; the profile is *exact*: "two distinct
      -- coordinate labels remain distinct entries even if their numerical
      -- values in the embedded graph coincide", so the declared family has
      -- exactly `W₂(R)` labelled entries.  The boundary-degree and
      -- all-context target components of `ρ_T^ex` are the ones every
      -- admissible quotient below is tested against.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
          (remainderCurvatureTests object packing).card =
            remainderWedgeSupply object packing)
  | .admissibleRankQuotient, object =>
      -- `def:admissible-rank-quotient` at the remainder of every maximal
      -- packing: an admissible rank quotient of the raw curvature family
      -- (`remainderQuotient`: connected carrying support, boundary-degree
      -- fibre, all-context target-completeness) that is rank-reducing on the
      -- family is represented — at a proper support by a strictly smaller
      -- proper representative (`lem:replacement`'s five hypotheses), at the
      -- whole graph by a strictly smaller admissible closed representative.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
          ∀ quotient : remainderQuotient data object packing,
            quotient.toRankQuotient.RankReducingOn
              ↑(remainderCurvatureTests object packing) →
              Graph.Strategy.InterfaceReplacement.ReplacementSupport
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object quotient.support ∨
                ∃ representative : Graph.FiniteObject.{u},
                  representative.LexicographicallySmaller object ∧
                    Graph.MinimumDegreeAtLeast data.threshold representative ∧
                    (Graph.HasCycleWithLength data.LengthOK representative →
                      Graph.HasCycleWithLength data.LengthOK object))
  | .curvatureTargetRank, object =>
      -- `def:curvature-target-rank` at the remainder of every maximal packing:
      -- a subfamily of `𝒲₂(R)` survives when every functional admissible rank
      -- quotient is label-injective on it; `r_Ω(R)` is the maximum size of a
      -- surviving subfamily — attained, and an upper bound for every
      -- surviving subfamily.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
          (∃ independent ⊆ remainderCurvatureTests object packing,
            Graph.FiniteObject.SurvivesCurvatureSystem
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              (object.remainderSupport packing) independent ∧
            independent.card = remainderCurvatureTargetRank data object packing) ∧
          ∀ candidate ⊆ remainderCurvatureTests object packing,
            Graph.FiniteObject.SurvivesCurvatureSystem
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              (object.remainderSupport packing) candidate →
            candidate.card ≤ remainderCurvatureTargetRank data object packing)
  | .targetRankCircuit, object =>
      -- `lem:target-rank-circuit` at the remainder of every maximal packing.
      -- For a maximal surviving subfamily `𝓘` and a raw test `a ∉ 𝓘`, some
      -- functional admissible rank quotient that loses rank on the family
      -- determines `a` from a finite subfamily `ℬ ⊆ 𝓘`: a proper
      -- target-dependence `(a, ℬ)` (`def:curvature-target-dependence`).  In
      -- particular, if no proper target-dependence exists among the raw tests,
      -- the whole family survives every functional admissible rank quotient.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
          let tests := remainderCurvatureTests object packing
          let ProperDependence := fun
              (test : object.InternalWedge (object.remainderSupport packing))
              (determiners : Set (object.InternalWedge (object.remainderSupport packing))) =>
            determiners.Finite ∧ test ∉ determiners ∧
              ∃ quotient : remainderQuotient data object packing,
                quotient.toRankQuotient.FunctionalOn ↑tests ∧
                  quotient.toRankQuotient.RankReducingOn ↑tests ∧
                    quotient.toRankQuotient.Determines test determiners
          (∀ independent ⊆ tests,
            Graph.FiniteObject.SurvivesCurvatureSystem
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              (object.remainderSupport packing) independent →
            independent.card = remainderCurvatureTargetRank data object packing →
            ∀ test ∈ tests, test ∉ independent →
              ∃ determiners, determiners ⊆ ↑independent ∧
                ProperDependence test determiners) ∧
          ((¬ ∃ test ∈ tests, ∃ determiners, determiners ⊆ ↑tests ∧
              ProperDependence test determiners) →
            Graph.FiniteObject.SurvivesCurvatureSystem
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              (object.remainderSupport packing) tests))
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
  | .separatedTesters, object =>
      -- `lem:separated-testers`, with each manuscript object represented
      -- literally.  `closedBall` is the rooted radius-`r` neighbourhood.  The
      -- rooted graph isomorphism maps the two wedge centres and their two
      -- neighbours.  An ambient target tester is the outside side of an exact
      -- owned decomposition whose piece side is the union of the two balls;
      -- its internal support is therefore in their complement.  Finally an
      -- attempted rank quotient identifying the wedge labels is either valid
      -- against every outside context or exhibits an identified pair with a
      -- concrete target-defect context.
      (∀ (packing : Finset (Finset object.Vertex)),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
        ∀ (radius : Nat) (u v : object.Vertex),
          u ∈ object.remainderSupport packing →
          v ∈ object.remainderSupport packing →
          let closedBall := fun root : object.Vertex =>
            object.vertexFinset.filter fun vertex =>
              object.graph.edist vertex root ≤ radius
          ∀ (leftWedge rightWedge :
              object.InternalWedge (object.remainderSupport packing)),
            leftWedge ∈ remainderCurvatureTests object packing →
            rightWedge ∈ remainderCurvatureTests object packing →
            leftWedge.1 = u → rightWedge.1 = v →
            (∃ iso : (object.induce (closedBall u)).graph ≃g
                  (object.induce (closedBall v)).graph,
              (∀ hu : u ∈ closedBall u, (iso ⟨u, hu⟩).1 = v) ∧
              (∀ hv : v ∈ closedBall v, (iso.symm ⟨v, hv⟩).1 = u) ∧
              (∀ x, x ∈ leftWedge.2.1 →
                ∃ hx : x ∈ closedBall u,
                  (iso ⟨x, hx⟩).1 ∈ rightWedge.2.1) ∧
              (∀ y, y ∈ rightWedge.2.1 →
                ∃ hy : y ∈ closedBall v,
                  (iso.symm ⟨y, hy⟩).1 ∈ leftWedge.2.1)) →
            Disjoint (closedBall u) (closedBall v) →
            (∀ (decomposition : Graph.OwnedDecomposition object),
              (∀ vertex, (vertex ∈ closedBall u ∨ vertex ∈ closedBall v) ↔
                ∃ inside, decomposition.pieceIntoAmbient inside = vertex) →
              ∀ (represented :
                  object.InternalWedge (object.remainderSupport packing) →
                    Graph.BoundaryPiece decomposition.interface),
                ¬ (Graph.HasCycleWithLength data.LengthOK
                      (Graph.glue (represented leftWedge) decomposition.outside) ↔
                    Graph.HasCycleWithLength data.LengthOK
                      (Graph.glue (represented rightWedge) decomposition.outside)) →
                ∀ internal : decomposition.outside.Internal,
                  decomposition.vertexEquiv
                      (Graph.contextEmbedding decomposition.piece
                        decomposition.outside (.inr internal)) ∉ closedBall u ∧
                  decomposition.vertexEquiv
                      (Graph.contextEmbedding decomposition.piece
                        decomposition.outside (.inr internal)) ∉ closedBall v) ∧
            (∀ (attempt : Graph.AttemptedQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object
                  (remainderCurvatureTests object packing)
                  (Graph.FiniteObject.internalWedgeSupport
                    (region := object.remainderSupport packing))),
              attempt.label leftWedge = attempt.label rightWedge →
              ((∀ left right : Graph.BoundaryPiece
                    (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                      object attempt.support),
                  attempt.Identifies left right →
                    Graph.Response.ContextEquivalent
                      (Graph.HasCycleWithLength data.LengthOK) left right) ∨
                ∃ left right : Graph.BoundaryPiece
                    (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                      object attempt.support),
                  attempt.Identifies left right ∧
                    Graph.Response.TargetDefect
                      (Graph.HasCycleWithLength data.LengthOK) left right)))
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
      -- is stated exactly under this hypothesis.  The paper's `Z` is the
      -- connected determination support carried by the quotient itself.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data object packing,
            (∃ test determiners supportData,
              DeterminationCertificate data object packing test determiners
                quotient supportData) ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ object.remainderSupport packing ∧
                  ∃ vertex,
                    vertex ∉ quotient.support ∧
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
                    vertex ∈ quotient.support)
  | .repairIdentity, object =>
      -- Node `[44]`, `lem:smearing-support-repair`: for each stipulated
      -- `1`--`3` repair component on the active support `Z = G`, the paper
      -- records only the handshake identity below.  The raw embedding and
      -- graph inclusion express that the repair network lies in the active
      -- graph; node `[43]`'s whole-support witness remains in its own earlier
      -- ledger entry instead of being copied into this value.
      ∀ component : Graph.OneThreeRepair.Component.{u},
        (∃ embedding : component.object.Vertex ↪ object.Vertex,
          component.object.graph.map embedding ≤ object.graph) →
        (component.internal.card : Int) =
          component.boundary.card - 2 +
            2 * component.cycleRank - component.surplus
  | .globalBarrier, object =>
      -- Node `[45]`, `lem:no-silent-global-smearing`: node `[43]` has already
      -- established that the target-complete rank-reducing quotient has
      -- support `Z = G`.  The closed admissibility clause therefore supplies
      -- exactly the strictly smaller admissible closed representative below;
      -- the earlier quotient and coverage data remain in their own ledger
      -- entry and are not republished here.
      ∃ representative : Graph.FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK object)
  | .coldCorridorState, object =>
      -- The ledger retains the actual corridor presentations, state readings,
      -- first repeat, exact table record, and the paper's terminal/repeated
      -- exchange representative.  Consumers recover those witnesses from this
      -- key; they do not supply a fresh `Presentation` or manufacture a row.
      ColdCorridorStateStatement data object
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
      ColdGermCandidatesStatement data object ∧
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
      ColdGermCandidatesStatement data object ∧
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
      ColdGermCandidatesStatement data object ∧
        ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
          ∀ (Profile : Type)
            (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
            germ.Distinguishing →
              ¬ Graph.Response.TargetComplete profile
                (Graph.HasCycleWithLength data.LengthOK) germ.piece germ.canonical
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
  | .coldMassLinear, object =>
      ColdMassLinearStatement data object
  | .coldMassBounded, object =>
      ColdMassBoundedStatement data object
  | .bridgeless, object =>
      -- `lem:bridgeless`: "every edge of `G` lies on a cycle; equivalently
      -- `R_e(G) ≠ ∅` for every oriented edge".  `HasReturn` is a simple path
      -- from the tail back to the head after the edge is deleted.
      (∀ contraction : Graph.EdgeContraction object, contraction.HasReturn)
  | .windowPackageRealized, object =>
      WindowPackageRealized data object (canonicalWindowPacking data object)
  | .windowPackageUnrealized, object =>
      ¬ WindowPackageRealized data object (canonicalWindowPacking data object)
  | .densePackingOverflow, object =>
      Graph.skeletonBudget object <
        2 ^ (windowPackageBits data object *
          (canonicalWindowPacking data object).card)
  | .denseDeficiencyBelow, object =>
      DenseDeficiencyBelowStatement data object
  | .denseDeficiencyAtOrAbove, object =>
      ¬ DenseDeficiencyBelowStatement data object
  | .coldWindowStubStructure, object => by
      -- `lem:cold-window-stub-excess` read vertex by vertex at every ambient-cubic
      -- cold window of the fixed packing (`Graph/WindowStubStructure.lean`).
      classical
      exact (∀ window ∈ (canonicalColdWindows data object).filter (AmbientCubicWindow data object),
        ∃ ends : Finset object.Vertex, ends ⊆ window ∧ ends.card ≤ 2 ∧
          (∀ vertex ∈ window, vertex ∉ ends →
            (object.externalNeighbours window vertex).card = data.threshold - 2) ∧
          (∀ vertex ∈ ends,
            (object.externalNeighbours window vertex).card = data.threshold - 1) ∧
          (data.windowOrder - 2) * (data.threshold - 2) ≤
            ∑ vertex ∈ window.filter (fun vertex =>
              (object.externalNeighbours window vertex).card = data.threshold - 2),
              (object.externalNeighbours window vertex).card)
  | .coldCanonicalNeutralConfiguration, object =>
      CanonicalNeutralConfigurationStatement data object
  | .coldGenuineSecondStrand, object =>
      GenuineSecondStrandStatement data object
  | .coldCanonicalSwapSmaller, object =>
      ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
        germ.Neutral ∧
          (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount
  | .coldCanonicalSwapSameSize, object =>
      ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
        germ.Neutral →
          ¬ (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount
  | .blockedClassMember, object =>
      -- `def:blocked-class`, last sentence, at the fixed maximal packing: the
      -- object's skeleton has the baseline minimum degree, contains every packed
      -- window at its labelled position, and no accepted cycle passes through a
      -- window; and the class is dominated by the skeleton budget
      -- (`lem:skeleton-dominates`).  Read at `objectSkeleton`, the graph
      -- transported to `Fin n` by the object's own labelling.
      Graph.BlockedClass.MinDegreeAtLeast data.threshold
          (Graph.BlockedClass.objectSkeleton object) ∧
        Graph.BlockedClass.IsBlocked data.windowOrder data.LengthOK
          (Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object))
          (Graph.BlockedClass.objectSkeleton object) ∧
        Nat.card (Graph.BlockedClass.Blocked object.vertexCount object.edgeCount
            data.threshold data.windowOrder data.LengthOK
            (Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object))) ≤
          Graph.skeletonBudget object
  | .blockedScaleAdditive, object =>
      BlockedScaleAdditivityStatement data object
  | .blockedBarrierOverlap, object =>
      ¬ BlockedScaleAdditivityStatement data object
  | .absorbedGermFanData, object =>
      AbsorbedGermFanDataStatement data object
  | .absorbedGermSplit, object =>
      AbsorbedGermSplitStatement data object
  | .coldFamilyPositive, object =>
      0 < (canonicalColdWindows data object).card
  | .coldFamilyEmpty, object =>
      (canonicalColdWindows data object).card = 0
  | .coldReturnCorridors, object =>
      -- `def:cold-corridor-first-failure`: "each selected branch-excess
      -- half-edge has exactly one corridor" — at every outside component of
      -- `X_cold` and every boundary stub of it, the corridor with that entry
      -- exists (its two-stub clause is `lem:bridgeless`, its connection is the
      -- component's).
      (∀ component : Finset object.Vertex,
        Graph.ColdCorridor.IsOutsideComponent object
          (coldAmbientCubicSupport data object) component →
        ∀ entry : Fin (Graph.ColdCorridor.boundaryStubs object
            (coldAmbientCubicSupport data object) component).length,
          ∃ corridor : Graph.ColdCorridor.Corridor object
              (coldAmbientCubicSupport data object) component,
            corridor.entry = entry)
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
      let scales := data.separatedScaleCount object.vertexCount
      let bits := windowPackageBits data object
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
              data.windowRate * scales ≤ bits ∧
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
      ColdGermCandidatesStatement data object ∧
        ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object,
          germ.increment < 0 →
            germ.Distinguishing ∧
              (∀ (Profile : Type)
                (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
                ¬ Graph.Response.TargetComplete profile
                  (Graph.HasCycleWithLength data.LengthOK)
                  germ.piece germ.canonical) ∧
              (germ.Distinguishing ∨
                HandoffProduced data object (canonicalWindowPacking data object)
                  germ.support)
  | .coldBranchClosed, object =>
      -- `thm:cold-branch-quantitative-closure`, in the form consumed by the
      -- cold oval: after the current residual's length-changing germs and
      -- same-interface table rows have been routed, no local terminal cold
      -- pattern remains on this residual.
      Graph.ColdCorridor.NoTerminalColdResidual data.coldSignature data.threshold
        data.LengthOK (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
  | .forcedCurvatureCost, object =>
      -- `cor:forced-curvature-cost`, "from `lem:full-rank` and `lem:wedge-lower`":
      -- the exact equality `r_Ω(R) = W₂(R)` of node `[34]` substituted into
      -- node `[30]`'s demand floor (`K .wedgeSupply`'s "in particular"), both
      -- sides multiplied by the registered cost `c_Ω`:
      --   `c_Ω·(δ|R| + 2·2(order−1)p) ≤ c_Ω·r_Ω(R) + c_Ω·2(δ·order·p + T(n))`,
      -- the manuscript's `c_Ω r_Ω(R) ≥ K_win|R| − o(|R|)`, at the packing of
      -- the full-rank fact.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        data.curvatureCost *
              (data.threshold * (object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
            data.curvatureCost *
                remainderCurvatureTargetRank data object packing +
              data.curvatureCost *
                (2 * (data.threshold * (data.windowOrder * packing.card) +
                  data.surplusThreshold object.vertexCount)))
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
          (object.internalEdgeCount (object.remainderSupport packing))
          (object.remainderSupport packing).card)
  | .remainderEntropyLow, object =>
      -- Node `[50]`, no.  The exact negation, with the witness exhibited.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
            data.windowOrder data.threshold
            (object.positiveDeficiency (object.remainderSupport packing)
              data.threshold)
            (object.internalEdgeCount (object.remainderSupport packing))
            (object.remainderSupport packing).card)
  | .entropyPackageDemand, object =>
      -- Node `[52]`: `eq:feasibility`'s left-hand side.  Raising the joint
      -- demand to the `d`-th power clears the `1/d` the entropy split carries,
      -- and the high-entropy arm's `n^{|R|} ≤ |𝒢(R)|^d` is substituted for the
      -- remainder factor.  What the inequality says is that the window and
      -- remainder coordinates together realize at least `2^{rate·p}·n^{|R|/d}`
      -- states (`prop:two-budget` (a)).
      ((2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
              (canonicalHotWindows data object).card)) ^ data.entropyDenominator *
          object.vertexCount ^
            (object.remainderSupport (canonicalWindowPacking data object)).card ≤
        jointPackageDemand data object ^ data.entropyDenominator)
  | .entropyCapActive, object =>
      -- Node `[53]`, yes -- the terminal `[54]`.  `eq:entropy-cap`: the
      -- remaining non-curvature budget is strictly smaller than the forced
      -- curvature cost, i.e. the joint package strictly overflows the labelled
      -- skeleton budget of `lem:near-cubic-budget`.
      Graph.skeletonBudget object < jointPackageDemand data object
  | .entropyCapBound, object =>
      -- Node `[54]`: `lem:independent-target-entropy` and
      -- `lem:skeleton-dominates` bound the exact joint code by the labelled
      -- skeleton budget.  `K .entropyCapActive` is its strict negation.
      jointPackageDemand data object ≤ Graph.skeletonBudget object
  | .largeBudgetResidual, object =>
      -- Residual C.  The high-entropy arm reaches it through the exact
      -- skeleton comparison; the low-entropy arm is routed here unchanged, as `prop:two-budget` prescribes.
      LargeBudgetResidual data object
  | .netDeficiencyCap, object =>
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        packing.card = object.windowPackingNumber data.windowOrder →
        Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
            data.dischargeScale data.windowOrder data.windowRate
            data.spineScale data.densitySlack object.vertexCount →
          data.dischargeScale *
              (data.threshold * (data.windowOrder * packing.card) +
                data.spineScale * Core.ceilSqrt object.vertexCount) <
            data.dischargeScale *
                (2 * (data.windowOrder - 1) * packing.card) +
              (object.remainderSupport packing).card)
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
      -- Node `[59]`, yes: the selected maximum packing and the exact assertion
      -- `N₀(R) ≥ 0` for its remainder.  Carrying the packing in the fact keeps
      -- this a test of the paper's fixed `R`, rather than a statement about all
      -- possible maximal packings.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          object.NonNegativeNetCharge (object.remainderSupport packing)
            data.threshold data.dischargeScale)
  | .netChargeNegative, object =>
      -- Node `[59]`, no: the same selected maximum packing and `N₀(R) < 0`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          (∀ window : Finset object.Vertex,
            object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          object.NegativeNetCharge (object.remainderSupport packing)
            data.threshold data.dischargeScale)
  | .exactCollisionFails, object =>
      -- The exact complement of `K .netChargeCap` (`lem:exact-collision-test`):
      -- some maximal packing's remainder has nonnegative net charge.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
            object.NonNegativeNetCharge (object.remainderSupport packing)
              data.threshold data.dischargeScale)
  | .absorbedConfigurationResidual, object =>
      -- Node `[174]`, `lem:exact-collision-test`: at the failure witness
      -- packing, `|R| + s·σ_R ≤ s·def⁺(R)` combined with the exact stub supply
      -- `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W` and
      -- `|R| + order·p = n`, `p = |𝒫_hot| + |𝒫_cold|`, gives the manuscript's
      -- `C ≥ (n − A|𝒫_hot| − s(σ_W − σ_R))/A` with `A = s·(δ·order − 2(order−1)) + order`.
      (∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
            object.NonNegativeNetCharge (object.remainderSupport packing)
              data.threshold data.dischargeScale ∧
            object.vertexCount +
                data.dischargeScale *
                  object.ambientSurplus (object.remainderSupport packing)
                    data.threshold ≤
              data.netChargeCoefficient *
                  ((canonicalHotWindows data object).card +
                    (canonicalColdWindows data object).card) +
                data.dischargeScale *
                  object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
                    data.threshold)
  | .netChargeCap, object =>
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
          packing.card = object.windowPackingNumber data.windowOrder →
            object.NegativeNetCharge (object.remainderSupport packing)
              data.threshold data.dischargeScale)
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
  | .typeABoundedSupport, object =>
      -- Node `[87]`, on the selected incoming Type A support only.  Node `[27]`
      -- supplies induced-window freeness on this subregion.  A shortest path
      -- inside the piece is induced, so it has at most `windowOrder - 2`
      -- edges; zero surplus against the standing baseline makes the piece
      -- subcubic, and the rooted breadth-first count gives the displayed cap.
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
              Graph.InducedPathFree (object.induce piece) data.windowOrder ∧
              (∀ left ∈ piece, ∀ right ∈ piece,
                ∃ path : object.graph.Walk left right,
                  path.IsPath ∧
                    (∀ vertex ∈ path.support, vertex ∈ piece) ∧
                    path.length ≤ data.windowOrder - 2) ∧
              piece.card ≤
                1 + data.threshold *
                  (2 ^ (data.windowOrder - 2) - 1))
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
  | .typeBAssignedSupport, object =>
      -- Node `[65]` at the `[64]` entry: the assigned fan centres of the
      -- ordinary Type B support are its high centres, and there is one.
      TypeBSupportWith data object (fun _packing piece =>
        ∃ centre ∈ piece, Graph.IsHighCentre object data.threshold centre)
  | .typeBFanEntry, object =>
      TypeBFanEntryStatement data object
  | .typeBFanHeavyCentre, object =>
      -- Node `[68]`, yes arm on either literal Type B input: one actual assigned
      -- centre has degree strictly above `δ + 1` (greater than four in EG).
      TypeBFanHeavyCentreStatement data object
  | .typeBFanDegreeFourCentres, object =>
      -- Node `[68]`, no arm: every canonical assigned centre, or the chosen
      -- centre for every indexed `[177]` datum, has degree exactly `δ + 1`.
      TypeBFanDegreeFourCentresStatement data object
  | .typeBFanLocalDichotomy, object =>
      -- Node `[69]`, `cor:heavy-center-local-dichotomy`, on the common
      -- assigned-centre carrier selected by `[68]`: either the canonical
      -- support or the indexed decorated handoff from `[177]`.
      TypeBFanLocalDichotomyStatement data object
  | .typeBFanDegreeFourProfile, object =>
      -- Nodes `[78]`--`[79]` on either literal Type B carrier.  At every
      -- relevant degree-four centre this is `cor:degree-four-local-activation`
      -- together with the three displayed degree-four fan-profile identities.
      TypeBFanDegreeFourProfileStatement data object
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
  | .typeAExclusion, object =>
      -- Node `[86]`, `lem:typeA-exclusion` via `lem:density-mersenne`, stated
      -- at the minimal counterexample the branch carries, exactly at the
      -- paper's generality: over every connected admissible sub-support of
      -- its own maximal-packing remainders — "every admissible subcubic
      -- P₁₃-free target-safe boundaried piece", so the same fact serves the
      -- canonical pieces at `K .route8PiecesClassified` and the post-ledger
      -- core components of the Type B bridge pieces.  A negative zero-surplus
      -- piece leaves through the target-defect exit, the silent-core residual
      -- profile, or the decorated handoff.
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
          ((∃ receiver : object.Vertex,
              object.IsReceiver piece data.threshold receiver ∧
                Nonempty (Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                  data.dischargeScale receiver ∅)) ∨
            (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
                  data.threshold data.dischargeScale,
                (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
                    data.threshold data.dischargeScale receiver,
                  Graph.Route8.TraceBasin.Route8Entry object piece
                    data.threshold data.LengthOK receiver load ∨
                    ∃ basin : Finset object.Vertex,
                      Graph.Route8.TraceBasin.select? object piece
                          data.threshold receiver load = some basin ∧
                        ∃ retained,
                          Graph.Route8.TraceBasin.TraceResponseQuotient object
                            piece data.threshold data.LengthOK receiver load
                            basin retained) ∧
                ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                    receiver,
                  data.dischargeScale ≤
                    (Graph.VisibleEntry.visibleLoadsAt object piece
                      data.threshold receiver outside).card →
                  ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                      data.threshold data.dischargeScale receiver outside ∅,
                    Graph.Route8.TraceBasin.Route8Entry object piece
                      data.threshold data.LengthOK receiver load ∨
                      ∃ basin : Finset object.Vertex,
                        Graph.Route8.TraceBasin.select? object piece
                            data.threshold receiver load = some basin ∧
                          ∃ retained,
                            Graph.Route8.TraceBasin.TraceResponseQuotient object
                              piece data.threshold data.LengthOK receiver load
                              basin retained) ∨
            HandoffProduced data object packing piece) ∧
          -- The additive per-load publication
          -- (`lem:typeA-reduced-silent-residual` with the exit-(7) routing of
          -- `lem:typeA-exits-discharged`): at every saturated receiver, each
          -- unpaid silent-excess load and each selected visible unpeeled load
          -- of an overloaded completion port realizes the four-way split the
          -- executor derives before collapsing — the exit-(4) witness, the
          -- route-8 entry, the exit-(5) trace-response quotient, or the
          -- exit-(7) surviving separator whose recorded envelope is the
          -- produced decorated handoff.
          (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
              data.threshold data.dischargeScale,
            (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
                data.threshold data.dischargeScale receiver,
              (∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece
                  data.threshold data.dischargeScale receiver ∅,
                witness.load = load) ∨
                Graph.Route8.TraceBasin.Route8Entry object piece
                  data.threshold data.LengthOK receiver load ∨
                (∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.select? object piece
                      data.threshold receiver load = some basin ∧
                    ∃ retained,
                      Graph.Route8.TraceBasin.TraceResponseQuotient object
                        piece data.threshold data.LengthOK receiver load
                        basin retained) ∨
                ((∃ basin : Finset object.Vertex,
                    Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                      piece data.threshold data.LengthOK receiver load
                      basin) ∧
                  HandoffProduced data object packing piece)) ∧
            ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                receiver,
              data.dischargeScale ≤
                (Graph.VisibleEntry.visibleLoadsAt object piece
                  data.threshold receiver outside).card →
              ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver outside ∅,
                (∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver ∅,
                  witness.load = load) ∨
                  Graph.Route8.TraceBasin.Route8Entry object piece
                    data.threshold data.LengthOK receiver load ∨
                  (∃ basin : Finset object.Vertex,
                    Graph.Route8.TraceBasin.select? object piece
                        data.threshold receiver load = some basin ∧
                      ∃ retained,
                        Graph.Route8.TraceBasin.TraceResponseQuotient object
                          piece data.threshold data.LengthOK receiver load
                          basin retained) ∨
                  ((∃ basin : Finset object.Vertex,
                      Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                        piece data.threshold data.LengthOK receiver load
                        basin) ∧
                    HandoffProduced data object packing piece)))
  | .typeBBridgeReduction, object =>
      -- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`
      -- (`def:typeB-bridge-statements`), in the contrapositive the branch
      -- carries at every negative positive-surplus canonical piece: the exact
      -- B2 refinement with a nonnegative remaining core would give `N₀ ≥ 0`,
      -- so a negative piece carries the B2 disjoint ledger with strictly
      -- negative remaining scaled core charge — every remaining component the
      -- post-ledger Type A hygiene carrier of
      -- `lem:typeB-postledger-core-hygiene`, with the B2(d) grouped decorated
      -- envelope coverage — or a minimal Type B overlap obstruction among the
      -- piece's own high centres (`lem:typeB-bridge-to-overlap`).
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ canonicalPiece : Graph.TypeBRefinedSupport.CanonicalPiece object
            packing,
          object.NegativeNetCharge canonicalPiece.vertices data.threshold
            data.dischargeScale →
          0 < object.ambientSurplus canonicalPiece.vertices data.threshold →
          (∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale packing
                canonicalPiece.vertices
                (Graph.TypeBRefinedSupport.centres object data.threshold
                  canonicalPiece.vertices),
            ledger.ExactAugmentedLedgerRefinement ∧
              (¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex) ∧
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
                      component.1 data.LengthOK (handoffHighDegree data object)
                      (handoffAbsorbing data object packing),
                    ∃ grouped :
                      Graph.DecoratedHandoff.GroupedEnvelopes object
                        data.LengthOK (handoffUncompressible data object)
                        (handoffWindowFree data object)
                        (handoffHighDegree data object)
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
                                (production component).separation.separator) ∨
            Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
              data.threshold data.dischargeScale packing
                canonicalPiece.vertices
                (Graph.TypeBRefinedSupport.centres object data.threshold
                  canonicalPiece.vertices)))
  | .typeBSublinearLedger, object =>
      TypeBSublinearHypotheses data object
  | .typeBSublinearResidual, object =>
      ¬ TypeBSublinearHypotheses data object
  | .route8QuotientFree, object =>
      Route8QuotientFreeStatement data object
  | .route8QuotientResidual, object =>
      ¬ Route8QuotientFreeStatement data object
  | .route8DemandLedger, object =>
      Route8DemandLedgerStatement data object
  | .route8ExtractedEntryCensus, object =>
      Route8ExtractedEntryCensusFact data object
  | .typeAPortReturn, object =>
      -- `lem:typeA-port-return`, on the selected saturated Type A support
      -- carried by the literal incoming residual: every completion port of
      -- every receiver of that support carries an anchored return.
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
              (∃ selectedReceiver : object.Vertex,
                object.IsReceiver piece data.threshold selectedReceiver ∧
                  object.Saturated piece data.threshold data.dischargeScale
                    selectedReceiver) ∧
              ∀ receiver : object.Vertex,
                object.IsReceiver piece data.threshold receiver →
                ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                    receiver,
                  Nonempty
                    (Graph.VisibleEntry.AnchoredReturn object receiver outside))
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
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.PeeledByWitnesses
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold data.dischargeScale receiver peeled)
  | .typeAExitSevenProduced, object =>
      -- Node `[107]`, yes: exit `(7)` is produced on the exact selected
      -- no-exit-`(6)` residual.
      SelectedNoExitSixWith data object
        (fun packing piece => HandoffProduced data object packing piece)
  | .typeAExitSevenHandoff, object =>
      -- Node `[108]`: the produced envelope is committed as the Type B
      -- handoff.  Its admissibility is the fact proved at node `[65]`.
      SelectedNoExitSixWith data object
        (fun packing piece => HandoffProduced data object packing piece)
  | .typeBDecoratedAssignedSupport, object =>
      SelectedNoExitSixWith data object
        (fun packing piece =>
          DecoratedTypeBAssignedSupport data object packing piece)
  | .typeAExitSevenFree, object =>
      -- Node `[107]`, no: the same selected residual has no decorated
      -- handoff envelope and therefore enters the route-8 test.
      SelectedNoExitSixWith data object
        (fun packing piece => ¬ HandoffProduced data object packing piece)
  | .highCentreNormalForm, object =>
      -- Node `[67]`: `lem:heavy-neighbourhood-normal-form`, at every high
      -- centre of the object at once.  It is not about one support, so it is
      -- stated of the object and both arms of the split read it.
      (∀ centre : object.Vertex,
        Graph.IsHighCentre object data.threshold centre →
        Graph.NormalForm object data.threshold centre)
  | .fanCertificateCap, object =>
      -- Node `[70]`, `lem:fan-certificate`, on the literal assigned-centre
      -- support entering the node.  The bound is the label algebra's own
      -- packing number at the registered window order, never a numeral: at the
      -- manuscript's order it evaluates to `8`.  It is conditional on the
      -- certificate labelling, exactly as in the manuscript.
      TypeBFanCertificateCapStatement data object
  | .fanCertificateMarked, object =>
      -- Node `[71]`/`[80]`, yes arm, on either common Type B input.  The
      -- indexed absorbed form retains the literal corridor and envelope
      -- witness rather than manufacturing a canonical support.
      TypeBFanCertificateMarkedStatement data object
  | .fanCertificateResidual, object =>
      -- Node `[71]`/`[80]`, no arm, retaining the same literal carrier on
      -- which the missing fan-certificate labelling was observed.
      TypeBFanCertificateResidualStatement data object
  | .typeBHybridEntry, object =>
      -- Node `[74]`/`[82]`.  Scoped to the assigned centres of the Type B fan
      -- support, because `k ≤ α(D)` is available only at a certificate-marked
      -- fan, and quantified over the envelope and the packed-window union
      -- because both are fan data.
      TypeBFanHybridEntryStatement data object
  | .typeBDirectCycle, object =>
      -- Node `[72]`/`[81]`, the closing arm.  On either literal Type B carrier,
      -- an applicable centre carries one of the four direct configurations;
      -- the absorbed lane uses the object's canonical window packing without
      -- manufacturing a canonical remainder component.
      TypeBFanDirectCycleStatement data object
  | .typeBDirectCycleFree, object =>
      -- Node `[72]`/`[81]`, surviving arm, retaining the same canonical or
      -- indexed absorbed carrier read by the direct-cycle decision.
      TypeBFanDirectCycleFreeStatement data object
  | .typeBB2Choice, object =>
      -- Node `[72]`/`[81]`, yes: the B2 disjoint choice at the assigned
      -- centres `H_X` of the literal fan support.  The absorbed lane retains
      -- its actual first-failure support and heavy centre rather than inventing
      -- either a decorated Type A envelope core or a canonical piece.
      TypeBB2ChoiceStatement data object
  | .typeBDisjointLedger, object =>
      (TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
                  data.threshold data.dischargeScale packing
                    canonicalPiece.vertices centres,
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
                          component.1 data.LengthOK (handoffHighDegree data object)
                          (handoffAbsorbing data object packing),
                        ∃ grouped :
                          Graph.DecoratedHandoff.GroupedEnvelopes object
                            data.LengthOK (handoffUncompressible data object)
                            (handoffWindowFree data object)
                            (handoffHighDegree data object)
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
                                    (production component).separation.separator)) ∨
        AbsorbedGermFanB2PaidStatement data object
  | .typeBOverlapObstruction, object =>
      -- Node `[72]`/`[81]`, no.  `lem:typeB-bridge-to-overlap`: the
      -- disjoint-carrier clause fails on some assigned support, and what that
      -- support then carries is a *minimal* Type B overlap obstruction among
      -- its assigned centres.
      TypeBB2ObstructionStatement data object
  | .fanCertificateResidualMass, object =>
      -- Node `[75]`/`[84]`: the residual centre's fan mass is charged to the
      -- bridge mass (`def:typeB-residual-mass`).
      TypeBFanCertificateResidualMassStatement data object
  | .typeBOverlapObstructionMass, object =>
      (TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
                data.threshold data.dischargeScale packing
                  canonicalPiece.vertices centres) ∧
              ∀ centre ∈ centres,
                ∀ envelope : Finset object.Vertex,
                  Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                      data.threshold data.dischargeScale envelope centre ≤
                    data.bridgeMassFactor * data.dischargeScale *
                      (object.degree centre - data.threshold))) ∨
        AbsorbedGermFanB2ObstructionMassStatement data object
  | .typeBExclusionResidualMass, object =>
      TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
          ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale packing
                canonicalPiece.vertices centres,
            ledger.ExactAugmentedLedgerRefinement ∧
              (¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex) ∧
              ∀ centre ∈ centres,
                ∀ envelope : Finset object.Vertex,
                  Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                  data.threshold data.dischargeScale envelope centre ≤
                    data.bridgeMassFactor * data.dischargeScale *
                      (object.degree centre - data.threshold))
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
      -- `prop:typeB-bridge-sublinear` in exact finite form.  `ordinary` is the
      -- canonical assigned-support role and `grouped` is the decorated-envelope
      -- role from `def:typeB-residual-mass`.  Empty route-8 subcollections are
      -- the proposition's hypothesis that the non-window cores contain no
      -- admissible route-8 profile.  The factor `2` is precisely the paper's
      -- at-most-twice convention: a high-centre surplus unit occurs at most once
      -- in each of the two roles.
      ((∀ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing →
          ∀ ordinary grouped : Finset object.Vertex,
            ordinary ⊆ object.remainderSupport packing →
            grouped ⊆ object.remainderSupport packing →
            (∀ piece ∈ object.canonicalPieces ordinary,
              Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
                (object.pieceSupport ordinary piece)
                data.threshold data.dischargeScale) →
            (∀ piece ∈ object.canonicalPieces grouped,
              Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
                (object.pieceSupport grouped piece)
                data.threshold data.dischargeScale) →
            ∑ piece ∈ object.canonicalPieces ordinary,
                ((object.pieceSupport ordinary piece).card +
                    data.dischargeScale * object.ambientSurplus
                      (object.pieceSupport ordinary piece)
                      data.threshold -
                  data.dischargeScale * object.positiveDeficiency
                    (object.pieceSupport ordinary piece) data.threshold) +
              ∑ piece ∈ object.canonicalPieces grouped,
                ((object.pieceSupport grouped piece).card +
                    data.dischargeScale * object.ambientSurplus
                      (object.pieceSupport grouped piece) data.threshold -
                  data.dischargeScale * object.positiveDeficiency
                    (object.pieceSupport grouped piece) data.threshold) ≤
                2 * (data.bridgeMassFactor * data.dischargeScale *
                  object.degreeSurplus data.threshold)) ∧
        object.degreeSurplus data.threshold ≤
          data.surplusThreshold object.vertexCount)
  | .typeBExcluded, object =>
      -- Nodes `[74]`/`[82]`, the successful B2 reduction.  A canonical
      -- assigned support publishes the paper's literal `N₀(X) ≥ 0`.
      -- The indexed `[177]` lane publishes its literal paid B2 entry: that
      -- lane has no canonical negative remainder support and must not be
      -- relabelled as the B2-failure residual of `[84]`.
      (TypeBAssignedLedgerWith data object
          (fun _packing canonicalPiece _centres =>
            object.NonNegativeNetCharge canonicalPiece.vertices data.threshold
              data.dischargeScale)) ∨
        AbsorbedGermFanB2PaidStatement data object
  | .typeBExclusionResidual, object =>
      TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
                  data.threshold data.dischargeScale packing
                    canonicalPiece.vertices centres,
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
                      vertex)
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
                  ∃ peeled : Finset object.Vertex,
                    peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.PeeledByWitnesses
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold data.dischargeScale receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledLoads piece
                            data.threshold receiver peeled ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            object.routedLoads piece data.threshold receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver peeled)
  | .typeAExitFourFiniteDescent, object =>
      -- `lem:typeA-exit4-finite-descent`: the finite descent principle at the
      -- exact selected receiver and current peeling set (the terminal
      -- predicates are instantiated by the rows that use it, node `[123]`).
      TypeAExitFourFiniteDescentFact data object
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
                      Graph.ExitFour.PeeledByWitnesses
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold data.dischargeScale receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold data.dischargeScale receiver peeled,
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
                            data.threshold data.dischargeScale receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold data.dischargeScale receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)))
  | .typeAExitFourReceiverDischarged, object =>
      -- Node `[102]` → `[89]`, the retest after the exit-`(4)` descent
      -- (`lem:typeA-exit4-finite-descent`, `lem:typeA-exit4-peeling-charge`):
      -- the peeling set reached by charging exit-`(4)` witnesses leaves the
      -- selected receiver unsaturated at the peeled residual, i.e. its
      -- remaining receiver charge `q(w) − ¼ − ¼·L₄(w)` is nonnegative in the
      -- cleared scale.  The peeled loads are the receiver's target-defect
      -- entries for the pressure ledger.
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
                      Graph.ExitFour.PeeledByWitnesses
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                          data.dischargeScale receiver peeled ∧
                      1 + Graph.ExitFour.residualLoad piece data.threshold
                          receiver peeled ≤
                        data.dischargeScale *
                          object.missingPorts piece data.threshold receiver)
  | .typeAExitFive, object =>
      -- Node `[103]`, yes: one load in the exact visible/silent post-exit-`(4)`
      -- residual has a selected trace basin whose declared `u`-supported
      -- response algebra admits alternative (b), including the paper's
      -- proper-realization / trace-response-only split.
      let exitFiveAt := fun (piece : Finset object.Vertex)
          (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
        ∃ load : object.Vertex,
          (((∃ package :
                Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                  data.dischargeScale receiver peeled,
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver package.outside
                    peeled,
                  witness.load = selected) ∧
                load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled) ∨
            (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                data.dischargeScale receiver peeled ∧
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                  data.dischargeScale receiver peeled) ∧
              load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled)) ∧
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
                  piece data.threshold data.LengthOK receiver load basin)
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
                      exitFiveAt piece receiver peeled)
  | .typeAExitFiveFree, object =>
      -- Node `[103]`, no: the same exact post-exit-`(4)` residual is retained,
      -- and none of its eligible loads has alternative (b) at its selected
      -- trace basin.
      let exitFiveAt := fun (piece : Finset object.Vertex)
          (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
        ∃ load : object.Vertex,
          (((∃ package :
                Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                  data.dischargeScale receiver peeled,
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver package.outside
                    peeled,
                  witness.load = selected) ∧
                load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled) ∨
            (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                data.dischargeScale receiver peeled ∧
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                  data.dischargeScale receiver peeled) ∧
              load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled)) ∧
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
                  piece data.threshold data.LengthOK receiver load basin)
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
                            data.threshold data.dischargeScale receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold data.dischargeScale receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ¬ exitFiveAt piece receiver peeled)
  | .typeAExitSix, object =>
      -- Node `[105]`, yes: the selected saturated handoff state, after exits
      -- `(4)` and `(5)` have failed, carries an equality of declared response
      -- coordinates that becomes target-complete only after adjoining a larger
      -- connected support.  The witness is tied to the incoming residual; it is
      -- not an arbitrary route-8 object.
      let exitFiveAt := fun (piece : Finset object.Vertex)
          (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
        ∃ load : object.Vertex,
          (((∃ package :
                Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                  data.dischargeScale receiver peeled,
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver package.outside
                    peeled,
                  witness.load = selected) ∧
                load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled) ∨
            (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                data.dischargeScale receiver peeled ∧
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                  data.dischargeScale receiver peeled) ∧
              load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled)) ∧
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
                  piece data.threshold data.LengthOK receiver load basin)
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
                            data.threshold data.dischargeScale receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold data.dischargeScale receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ exitFiveAt piece receiver peeled ∧
                        ExitSixDelocalizes data object piece receiver peeled))
  | .typeAExitSixFree, object =>
      -- Node `[105]`, no: the same selected saturated handoff state has no
      -- exit-`(6)` delocalization witness.
      let exitFiveAt := fun (piece : Finset object.Vertex)
          (receiver : object.Vertex) (peeled : Finset object.Vertex) =>
        ∃ load : object.Vertex,
          (((∃ package :
                Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                  data.dischargeScale receiver peeled,
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver package.outside
                    peeled,
                  witness.load = selected) ∧
                load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled) ∨
            (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                data.dischargeScale receiver peeled ∧
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                  data.dischargeScale receiver peeled) ∧
              load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled)) ∧
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
                  piece data.threshold data.LengthOK receiver load basin)
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
                            data.threshold data.dischargeScale receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold data.dischargeScale receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ exitFiveAt piece receiver peeled ∧
                        ¬ ExitSixDelocalizes data object piece receiver peeled))
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
  | .route8ResidualProfile, object =>
      -- Node `[110]`: the selected route-8 residual satisfies the
      -- silent-core residual profile, without creating a secondary carrier.
      SilentCoreResidualProfile data object
  | .route8GlobalSqueeze, object =>
      -- Node `[111]`: the exact route-8 Type A collection and the cleared
      -- defining sum for `D_A` on the selected residual packing.
      Route8GlobalSqueeze data object
  | .route8BasinBurden, object =>
      -- Node `[112]`: the selected route-8 residual carries the basin-burden
      -- lower side of `lem:typeA-route8-burden`.
      Route8BasinBurden data object
  | .route8LargeBudgetDeficit, object =>
      -- Node `[113]`: the exact cleared lower bound on `D_A(𝒳_A)` for the
      -- selected route-8 collection.
      Route8LargeBudgetDeficit data object
  | .route8LargeBudgetDeficitFails, object =>
      -- The corrected manuscript's unified-demand arm: the route-8-only
      -- collection does not carry the displayed lower bound, so node `[123]`
      -- must retain the target-defect entries and peel them.
      ¬ Route8LargeBudgetDeficit data object
  | .route8CarrierCore, object =>
      -- Node `[114]`: the canonical minimal carrier-core theorem package,
      -- available on the selected route-8 residual.
      Route8CarrierCore data object
  | .route8TrueResidual, object =>
      -- Node `[114]`, `def:typeA-true-route8-residual`: clauses (R1)--(R4)
      -- for every actual indexed entry of the selected route-8 collection.
      Route8TrueResidual data object
  | .route8CarrierCutParity, object =>
      -- Node `[114]`, `lem:typeA-carrier-cut-parity`: the exact conditional
      -- cut-parity statement on every surviving mixed event.
      Route8CarrierCutParity data object
  | .route8SmallCoreEntry, object =>
      -- Node `[115]`, yes arm: the selected route-8 collection contains a
      -- literal indexed entry with `alpha ≤ 1`.
      Route8SmallCoreEntry data object
  | .route8NoSmallCoreEntry, object =>
      -- Node `[115]`, no arm: all literal indexed entries have `alpha ≥ 2`.
      Route8NoSmallCoreEntry data object
  | .route8SmallCoreCollapse, object =>
      -- Node `[116]`: the selected small entry realizes an exact exit
      -- `(4)`--`(7)` trace-basin alternative.
      Route8SmallCoreCollapse data object
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
  | .route8TerminalNoGo, object =>
      -- Node `[124]`: terminal two-carrier route-8 no-go through Q5
      -- carrier-deletion and the committed no-exit-(4) fact.
      Route8TerminalNoGo data object
  | .route8Census, object =>
      -- The two census readings, with the carrier convention of
      -- `def:typeA-terminal-two-carrier`: a two-carrier entry has at most
      -- `δ − 1` (the manuscript's two) private essential carriers, so the
      -- no-two-carrier bound is `δ` per entry and the rate is `τ < δ/(δs+1)`.
      let packing := canonicalWindowPacking data object
      let support := object.remainderSupport packing
      let routeEight : Finset
          (Graph.SupportComponents.Connected.Component object support) := by
        classical
        exact (object.canonicalPieces support).filter
          (Route8Survives data object packing)
      Graph.Route8Census.CollectionDeficit object packing routeEight
          data.threshold data.dischargeScale
          (data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount) ∧
        Graph.Route8Census.Rate object packing data.threshold data.dischargeScale
          (data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount)
  | .route8Deficit, object =>
      Graph.Route8Census.Deficit object (canonicalWindowPacking data object)
        data.threshold data.dischargeScale
        (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount)
  | .route8Rate, object =>
      Graph.Route8Census.Rate object (canonicalWindowPacking data object)
        data.threshold data.dischargeScale
        (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount)
  | .route8RateFails, object =>
      ¬ Graph.Route8Census.Rate object (canonicalWindowPacking data object)
        data.threshold data.dischargeScale
        (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount)
  | .route8PiecesClassified, object =>
      -- `thm:branch-kill`'s all-pieces classification, exactly as stated: at a
      -- negative zero-surplus piece, an exit-(4) witness for a routed load,
      -- the route-8 residual profile — per saturated receiver, every unpaid
      -- silent-excess and overloaded-port visible load is a route-8 entry or
      -- realizes the exit-(5) plain response quotient (cased), the exact
      -- per-load conclusion `K .typeAExclusion`'s arm 2 delivers
      -- (`lem:typeA-reduced-silent-residual`, `rem:unified-covers-exit4`) —
      -- or a produced decorated Type B handoff; at a negative positive-surplus
      -- piece, the Type B bridge component pair.
      Graph.Route8Deficit.PieceClassification object
        (Graph.HasCycleWithLength data.LengthOK)
        (fun piece =>
          ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
              data.threshold data.dischargeScale,
            (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
                data.threshold data.dischargeScale receiver,
              Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
                  data.LengthOK receiver load ∨
                ∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.select? object piece data.threshold
                      receiver load = some basin ∧
                    ∃ retained,
                      Graph.Route8.TraceBasin.TraceResponseQuotient object
                        piece data.threshold data.LengthOK receiver load basin
                        retained) ∧
              ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                  receiver,
                data.dischargeScale ≤
                  (Graph.VisibleEntry.visibleLoadsAt object piece
                    data.threshold receiver outside).card →
                ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver outside ∅,
                  Graph.Route8.TraceBasin.Route8Entry object piece
                      data.threshold data.LengthOK receiver load ∨
                    ∃ basin : Finset object.Vertex,
                      Graph.Route8.TraceBasin.select? object piece
                          data.threshold receiver load = some basin ∧
                        ∃ retained,
                          Graph.Route8.TraceBasin.TraceResponseQuotient object
                            piece data.threshold data.LengthOK receiver load
                            basin retained)
        (fun piece =>
          HandoffProduced data object (canonicalWindowPacking data object) piece)
        (fun piece =>
          -- `def:typeB-bridge-statements` at the piece: the B2 disjoint ledger
          -- with strictly negative remaining scaled core charge, or a minimal
          -- overlap obstruction (`K .typeBBridgeReduction`'s dichotomy; the
          -- post-ledger hygiene and grouped coverage stay on that key and are
          -- not republished here).
          (∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale
              (canonicalWindowPacking data object) piece
              (Graph.TypeBRefinedSupport.centres object data.threshold piece),
            ledger.ExactAugmentedLedgerRefinement ∧
              ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale piece vertex) ∨
            Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
              data.threshold data.dischargeScale
              (canonicalWindowPacking data object) piece
              (Graph.TypeBRefinedSupport.centres object data.threshold piece)))
        (canonicalWindowPacking data object) data.threshold data.dischargeScale
  | .route8UnifiedNegative, object =>
      -- `def:typeA-unified-negative`: only the exact canonical collection and
      -- its cleared defining sum; all quantitative and entry facts are later.
      Route8UnifiedNegative data object
  | .route8UnifiedDeficit, object =>
      Route8UnifiedDeficitFact data object
  | .route8UnifiedEntryCensus, object =>
      Route8UnifiedEntryCensusFact data object
  | .route8StageRateFailed, object =>
      Route8StageRateFailedFact data object
  | .route8DemandAbsorption, object =>
      Route8DemandAbsorptionStatement data object
  | .route8WindowBlockers, object =>
      Route8WindowBlockersStatement data object
  | .route8PeeledDemandResidual, object =>
      Route8PeeledDemandResidualStatement data object
  | .route8TwoCarrierEntry, object =>
      let packing := canonicalWindowPacking data object
      let support := object.remainderSupport packing
      let routeEight : Finset
          (Graph.SupportComponents.Connected.Component object support) := by
        classical
        exact (object.canonicalPieces support).filter
          (Route8Survives data object packing)
      ∃ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
          data.threshold data.dischargeScale,
        Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
          data.threshold data.dischargeScale data.LengthOK index
  | .route8NoTwoCarrierEntry, object =>
      let packing := canonicalWindowPacking data object
      let support := object.remainderSupport packing
      let routeEight : Finset
          (Graph.SupportComponents.Connected.Component object support) := by
        classical
        exact (object.canonicalPieces support).filter
          (Route8Survives data object packing)
      ∀ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
          data.threshold data.dischargeScale,
        ¬ Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
          data.threshold data.dischargeScale data.LengthOK index
  | .route8TrueTwoCarrierEntry, object =>
      -- `def:typeA-true-route8-residual` at the selected two-carrier entry: no
      -- exit-`(4)` witness for its load at its receiver (`Graph.ExitFour.Witness`
      -- with the empty peeling: the load is a routed load of the receiver).
      let packing := canonicalWindowPacking data object
      let support := object.remainderSupport packing
      let routeEight : Finset
          (Graph.SupportComponents.Connected.Component object support) := by
        classical
        exact (object.canonicalPieces support).filter
          (Route8Survives data object packing)
      ∃ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
          data.threshold data.dischargeScale,
        Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
          data.threshold data.dischargeScale data.LengthOK index ∧
        ¬ ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
            index.1 data.threshold data.dischargeScale index.2.1 ∅,
          witness.load = index.2.2
  | .route8VisibleExitFourRouting, object =>
      -- `lem:typeA-unpeeled-visible-routing` at the unified collection,
      -- discharged through the standing invariants and
      -- `rem:unified-covers-exit4`: an overloaded completion port among the
      -- unpeeled loads realizes the exit list, with exits `(1)`--`(3)` and
      -- `(6)` closed by the standing invariants and exit `(7)` excluded by
      -- the collection's own no-handoff filter.  What remains is exit `(4)` —
      -- a witness at the current peeling whose load is one of the port's
      -- visible unpeeled loads — or, per selected visible unpeeled load, the
      -- trace-basin outcome of `lem:typeA-reduced-silent-residual`: a route-8
      -- entry, or the exit-`(5)` response quotient at the selected basin
      -- (cased on the branch, never refuted from the invariants).
      letI : DecidableEq object.Vertex := object.vertices.decEq
      (∀ component ∈ route8UnifiedComponents data object,
        ∀ receiver ∈ object.receivers
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component)
            data.threshold,
          ∀ peeled : Finset object.Vertex,
            peeled ⊆ object.routedLoads
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component)
              data.threshold receiver →
            ∀ outside ∈ Graph.VisibleEntry.completionPorts object
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component)
                receiver,
              data.dischargeScale ≤
                ((Graph.VisibleEntry.visibleLoadsAt object
                    (object.pieceSupport
                      (object.remainderSupport
                        (canonicalWindowPacking data object))
                      component)
                    data.threshold receiver outside) \ peeled).card →
              (∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK)
                  (object.pieceSupport
                    (object.remainderSupport (canonicalWindowPacking data object))
                    component)
                  data.threshold data.dischargeScale receiver peeled,
                witness.load ∈
                  (Graph.VisibleEntry.visibleLoadsAt object
                    (object.pieceSupport
                      (object.remainderSupport
                        (canonicalWindowPacking data object))
                      component)
                    data.threshold receiver outside) \ peeled) ∨
                ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                    (object.pieceSupport
                      (object.remainderSupport
                        (canonicalWindowPacking data object))
                      component)
                    data.threshold data.dischargeScale receiver outside peeled,
                  Graph.Route8.TraceBasin.Route8Entry object
                      (object.pieceSupport
                        (object.remainderSupport
                          (canonicalWindowPacking data object))
                        component)
                      data.threshold data.LengthOK receiver load ∨
                    ∃ basin : Finset object.Vertex,
                      Graph.Route8.TraceBasin.select? object
                          (object.pieceSupport
                            (object.remainderSupport
                              (canonicalWindowPacking data object))
                            component)
                          data.threshold receiver load = some basin ∧
                        ∃ retained,
                          Graph.Route8.TraceBasin.TraceResponseQuotient object
                            (object.pieceSupport
                              (object.remainderSupport
                                (canonicalWindowPacking data object))
                              component)
                            data.threshold data.LengthOK receiver load basin
                            retained)
  | .route8PeelingDescent, object =>
      -- `thm:large-budget-route8-only`'s procedure at the fixed maximal packing,
      -- with the two-role Type B allowance `2·F·s·T(n)`.
      let entries := route8UnifiedEntries data object
      let bridgeSlack := 2 * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount)
      ∃ final : List (Graph.Route8Census.Index object),
        Graph.Route8Pressure.StageOutcome object (canonicalWindowPacking data object)
          entries (route8UnifiedComponents data object) data.threshold
          data.dischargeScale bridgeSlack data.LengthOK final
  | .route8UnifiedTrueTwoCarrierEntry, object =>
      letI : DecidableEq object.Vertex := object.vertices.decEq
      let entries := route8UnifiedEntries data object
      ∃ index ∈ entries,
        Graph.Route8.IndexedTwoCarrierCore entries
            (Graph.Route8Census.core object data.threshold data.LengthOK)
            (data.threshold - 1) index ∧
          let basin := Graph.Route8Census.basin object data.threshold index
          Graph.Route8.TraceBasin.select? object index.1 data.threshold
              index.2.1 index.2.2 = some basin ∧
            Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1
              data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
            2 ≤ ((Graph.Route8Census.presented object data.threshold data.LengthOK
              index).toEntry (Graph.HasCycleWithLength data.LengthOK)).alpha ∧
          ¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold data.dischargeScale
              index.2.1 ∅,
            witness.load = index.2.2
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
          let recorded := Graph.recordSparsePairDEBlockers
            (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
            (LengthOK := data.LengthOK) activation pairs
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
      -- Node `[130]`, no: the circuit extraction starts with a functional
      -- attempted determination which is rank-reducing on `ℛ_Π`.  It is
      -- deliberately not upgraded to `DeclaredQuotient` here: node `[132]`
      -- must still test the degree-profile and context-completeness clauses of
      -- `def:admissible-rank-quotient`.
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
            attempt.toRankQuotient.FunctionalOn ↑family ∧
              ¬ Set.InjOn attempt.label ↑family
  | .independentPairFamily, object =>
      -- Node `[130]`, yes: no functional attempted determination reduces
      -- `ℛ_Π`.  This is the literal complement of the no-arm above.
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
          attempt.toRankQuotient.FunctionalOn ↑family →
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
          -- `lem:mixed-sparse-spine-dependence`: the union does not survive the
          -- admissible quotient system — some functional admissible rank
          -- quotient of the mixed family is rank-reducing.
          (¬ ∀ declared : Graph.DeclaredQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              mixedFamily mixedSupport,
              declared.toRankQuotient.FunctionalOn ↑mixedFamily →
                Set.InjOn declared.label ↑mixedFamily) →
            Graph.SparseSurplusExit
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object ∨
              ∃ pair ∈ pairs,
                ∃ attempt : Graph.AttemptedQuotient
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) object
                    mixedFamily mixedSupport,
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
      -- The one concrete activation/carrier/packing presentation constructed
      -- at `[136]`, together with every accounting identity proved there.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
          data.windowOrder,
        capacity.activation =
            (Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK)
              (Graph.pairResponseActivation active)
              (object.portPairSchedule data.threshold)) ∧
          (object.primitiveCarrier data.threshold).card =
            object.vertexCount + 2 * object.edgeCount +
              object.degreeSurplus data.threshold ∧
          (object.primitiveCarrier data.threshold).card ≤
            object.primitiveCarrierSupply data.threshold ∧
          Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement object
            data.threshold data.windowOrder capacity.activation capacity.carrier
            capacity.packing ∧
          Graph.SupportComponents.Connected.ConnectedOn object
            object.vertexFinset
  | .roleFibrePartition, object =>
      -- `lem:exact-surplus-pair-charge-partition` with the classwise and
      -- subtype budgets, at the object's own capacity-token ledger.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.RoleFibrePartitionStatement object data.threshold
              data.windowOrder data.surplusScale capacity
  | .fibrePressure, object =>
      -- `lem:capacity-token-high-load` with
      -- `cor:forced-homogeneous-same-token-scale` and the two sharp budgets,
      -- existential in the object's own capacity-token ledger at every declared
      -- presentation.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.FibrePressureStatement object data.threshold data.windowOrder
              data.surplusScale capacity
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
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.SparsePressureOverloadStatement object data.threshold
              data.windowOrder data.routingLabelBound capacity
  | .freePairEntropySandwich, object =>
      FreePairEntropySandwichStatement data object
  | .freePairCodeUnrealized, object =>
      FreePairCodeUnrealizedStatement data object
  | .blockedPairEntropySandwich, object =>
      BlockedPairEntropySandwichStatement data object
  | .blockedPairCodeUnrealized, object =>
      BlockedPairCodeUnrealizedStatement data object
  | .windowClassOverload, object =>
      -- Node `[139]`, yes: the overload occurs at a window-incidence token.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.SparsePressureOverloadInClass object data.threshold
              data.windowOrder data.routingLabelBound capacity .windowIncidence
  | .windowClassAbsent, object =>
      -- Node `[139]`, no.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.SparsePressureOverloadOutsideClass object data.threshold
              data.windowOrder data.routingLabelBound capacity .windowIncidence
  | .remainderClassOverload, object =>
      -- Node `[141]`, yes: the overload occurs at a remainder-surplus token.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.SparsePressureOverloadInClass object data.threshold
              data.windowOrder data.routingLabelBound capacity .remainderSurplus
  | .remainderClassAbsent, object =>
      -- Node `[141]`, no: after the inherited non-window residual, the same
      -- selected overload token is necessarily primitive.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.SparsePressureOverloadInClass object data.threshold
              data.windowOrder data.routingLabelBound capacity .primitiveCarrier
  | .windowIncidenceAudit, object =>
      -- Node `[140]`: the actual `L_geom` pattern forced by the selected
      -- window-incidence overload witness.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.HomogeneousBottleneckPatternStatement object data.threshold
              data.windowOrder capacity
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder))
  | .remainderSurplusAudit, object =>
      -- Node `[142]`: the actual `L_geom` pattern forced by the selected
      -- remainder-surplus overload witness.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.HomogeneousBottleneckPatternStatement object data.threshold
              data.windowOrder capacity
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder))
  | .primitiveCarrierAudit, object =>
      -- Node `[143]`: the actual `L_geom` pattern forced by the selected
      -- primitive-carrier overload witness.
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.HomogeneousBottleneckPatternStatement object data.threshold
              data.windowOrder capacity
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder))
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
      ∃ active : Graph.ActiveSurplusDemands
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
          data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
              (Graph.recordSparsePairDEBlockers
                (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                (LengthOK := data.LengthOK)
                (Graph.pairResponseActivation active)
                (object.portPairSchedule data.threshold)) ∧
            Graph.HomogeneousBottleneckPatternStatement object data.threshold
              data.windowOrder capacity
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder))
  | .bottleneckRouting, object =>
      -- `lem:same-token-bottleneck-routing`, on the actual active family and
      -- capacity presentation.  No caller-supplied route, separator, reading,
      -- profile map, or callback is part of the proposition.
      ∃ active : Graph.ActiveSurplusDemands
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
            data.threshold,
        ∃ capacity : Graph.CapacityPresentation object data.threshold
            data.windowOrder,
          capacity.activation =
            (Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK)
              (Graph.pairResponseActivation active)
              (object.portPairSchedule data.threshold)) ∧
          Graph.HomogeneousBottleneckPatternStatement object data.threshold
              data.windowOrder capacity
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder)) ∧
          (Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object ∨
              SameTokenTypeBHandoffStatement data object)
  | .typeBHandoff, object =>
      -- The direct Type B handoff on the survivor branch, with exactly the
      -- core/envelope clauses proved at `[144]` and no imported Type-A state.
      SameTokenTypeBHandoffStatement data object
  | .homogeneousBottleneck, object =>
      -- `cor:homogeneous-same-token-caps-close` at the counted `L_geom`, with
      -- `thm:homogeneous-overload-geometric-closure`'s edge-count half.
      Graph.HomogeneousCapsCloseStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))
  | .sparseSurplusSurvivor, object =>
      -- `def:named-surplus-exits`: none of the five sparse-surplus conclusions
      -- occurs on this branch.
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
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
  | .cubicBaseline => "cubicBaseline"
  | .returnAvoidance => "returnAvoidance"
  | .noProperBaseline => "noProperBaseline"
  | .tightEndpoint => "tightEndpoint"
  | .slackIndependent => "slackIndependent"
  | .degreeProfileFibres => "degreeProfileFibres"
  | .targetCompleteContextUniversality => "targetCompleteContextUniversality"
  | .replacementExclusion => "replacementExclusion"
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
  | .exactResponseProfile => "exactResponseProfile"
  | .admissibleRankQuotient => "admissibleRankQuotient"
  | .curvatureTargetRank => "curvatureTargetRank"
  | .targetRankCircuit => "targetRankCircuit"
  | .curvatureRankDrop => "curvatureRankDrop"
  | .curvatureFullRank => "curvatureFullRank"
  | .branchDependence => "branchDependence"
  | .separatedTesters => "separatedTesters"
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
  | .typeBFanLocalDichotomy => "typeBFanLocalDichotomy"
  | .typeBFanDegreeFourProfile => "typeBFanDegreeFourProfile"
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
  | .coldFailureDefect => "coldFailureDefect"
  | .coldFailureCompression => "coldFailureCompression"
  | .coldFailureHandoff => "coldFailureHandoff"
  | .coldFailureRouting => "coldFailureRouting"
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
  | .densePackingOverflow => "densePackingOverflow"
  | .denseDeficiencyBelow => "denseDeficiencyBelow"
  | .denseDeficiencyAtOrAbove => "denseDeficiencyAtOrAbove"
  | .coldWindowStubStructure => "coldWindowStubStructure"
  | .coldCanonicalNeutralConfiguration => "coldCanonicalNeutralConfiguration"
  | .coldGenuineSecondStrand => "coldGenuineSecondStrand"
  | .coldCanonicalSwapSmaller => "coldCanonicalSwapSmaller"
  | .coldCanonicalSwapSameSize => "coldCanonicalSwapSameSize"
  | .blockedClassMember => "blockedClassMember"
  | .blockedScaleAdditive => "blockedScaleAdditive"
  | .blockedBarrierOverlap => "blockedBarrierOverlap"
  | .absorbedGermFanData => "absorbedGermFanData"
  | .absorbedGermSplit => "absorbedGermSplit"
  | .coldFamilyPositive => "coldFamilyPositive"
  | .coldFamilyEmpty => "coldFamilyEmpty"
  | .coldGermCandidates => "coldGermCandidates"
  | .coldSelectedBranchExcess => "coldSelectedBranchExcess"
  | .coldAmbientCubicStubExcess => "coldAmbientCubicStubExcess"
  | .coldHandoffTransfer => "coldHandoffTransfer"
  | .coldGermExtraction => "coldGermExtraction"
  | .coldPositiveGerm => "coldPositiveGerm"
  | .coldGermRouted => "coldGermRouted"
  | .coldBranchClosed => "coldBranchClosed"
  | .highCentreNormalForm => "highCentreNormalForm"
  | .fanCertificateCap => "fanCertificateCap"
  | .fanCertificateMarked => "fanCertificateMarked"
  | .fanCertificateResidual => "fanCertificateResidual"
  | .typeBHybridEntry => "typeBHybridEntry"
  | .typeBDirectCycle => "typeBDirectCycle"
  | .typeBDirectCycleFree => "typeBDirectCycleFree"
  | .typeBB2Choice => "typeBB2Choice"
  | .typeBDisjointLedger => "typeBDisjointLedger"
  | .typeBOverlapObstruction => "typeBOverlapObstruction"
  | .fanCertificateResidualMass => "fanCertificateResidualMass"
  | .typeBOverlapObstructionMass => "typeBOverlapObstructionMass"
  | .typeBExclusionResidualMass => "typeBExclusionResidualMass"
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
  | .typeAExitSevenProduced => "typeAExitSevenProduced"
  | .route8ResidualProfile => "route8ResidualProfile"
  | .route8GlobalSqueeze => "route8GlobalSqueeze"
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
  | .route8NoTwoCarrierContradiction => "route8NoTwoCarrierContradiction"
  | .route8TerminalNoGo => "route8TerminalNoGo"
  | .route8Census => "route8Census"
  | .route8Deficit => "route8Deficit"
  | .route8Rate => "route8Rate"
  | .route8RateFails => "route8RateFails"
  | .route8PiecesClassified => "route8PiecesClassified"
  | .route8UnifiedNegative => "route8UnifiedNegative"
  | .route8UnifiedDeficit => "route8UnifiedDeficit"
  | .route8UnifiedEntryCensus => "route8UnifiedEntryCensus"
  | .route8StageRateFailed => "route8StageRateFailed"
  | .route8DemandAbsorption => "route8DemandAbsorption"
  | .route8WindowBlockers => "route8WindowBlockers"
  | .route8PeeledDemandResidual => "route8PeeledDemandResidual"
  | .route8TwoCarrierEntry => "route8TwoCarrierEntry"
  | .route8NoTwoCarrierEntry => "route8NoTwoCarrierEntry"
  | .route8TrueTwoCarrierEntry => "route8TrueTwoCarrierEntry"
  | .route8PeelingDescent => "route8PeelingDescent"
  | .route8VisibleExitFourRouting => "route8VisibleExitFourRouting"
  | .route8UnifiedTrueTwoCarrierEntry => "route8UnifiedTrueTwoCarrierEntry"
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
  | .freePairEntropySandwich => "freePairEntropySandwich"
  | .freePairCodeUnrealized => "freePairCodeUnrealized"
  | .blockedPairEntropySandwich => "blockedPairEntropySandwich"
  | .blockedPairCodeUnrealized => "blockedPairCodeUnrealized"
  | .windowClassOverload => "windowClassOverload"
  | .windowClassAbsent => "windowClassAbsent"
  | .remainderClassOverload => "remainderClassOverload"
  | .remainderClassAbsent => "remainderClassAbsent"
  | .windowIncidenceAudit => "windowIncidenceAudit"
  | .remainderSurplusAudit => "remainderSurplusAudit"
  | .primitiveCarrierAudit => "primitiveCarrierAudit"
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
example : label .degreeProfileFibres = "degreeProfileFibres" := rfl
example : label .targetCompleteContextUniversality =
    "targetCompleteContextUniversality" := rfl
example : label .replacementExclusion = "replacementExclusion" := rfl
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
example : label .curvatureTargetRank = "curvatureTargetRank" := rfl
example : label .targetRankCircuit = "targetRankCircuit" := rfl
example : label .curvatureRankDrop = "curvatureRankDrop" := rfl
example : label .curvatureFullRank = "curvatureFullRank" := rfl
example : label .branchDependence = "branchDependence" := rfl
example : label .separatedTesters = "separatedTesters" := rfl
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
example : label .typeBFanLocalDichotomy = "typeBFanLocalDichotomy" := rfl
example : label .typeBFanDegreeFourProfile = "typeBFanDegreeFourProfile" := rfl
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
example : label .coldFailureDefect = "coldFailureDefect" := rfl
example : label .coldFailureCompression = "coldFailureCompression" := rfl
example : label .coldFailureHandoff = "coldFailureHandoff" := rfl
example : label .coldFailureRouting = "coldFailureRouting" := rfl
example : label .coldExchangeBound = "coldExchangeBound" := rfl
example : label .coldMassLinear = "coldMassLinear" := rfl
example : label .coldMassBounded = "coldMassBounded" := rfl
example : label .bridgeless = "bridgeless" := rfl
example : label .coldReturnCorridors = "coldReturnCorridors" := rfl
example : label .windowPackageRealized = "windowPackageRealized" := rfl
example : label .windowPackageUnrealized = "windowPackageUnrealized" := rfl
example : label .densePackingOverflow = "densePackingOverflow" := rfl
example : label .denseDeficiencyBelow = "denseDeficiencyBelow" := rfl
example : label .denseDeficiencyAtOrAbove = "denseDeficiencyAtOrAbove" := rfl
example : label .coldWindowStubStructure = "coldWindowStubStructure" := rfl
example : label .coldCanonicalNeutralConfiguration = "coldCanonicalNeutralConfiguration" := rfl
example : label .coldGenuineSecondStrand = "coldGenuineSecondStrand" := rfl
example : label .coldCanonicalSwapSmaller = "coldCanonicalSwapSmaller" := rfl
example : label .coldCanonicalSwapSameSize = "coldCanonicalSwapSameSize" := rfl
example : label .blockedClassMember = "blockedClassMember" := rfl
example : label .blockedScaleAdditive = "blockedScaleAdditive" := rfl
example : label .blockedBarrierOverlap = "blockedBarrierOverlap" := rfl
example : label .coldHandoffTransfer = "coldHandoffTransfer" := rfl
example : label .coldGermExtraction = "coldGermExtraction" := rfl
example : label .coldPositiveGerm = "coldPositiveGerm" := rfl
example : label .coldGermRouted = "coldGermRouted" := rfl
example : label .coldBranchClosed = "coldBranchClosed" := rfl
example : label .highCentreNormalForm = "highCentreNormalForm" := rfl
example : label .fanCertificateCap = "fanCertificateCap" := rfl
example : label .fanCertificateMarked = "fanCertificateMarked" := rfl
example : label .fanCertificateResidual = "fanCertificateResidual" := rfl
example : label .typeBHybridEntry = "typeBHybridEntry" := rfl
example : label .typeBDirectCycle = "typeBDirectCycle" := rfl
example : label .typeBDirectCycleFree = "typeBDirectCycleFree" := rfl
example : label .typeBB2Choice = "typeBB2Choice" := rfl
example : label .typeBDisjointLedger = "typeBDisjointLedger" := rfl
example : label .typeBOverlapObstruction = "typeBOverlapObstruction" := rfl
example : label .fanCertificateResidualMass = "fanCertificateResidualMass" := rfl
example : label .typeBOverlapObstructionMass = "typeBOverlapObstructionMass" := rfl
example : label .typeBExclusionResidualMass = "typeBExclusionResidualMass" := rfl
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
example : label .typeAExitSevenProduced = "typeAExitSevenProduced" := rfl
example : label .route8ResidualProfile = "route8ResidualProfile" := rfl
example : label .route8GlobalSqueeze = "route8GlobalSqueeze" := rfl
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
example : label .route8NoTwoCarrierContradiction =
    "route8NoTwoCarrierContradiction" := rfl
example : label .route8TerminalNoGo =
    "route8TerminalNoGo" := rfl
example : label .route8Census = "route8Census" := rfl
example : label .route8Deficit = "route8Deficit" := rfl
example : label .route8Rate = "route8Rate" := rfl
example : label .route8RateFails = "route8RateFails" := rfl
example : label .route8PiecesClassified = "route8PiecesClassified" := rfl
example : label .route8UnifiedNegative = "route8UnifiedNegative" := rfl
example : label .route8UnifiedDeficit = "route8UnifiedDeficit" := rfl
example : label .route8UnifiedEntryCensus = "route8UnifiedEntryCensus" := rfl
example : label .route8StageRateFailed = "route8StageRateFailed" := rfl
example : label .route8DemandAbsorption = "route8DemandAbsorption" := rfl
example : label .route8WindowBlockers = "route8WindowBlockers" := rfl
example : label .route8PeeledDemandResidual =
    "route8PeeledDemandResidual" := rfl
example : label .route8TwoCarrierEntry = "route8TwoCarrierEntry" := rfl
example : label .route8NoTwoCarrierEntry = "route8NoTwoCarrierEntry" := rfl
example : label .route8TrueTwoCarrierEntry = "route8TrueTwoCarrierEntry" := rfl
example : label .route8PeelingDescent = "route8PeelingDescent" := rfl
example : label .route8VisibleExitFourRouting =
    "route8VisibleExitFourRouting" := rfl
example : label .route8UnifiedTrueTwoCarrierEntry =
    "route8UnifiedTrueTwoCarrierEntry" := rfl
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
example : label .freePairEntropySandwich = "freePairEntropySandwich" := rfl
example : label .freePairCodeUnrealized = "freePairCodeUnrealized" := rfl
example : label .blockedPairEntropySandwich = "blockedPairEntropySandwich" := rfl
example : label .blockedPairCodeUnrealized = "blockedPairCodeUnrealized" := rfl
example : label .windowClassOverload = "windowClassOverload" := rfl
example : label .windowClassAbsent = "windowClassAbsent" := rfl
example : label .remainderClassOverload = "remainderClassOverload" := rfl
example : label .remainderClassAbsent = "remainderClassAbsent" := rfl
example : label .windowIncidenceAudit = "windowIncidenceAudit" := rfl
example : label .remainderSurplusAudit = "remainderSurplusAudit" := rfl
example : label .primitiveCarrierAudit = "primitiveCarrierAudit" := rfl
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
  | .cubicBaseline => 221
  | .returnAvoidance => 1
  | .noProperBaseline => 2
  | .tightEndpoint => 3
  | .slackIndependent => 4
  | .degreeProfileFibres => 322
  | .targetCompleteContextUniversality => 323
  | .replacementExclusion => 223
  | .coldMassLinear => 224
  | .coldMassBounded => 225
  | .bridgeless => 226
  | .coldReturnCorridors => 227
  | .windowPackageRealized => 228
  | .windowPackageUnrealized => 229
  | .densePackingOverflow => 337
  | .denseDeficiencyBelow => 230
  | .denseDeficiencyAtOrAbove => 231
  | .coldWindowStubStructure => 232
  | .coldCanonicalNeutralConfiguration => 233
  | .coldGenuineSecondStrand => 234
  | .coldCanonicalSwapSmaller => 244
  | .coldCanonicalSwapSameSize => 245
  | .blockedClassMember => 238
  | .blockedScaleAdditive => 320
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
  | .separatedTesters => 324
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
  | .typeBFanLocalDichotomy => 253
  | .typeBFanDegreeFourProfile => 254
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
  | .coldFailureDefect => 65
  | .coldFailureCompression => 66
  | .coldFailureHandoff => 67
  | .coldFailureRouting => 68
  | .coldExchangeBound => 177
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
  | .coldBranchClosed => 176
  | .highCentreNormalForm => 72
  | .fanCertificateCap => 76
  | .fanCertificateMarked => 77
  | .fanCertificateResidual => 78
  | .typeBHybridEntry => 80
  | .typeBDirectCycle => 81
  | .typeBDirectCycleFree => 82
  | .typeBB2Choice => 149
  | .typeBDisjointLedger => 150
  | .typeBOverlapObstruction => 84
  | .fanCertificateResidualMass => 186
  | .typeBOverlapObstructionMass => 187
  | .typeBExclusionResidualMass => 188
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
  | .typeAExitSevenProduced => 158
  | .route8ResidualProfile => 159
  | .route8GlobalSqueeze => 160
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
  | .route8NoTwoCarrierContradiction => 172
  | .route8TerminalNoGo => 174
  | .route8Census => 260
  | .route8Deficit => 263
  | .route8Rate => 264
  | .route8RateFails => 265
  | .route8PiecesClassified => 266
  | .route8UnifiedNegative => 336
  | .route8UnifiedDeficit => 339
  | .route8UnifiedEntryCensus => 340
  | .route8StageRateFailed => 342
  | .route8DemandAbsorption => 351
  | .route8WindowBlockers => 352
  | .route8PeeledDemandResidual => 353
  | .route8TwoCarrierEntry => 261
  | .route8NoTwoCarrierEntry => 262
  | .route8TrueTwoCarrierEntry => 280
  | .route8PeelingDescent => 282
  | .route8VisibleExitFourRouting => 338
  | .route8UnifiedTrueTwoCarrierEntry => 334
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
  | .freePairEntropySandwich => 240
  | .freePairCodeUnrealized => 241
  | .blockedPairEntropySandwich => 242
  | .blockedPairCodeUnrealized => 243
  | .windowClassOverload => 130
  | .windowClassAbsent => 131
  | .remainderClassOverload => 132
  | .remainderClassAbsent => 133
  | .windowIncidenceAudit => 134
  | .remainderSurplusAudit => 135
  | .primitiveCarrierAudit => 136
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
  | .targetRankCircuit => 210

/-- Left inverse of `idx`.  Writing it out is also what checks the numbering:
two keys sharing an index would make `ofIdx_idx` unprovable. -/
def ofIdx : Nat → Key
  | 0 => .selection
  | 221 => .cubicBaseline
  | 1 => .returnAvoidance
  | 2 => .noProperBaseline
  | 3 => .tightEndpoint
  | 4 => .slackIndependent
  | 322 => .degreeProfileFibres
  | 323 => .targetCompleteContextUniversality
  | 223 => .replacementExclusion
  | 224 => .coldMassLinear
  | 225 => .coldMassBounded
  | 226 => .bridgeless
  | 227 => .coldReturnCorridors
  | 228 => .windowPackageRealized
  | 229 => .windowPackageUnrealized
  | 337 => .densePackingOverflow
  | 230 => .denseDeficiencyBelow
  | 231 => .denseDeficiencyAtOrAbove
  | 232 => .coldWindowStubStructure
  | 233 => .coldCanonicalNeutralConfiguration
  | 234 => .coldGenuineSecondStrand
  | 244 => .coldCanonicalSwapSmaller
  | 245 => .coldCanonicalSwapSameSize
  | 238 => .blockedClassMember
  | 320 => .blockedScaleAdditive
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
  | 324 => .separatedTesters
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
  | 253 => .typeBFanLocalDichotomy
  | 254 => .typeBFanDegreeFourProfile
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
  | 65 => .coldFailureDefect
  | 66 => .coldFailureCompression
  | 67 => .coldFailureHandoff
  | 68 => .coldFailureRouting
  | 177 => .coldExchangeBound
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
  | 69 => .coldHandoffTransfer
  | 70 => .coldGermExtraction
  | 71 => .coldGermRouted
  | 176 => .coldBranchClosed
  | 72 => .highCentreNormalForm
  | 76 => .fanCertificateCap
  | 77 => .fanCertificateMarked
  | 78 => .fanCertificateResidual
  | 80 => .typeBHybridEntry
  | 81 => .typeBDirectCycle
  | 82 => .typeBDirectCycleFree
  | 149 => .typeBB2Choice
  | 150 => .typeBDisjointLedger
  | 84 => .typeBOverlapObstruction
  | 186 => .fanCertificateResidualMass
  | 187 => .typeBOverlapObstructionMass
  | 188 => .typeBExclusionResidualMass
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
  | 158 => .typeAExitSevenProduced
  | 159 => .route8ResidualProfile
  | 160 => .route8GlobalSqueeze
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
  | 172 => .route8NoTwoCarrierContradiction
  | 174 => .route8TerminalNoGo
  | 260 => .route8Census
  | 263 => .route8Deficit
  | 264 => .route8Rate
  | 265 => .route8RateFails
  | 266 => .route8PiecesClassified
  | 336 => .route8UnifiedNegative
  | 339 => .route8UnifiedDeficit
  | 340 => .route8UnifiedEntryCensus
  | 342 => .route8StageRateFailed
  | 351 => .route8DemandAbsorption
  | 352 => .route8WindowBlockers
  | 353 => .route8PeeledDemandResidual
  | 261 => .route8TwoCarrierEntry
  | 262 => .route8NoTwoCarrierEntry
  | 280 => .route8TrueTwoCarrierEntry
  | 282 => .route8PeelingDescent
  | 338 => .route8VisibleExitFourRouting
  | 334 => .route8UnifiedTrueTwoCarrierEntry
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
  | 137 => .quantitativeOverload
  | 140 => .homogeneousCapsHold
  | 141 => .homogeneousBottleneckPattern
  | 142 => .bottleneckRouting
  | 184 => .typeBHandoff
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
  | 242 => .blockedPairEntropySandwich
  | 243 => .blockedPairCodeUnrealized
  | 200 => .hotColdPartition
  | 201 => .dependentPairFamily
  | 202 => .independentPairFamily
  | 203 => .mixedSparseSpineDependence
  | 204 => .exactCubicBaselineBudget
  | 205 => .incrementalSkeletonRoom
  | 206 => .skeletonDominates
  | 207 => .exactResponseProfile
  | 208 => .admissibleRankQuotient
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
  | .cubicBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "cubicBaseline") 221
  | .returnAvoidance =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "returnAvoidance") 1
  | .noProperBaseline =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "noProperBaseline") 2
  | .tightEndpoint =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "tightEndpoint") 3
  | .slackIndependent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "slackIndependent") 4
  | .degreeProfileFibres =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "degreeProfileFibres") 322
  | .targetCompleteContextUniversality =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "targetCompleteContextUniversality") 323
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
  | .densePackingOverflow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "densePackingOverflow") 337
  | .denseDeficiencyBelow =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "denseDeficiencyBelow") 230
  | .denseDeficiencyAtOrAbove =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "denseDeficiencyAtOrAbove") 231
  | .coldWindowStubStructure =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldWindowStubStructure") 232
  | .coldCanonicalNeutralConfiguration =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "coldCanonicalNeutralConfiguration") 233
  | .coldGenuineSecondStrand =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldGenuineSecondStrand") 234
  | .coldCanonicalSwapSmaller =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCanonicalSwapSmaller") 244
  | .coldCanonicalSwapSameSize =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldCanonicalSwapSameSize") 245
  | .blockedClassMember =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedClassMember") 238
  | .blockedScaleAdditive =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "blockedScaleAdditive") 320
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
  | .separatedTesters =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "separatedTesters") 324
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
  | .typeBFanLocalDichotomy =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanLocalDichotomy") 253
  | .typeBFanDegreeFourProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "typeBFanDegreeFourProfile") 254
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
  | .coldBranchClosed =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "coldBranchClosed") 176
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
  | .typeAExitSevenProduced =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "typeAExitSevenProduced") 158
  | .route8ResidualProfile =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8ResidualProfile") 159
  | .route8GlobalSqueeze =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8GlobalSqueeze") 160
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
  | .route8NoTwoCarrierContradiction =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8NoTwoCarrierContradiction") 172
  | .route8TerminalNoGo =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8TerminalNoGo") 174
  | .route8Census =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Census") 260
  | .route8Deficit =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8Deficit") 263
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
  | .route8PeeledDemandResidual =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8PeeledDemandResidual") 353
  | .route8TwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8TwoCarrierEntry") 261
  | .route8NoTwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8NoTwoCarrierEntry") 262
  | .route8TrueTwoCarrierEntry =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8TrueTwoCarrierEntry") 280
  | .route8PeelingDescent =>
      .num (.str `Hypostructure.Graph.Strategy.Spine "route8PeelingDescent") 282
  | .route8VisibleExitFourRouting =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "route8VisibleExitFourRouting") 338
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
  | .blockedPairEntropySandwich =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedPairEntropySandwich") 242
  | .blockedPairCodeUnrealized =>
      .num (.str `Hypostructure.Graph.Strategy.Spine
        "blockedPairCodeUnrealized") 243
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
