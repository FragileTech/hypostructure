import Hypostructure.Graph.WindowAttachmentShadow
import Mathlib.Combinatorics.SimpleGraph.Metric
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
import Hypostructure.Graph.TypeBFanClosedPorts
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
import Hypostructure.Graph.LabelledRelabeling
import Hypostructure.Graph.AddedEdgeClosure
import Hypostructure.Graph.RootedLocalType
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.TargetDefectStructure
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.BlockedClass
import Hypostructure.Graph.CanonicalRealization
import Hypostructure.Graph.TwoStrandEnumeration
import Hypostructure.Graph.SerialSystemArithmetic

/-!
# Statements: registered parameters

The registered constants of a minimum-degree cycle spine that its statement
definitions read: the baseline, target predicate, window order, discharge
scale, routing alphabet size, certified barrier table, scale family, and the
remaining finite rates.  Every statement module takes a `Parameters` value as an
explicit argument; the presentation's side conditions on these numbers are not
part of this record.  This module imports no strategy, row, or vocabulary
module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

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

/-- **The registered parameters of a minimum-degree cycle spine** read by its
statement definitions.  A problem supplies them through its registered
presentation; no statement writes one of these numbers. -/
structure Parameters where
  /-- The registered minimum-degree baseline `δ`. -/
  threshold : Nat
  /-- The accepted cycle lengths the counterexample must avoid. -/
  LengthOK : Nat → Prop
  /-- The order of the induced obstruction window.  For `thm:p13free` this is
  the induced-path order; nothing here knows its value. -/
  windowOrder : Nat
  windowOrder_pos : 0 < windowOrder
  /-- **The `4` of node `[58]`.**  `def:net-charge` is
  `N₀(X) = def⁺(X) − σ(X) − |V(X)|/s` at this discharge scale.  Every
  comparison of the charge is made after multiplying through by `s`, so the
  reciprocal never appears and nothing rounds. -/
  dischargeScale : Nat
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
  /-- The selected dyadic scales of `lem:p13-window-package`. -/
  separatedScaleCount : Nat → Nat
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
  /-- **The `10` of node `[50]`.**  `prop:two-budget` splits on
  `η(R) ≥ (1/10)·log₂ n`, and the denominator is the proof's own threshold
  choice rather than anything measured on a graph.  Node `[50]` compares
  `n^{|R|}` against `|𝒢(R)|^d` at this `d`, so no logarithm or division is
  written. -/
  entropyDenominator : Nat
  /-- **`F`, the registered Type B bridge-mass factor.**

  `lem:typeB-bridge-deficit-bound` charges each bridge residual centre at
  `No_-(X) ≤ F·Σ_{h∈H_X}(d_G(h) − δ)` — the manuscript's `8`.  The value is not
  forced by anything: the estimate `(k − δ + α) + cα ≤ F(k − δ)` holds for every
  factor above a floor the next field records, and the manuscript picks a round
  one.  So it is a presentation constant, registered here in the same way as the
  order exponent, and `prop:typeB-bridge-sublinear`'s `16σ(G)` is this factor
  against the at-most-twice occurrence convention. -/
  bridgeMassFactor : Nat

/-- The paper's bounded-port boundary profile alphabet, derived from the
registered baseline rather than supplied by a problem. -/
abbrev Parameters.BoundaryProfile (data : Parameters) : Type :=
  Fin data.threshold → Fin data.threshold

/-- The paper's finite cold-corridor signature.  Its generating values retain
the exact labelled bounded-interface incidences of each D1--D7 coordinate;
`coldFirstFailureRoutingRow` reads those incidences from the current object. -/
noncomputable def Parameters.coldSignature (data : Parameters) :
    Graph.ColdCorridor.DeclaredSignature :=
  Graph.ColdCorridor.declaredSignature data.windowOrder data.windowOrder_pos

@[simp] theorem Parameters.coldSignature_windowOrder (data : Parameters) :
    data.coldSignature.windowOrder = data.windowOrder := rfl

/-- Finiteness of the derived profile alphabet. -/
@[reducible] noncomputable def Parameters.boundaryProfileFintype (data : Parameters) :
    Fintype data.BoundaryProfile := inferInstance

/-- `M₀ = Cap_hom(L_geom)`, computed generically from the public declared
coordinate signature.  No application repeats or hardcodes this alphabet. -/
def Parameters.homogeneousCap (data : Parameters) : Nat :=
  registeredHomogeneousCap data.routingLabelBound

/-- The coefficient of the linear capacity-token supply, derived from the
public baseline degree. -/
def Parameters.capacityTokenScale (data : Parameters) : Nat :=
  3 * (data.threshold - 1) + 2

/-- The paper's `C_sp`, obtained by the generic quadratic absorption from the
public presentation's baseline deficit scale and the computed token cap. -/
def Parameters.spineScale (data : Parameters) : Nat :=
  registeredSpineScale data.routingLabelBound data.threshold data.surplusScale

/-- **The registered scale threshold `C_sp·⌈√n⌉` of node `[19]`**. -/
def Parameters.surplusThreshold (data : Parameters) (size : Nat) : Nat :=
  data.spineScale * Core.ceilSqrt size

/-- **`A`, the net-charge coefficient of `cor:global-window-join-pressure`.**
`s·(δ·order − 2(order−1)) + order`, the manuscript's `73` at its own values.
No node writes it; it is read from the registered numbers. -/
def Parameters.netChargeCoefficient (data : Parameters) : Nat :=
  data.dischargeScale *
      (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) +
    data.windowOrder

/-- The Type A/B presentation determined by the spine's registered data. -/
def Parameters.typeABPresentation (data : Parameters) : Graph.TypeAB.Presentation.{u} where
  baselineDegree := data.threshold
  inducedPathOrder := data.windowOrder
  dischargeScale := data.dischargeScale
  Target := Graph.HasCycleWithLength data.LengthOK
  LengthOK := data.LengthOK

/-- The exact `o(1)` slack the cold branch hands to `prop:p13-density` at node
`[24]`: on the bounded arm
`C ≤ (1 + (threshold+1)·B_cold)·σ(G)`, so the window-only cap
carries `2·(1 + (threshold+1)·B_cold)·rate·scaleCount·T(n)`. -/
noncomputable def Parameters.densitySlack (data : Parameters) : Nat :=
  2 * (1 + (data.threshold + 1) *
    Graph.ColdCorridor.overlapBound data.threshold data.coldSignature)

end Hypostructure.Graph.Strategy.Spine
