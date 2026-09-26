import Hypostructure.Graph.Contracts.TypeB.Support

/-!
# Contracts: the local Type B fan analysis

`lem:heavy-neighbourhood-normal-form`, `lem:same-center-open-port-compatibility`,
the degree split, `cor:heavy-center-local-dichotomy` with its two routings,
`cor:degree-four-local-activation`, the fan-safe graph, `lem:fan-certificate`,
and the fan-closed port routing of `prop:fan-closed-port-typeB-routing`.  Each
conclusion is exactly the published statement; every hypothesis is explicit.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `lem:heavy-neighbourhood-normal-form` at every high centre.  (a) is the
tight-endpoint law at the edge `hx`; (b) and (c) exclude the two quadrilaterals
`hxyzh` and `hxzyh`, whose length is accepted. -/
theorem highCentreNormalForm
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (quadrilateral : data.LengthOK 4)
    (tight : TightEndpointStatement data object) :
    HighCentreNormalFormStatement data object := by
  intro centre high
  exact
    { neighbourTight := by
        intro x adjacent
        rcases tight ⟨(centre, x), adjacent⟩ with centreTight | endpointTight
        · exact absurd centreTight (Nat.ne_of_gt high)
        · exact endpointTight
      inducedMatching := by
        intro x y z centreX centreY centreZ distinct xy yz
        exact Graph.not_quadrilateral avoids quadrilateral
          centreX xy yz centreZ.symm centreY.ne distinct
      noCommonNeighbourOutside := by
        intro x y z centreX centreY distinct _nonadjacent outside xz yz
        exact Graph.not_quadrilateral avoids quadrilateral
          centreX xz yz.symm centreY.symm (Ne.symm outside) distinct }

/-- `lem:same-center-open-port-compatibility`. -/
theorem sameCenterOpenPortCompatibility
    (normal : HighCentreNormalFormStatement data object) :
    SameCenterOpenPortCompatibilityStatement data object := by
  intro centre high left right centreLeft centreRight distinct nonadjacent
    leftOpen rightOpen
  exact Graph.fanCompatible_of_endpoints_nonadjacent (normal centre high)
    centreLeft centreRight distinct nonadjacent leftOpen rightOpen

/-- The degree split: the no arm is the exact negation of the heavy arm. -/
theorem typeBFanDegreeFourCentres_iff_not_heavy :
    TypeBFanDegreeFourCentresStatement data object ↔
      ¬ TypeBFanHeavyCentreStatement data object := by
  constructor
  · rintro degreeFour ⟨packing, core, centres, support, centre, member, heavy⟩
    have degree := degreeFour packing core centres support centre member
    omega
  · intro notHeavy packing core centres support centre member
    exact TypeBSupport.degree_eq_of_not_heavy support member
      (fun heavy => notHeavy ⟨packing, core, centres, support, centre, member, heavy⟩)

/-- `cor:heavy-center-local-dichotomy` with its two routings at one heavy
centre: a fan-compatible open pair routes by
`cor:compatible-pair-typeB-routing`; otherwise `d_G(h) - 2 ≥ 3` ports are
triangular, and a family of exactly `d_G(h) - 2` of them routes by
`prop:triangular-port-typeB-routing`. -/
theorem heavyCentreRoutedAlternative
    (three : 3 ≤ data.threshold)
    (normal : HighCentreNormalFormStatement data object)
    (compatibleRouting : CompatiblePairTypeBRoutingStatement data object)
    (triangularRouting : TriangularPortTypeBRoutingStatement data object)
    {centre : object.Vertex}
    (heavy : data.threshold + 1 < object.degree centre) :
    HeavyCentreRoutedAlternative object centre := by
  have high : Graph.IsHighCentre object data.threshold centre := by
    simp only [Graph.IsHighCentre]
    omega
  rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
    ⟨left, right, compatible⟩ | triangular
  · exact Or.inl ⟨left, right, compatible, fun profile _hub =>
      compatibleRouting profile left right⟩
  · obtain ⟨ports, subset, card⟩ :=
      Finset.exists_subset_card_eq triangular
    refine Or.inr ⟨ports, subset, card, ?_, fun profile _hub =>
      triangularRouting profile ports⟩
    have atLeast := Graph.three_le_triangularEndpoints_card three heavy triangular
    omega

/-- Node-free form of the heavy-arm local analysis: every heavy assigned centre
of every Type B support carries the routed local dichotomy. -/
theorem typeBFanLocalDichotomy
    (three : 3 ≤ data.threshold)
    (normal : HighCentreNormalFormStatement data object)
    (compatibleRouting : CompatiblePairTypeBRoutingStatement data object)
    (triangularRouting : TriangularPortTypeBRoutingStatement data object) :
    TypeBFanLocalDichotomyStatement data object := by
  intro _packing _core _centres _support _centre _member heavy
  exact heavyCentreRoutedAlternative three normal compatibleRouting
    triangularRouting heavy

/-- `cor:degree-four-local-activation` and the degree-four fan profile at every
assigned centre, all of which have degree `δ + 1`. -/
theorem typeBFanDegreeFourProfile
    (normal : HighCentreNormalFormStatement data object)
    (degreeFour : TypeBFanDegreeFourCentresStatement data object) :
    TypeBFanDegreeFourProfileStatement data object := by
  intro packing core centres support centre member
  have high := TypeBSupport.high support centre member
  have degree := degreeFour packing core centres support centre member
  refine ⟨degree, ?_, ?_, ?_⟩
  · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
      compatible | triangular
    · exact Or.inl compatible
    · refine Or.inr ?_
      rw [degree] at triangular
      omega
  · omega
  · intro fanEnvelope
    obtain ⟨_surplus, counted, identity, _range⟩ :=
      Graph.TypeBFanIncidence.degreeFourProfile object data.threshold
        data.dischargeScale fanEnvelope degree
    exact ⟨counted, identity⟩

/-- `def:typeB-fan-safe`, clause (i), on a target-avoiding object: a fan return
whose shifted length is accepted closes an accepted cycle with the two fan
edges. -/
theorem fanSafeAt
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (centre : object.Vertex) :
    FanSafeAt data object centre := by
  intro first second firstAdj secondAdj different
  exact Graph.DecoratedHandoff.fanSafe_geometric firstAdj secondAdj different
    avoids

/-- The fan-safe graph at every assigned centre. -/
theorem typeBFanSafe
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    TypeBFanSafeStatement data object :=
  fun _packing _core _centres _support centre _member => fanSafeAt avoids centre

/-- The fan-safe graph and `lem:fan-certificate`: a certificate-marked centre is
capped by the label packing number of the registered window order. -/
theorem typeBFanCertificateCap
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    TypeBFanCertificateCapStatement data object := by
  intro _packing _core _centres _support centre _member
  exact ⟨fanSafeAt avoids centre, fun marking => marking.degree_le_fanPackingCap⟩

/-- `def:fan-closed-port`, with clause (c) derived. -/
theorem fanClosedPort : FanClosedPortStatement data object := by
  intro profile endpoint
  constructor
  · intro closed
    exact ⟨closed.1, closed.2, fun _shoulder member =>
      closed.incidence_classified member⟩
  · rintro ⟨remainder, envelope, _classified⟩
    exact ⟨remainder, envelope⟩

/-- `lem:compatible-pair-fan-closure`, read through `def:fan-closed-port`. -/
theorem compatiblePairFanClosure
    (definition : FanClosedPortStatement data object) :
    CompatiblePairFanClosureStatement data object := by
  intro profile left right compatible leftRemainder rightRemainder
    leftAssigned rightAssigned
  have closed := Graph.TypeBFanClosedPorts.compatiblePairFanClosure
    profile compatible leftRemainder rightRemainder leftAssigned rightAssigned
  exact ⟨(definition profile left).2 ((definition profile left).1 closed.1),
    (definition profile right).2 ((definition profile right).1 closed.2.1),
    closed.2.2⟩

/-- `prop:fan-closed-port-typeB-routing`, parts (a) and (b). -/
theorem fanClosedPortTypeBRouting
    (definition : FanClosedPortStatement data object) :
    FanClosedPortTypeBRoutingStatement data object := by
  intro profile ledger normal scale ports fanClosed two
  apply Graph.TypeBFanClosedPorts.fanClosedPortTypeBRouting
    profile ledger normal scale
  · intro vertex member
    exact (definition profile vertex).2
      ((definition profile vertex).1 (fanClosed vertex member))
  · exact two

/-- `cor:compatible-pair-typeB-routing`: the two fan-closed ports of
`lem:compatible-pair-fan-closure` route through
`prop:fan-closed-port-typeB-routing`. -/
theorem compatiblePairTypeBRouting
    (pairClosure : CompatiblePairFanClosureStatement data object)
    (fanClosedRouting : FanClosedPortTypeBRoutingStatement data object) :
    CompatiblePairTypeBRoutingStatement data object := by
  classical
  intro profile left right ledger normal scale compatible leftRemainder
    rightRemainder leftAssigned rightAssigned
  obtain ⟨leftClosed, rightClosed, distinct⟩ :=
    pairClosure profile left right compatible leftRemainder rightRemainder
      leftAssigned rightAssigned
  have pairCard : ({left, right} : Finset object.Vertex).card = 2 :=
    Finset.card_pair distinct
  have fanClosed : ∀ vertex ∈ ({left, right} : Finset object.Vertex),
      profile.IsFanClosed vertex := by
    intro vertex member
    rcases Finset.mem_insert.1 member with rfl | member
    · exact leftClosed
    · rw [Finset.mem_singleton] at member
      subst member
      exact rightClosed
  have routed := fanClosedRouting profile ledger normal scale
    ({left, right} : Finset object.Vertex) fanClosed (by rw [pairCard])
  rw [pairCard] at routed
  exact ⟨routed.1, routed.2.2.1, routed.2.2.2⟩

/-- `prop:triangular-port-typeB-routing`: a recorded and assigned family of
`k - 2` triangular ports is fan-closed and routes through
`prop:fan-closed-port-typeB-routing` with `D_B ≥ (5k - 19)/4`. -/
theorem triangularPortTypeBRouting
    (definition : FanClosedPortStatement data object)
    (fanClosedRouting : FanClosedPortTypeBRoutingStatement data object) :
    TriangularPortTypeBRoutingStatement data object := by
  classical
  intro profile ports ledger normal scale triangular cardPorts degreeFive
    remainder assigned
  have fanClosed : ∀ endpoint ∈ ports, profile.IsFanClosed endpoint := by
    intro endpoint member
    have direct : profile.IsFanClosed endpoint :=
      ⟨remainder endpoint member, assigned endpoint member⟩
    exact (definition profile endpoint).2
      ((definition profile endpoint).1 direct)
  have routed := fanClosedRouting profile ledger normal scale ports fanClosed
    (by omega)
  have canonical := Graph.TypeBFanClosedPorts.triangularPortTypeBRouting
    profile ledger normal scale triangular cardPorts degreeFive remainder
      assigned
  exact ⟨routed.1, canonical.2⟩

end Hypostructure.Graph.Contracts.TypeB
