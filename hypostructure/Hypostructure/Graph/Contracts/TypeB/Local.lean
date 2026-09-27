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

/-- On the `[19]` at-or-below arm, the node-`[65]` entry is on a continuation
lane: its same-token disjunct lives on the strict-surplus arm. -/
theorem typeBLanes_of_entry
    (entry : TypeBFanEntryStatement data object)
    (atOrBelow : SurplusAtOrBelowStatement data object) :
    TypeBLaneAt data object (fun _core centres =>
      centres.Nonempty ∧
        ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) := by
  rcases entry with lanes | ⟨above, _handoff⟩
  · exact lanes
  · exact absurd atOrBelow (Nat.not_le.mpr above)

/-- **Node `[68]`**: at the Type B support of the entry, some assigned centre is
heavy, or every assigned centre has the high-but-not-heavy degree `δ + 1`. -/
theorem typeBFanDegree_split
    (entry : TypeBFanEntryStatement data object)
    (atOrBelow : SurplusAtOrBelowStatement data object) :
    TypeBFanHeavyCentreStatement data object ∨
      TypeBFanDegreeFourCentresStatement data object := by
  rcases TypeBLaneAt.split (fun _core centres =>
      ∃ centre ∈ centres, data.threshold + 1 < object.degree centre)
      (typeBLanes_of_entry entry atOrBelow) with heavy | degreeFour
  · exact Or.inl (TypeBLaneAt.imp (fun _ _ _ holds => holds.2) heavy)
  · refine Or.inr (TypeBLaneAt.imp (fun _core centres member holds => ?_) degreeFour)
    intro centre centreMember
    have high := TypeBLaneMember.high member centre centreMember
    have notHeavy : ¬ data.threshold + 1 < object.degree centre :=
      fun heavy => holds.2 ⟨centre, centreMember, heavy⟩
    simp only [Graph.IsHighCentre] at high
    omega

/-- `cor:heavy-center-local-dichotomy` with its two routings at one heavy
centre: a fan-compatible open pair routes by
`cor:compatible-pair-typeB-routing`; otherwise `d_G(h) - 2 ≥ 3` ports are
triangular, and a family of exactly `d_G(h) - 2` of them routes by
`prop:triangular-port-typeB-routing`. -/
theorem heavyCentreRoutedAlternative
    (three : 3 ≤ data.threshold)
    (normal : HighCentreNormalFormStatement data object)
    {core centres : Finset object.Vertex}
    (compatibleRouting : CompatiblePairTypeBRoutingAt data object core centres)
    (triangularRouting : TriangularPortTypeBRoutingAt data object core centres)
    {centre : object.Vertex}
    (heavy : data.threshold + 1 < object.degree centre) :
    HeavyCentreRoutedAlternative data object core centres centre := by
  have high : Graph.IsHighCentre object data.threshold centre := by
    simp only [Graph.IsHighCentre]
    omega
  rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
    ⟨left, right, compatible⟩ | triangular
  · exact Or.inl ⟨left, right, compatible, fun profile fixed _hub =>
      compatibleRouting profile fixed left right⟩
  · obtain ⟨ports, subset, card⟩ :=
      Finset.exists_subset_card_eq triangular
    refine Or.inr ⟨ports, subset, card, ?_, fun profile fixed _hub =>
      triangularRouting profile fixed ports⟩
    have atLeast := Graph.three_le_triangularEndpoints_card three heavy triangular
    omega

/-- **Node `[69]`**: at the heavy arm's Type B support, every heavy assigned
centre carries the routed local dichotomy at the support's assigned profiles. -/
theorem typeBFanLocalDichotomy
    (three : 3 ≤ data.threshold)
    (normal : HighCentreNormalFormStatement data object)
    (compatibleRouting : CompatiblePairTypeBRoutingStatement data object)
    (triangularRouting : TriangularPortTypeBRoutingStatement data object)
    (heavy : TypeBFanHeavyCentreStatement data object) :
    TypeBFanLocalDichotomyStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member both =>
      ⟨both.1, fun _centre _member heavy =>
        heavyCentreRoutedAlternative three normal both.2.1 both.2.2 heavy⟩)
    (TypeBLaneAt.and heavy (TypeBLaneAt.and compatibleRouting triangularRouting))

/-- **Node `[79]`**: `cor:degree-four-local-activation` and the degree-four fan
profile at every assigned centre of the Type B support, all of degree `δ + 1`. -/
theorem typeBFanDegreeFourProfile
    (normal : HighCentreNormalFormStatement data object)
    (degreeFour : TypeBFanDegreeFourCentresStatement data object) :
    TypeBFanDegreeFourProfileStatement data object := by
  refine TypeBLaneAt.imp (fun _core centres member degrees => ?_) degreeFour
  intro centre centreMember
  have high := TypeBLaneMember.high member centre centreMember
  have degree := degrees centre centreMember
  obtain ⟨_surplus, counted, identity, _range⟩ :=
    Graph.TypeBFanIncidence.degreeFourProfile object data.threshold
      data.dischargeScale
      (typeBFanEnvelope _core centres centre) degree
  refine ⟨degree, ?_, ?_, counted, identity⟩
  · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
      compatible | triangular
    · exact Or.inl compatible
    · refine Or.inr ?_
      rw [degree] at triangular
      omega
  · omega

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

/-- **Node `[70]`**: the fan-safe graph and `lem:fan-certificate` at every
assigned centre of the Type B support of the `[69]`/`[79]` arm fact: G's
canonical fan-certificate labelling, when present, caps the degree. -/
theorem typeBFanCertificateCap
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (arm : TypeBLaneAt data object Q) :
    TypeBFanCertificateCapStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member _arm centre _centreMember =>
      ⟨fanSafeAt avoids centre, fun marking _markingEq =>
        marking.degree_le_fanPackingCap⟩)
    arm

/-- `def:fan-closed-port`, with clause (c) derived. -/
theorem fanClosedPortAt {core centres : Finset object.Vertex} :
    FanClosedPortAt data object core centres := by
  intro profile _fixed endpoint
  constructor
  · intro closed
    exact ⟨closed.1, closed.2, fun _shoulder member =>
      closed.incidence_classified member⟩
  · rintro ⟨remainder, envelope, _classified⟩
    exact ⟨remainder, envelope⟩

/-- `lem:compatible-pair-fan-closure`, read through `def:fan-closed-port`. -/
theorem compatiblePairFanClosureAt {core centres : Finset object.Vertex}
    (definition : FanClosedPortAt data object core centres) :
    CompatiblePairFanClosureAt data object core centres := by
  intro profile fixed left right compatible leftRemainder rightRemainder
    leftAssigned rightAssigned
  have closed := Graph.TypeBFanClosedPorts.compatiblePairFanClosure
    profile compatible leftRemainder rightRemainder leftAssigned rightAssigned
  exact ⟨(definition profile fixed left).2
      ((definition profile fixed left).1 closed.1),
    (definition profile fixed right).2
      ((definition profile fixed right).1 closed.2.1),
    closed.2.2⟩

/-- `prop:fan-closed-port-typeB-routing`, parts (a) and (b), at the registered
discharge rate: the library bound at `δ = 3`, `α = 1/4`, with both identities
read from the published cubic baseline. -/
theorem fanClosedPortTypeBRoutingAt {core centres : Finset object.Vertex}
    (thresholdEq : data.threshold = 3) (scaleEq : data.dischargeScale = 4)
    (definition : FanClosedPortAt data object core centres) :
    FanClosedPortTypeBRoutingAt data object core centres := by
  intro profile fixed normal ports fanClosed two
  have normalThree : Graph.NormalForm object 3 profile.marked.fan.hub :=
    thresholdEq ▸ normal
  obtain ⟨counted, familyBound, deficitBound, positive⟩ :=
    Graph.TypeBFanClosedPorts.fanClosedPortTypeBRouting profile
      (typeBDischargeProfile data) normalThree scaleEq
      (fun vertex member => (definition profile fixed vertex).2
        ((definition profile fixed vertex).1 (fanClosed vertex member))) two
  refine ⟨counted, ?_, deficitBound, positive⟩
  rw [thresholdEq]
  exact_mod_cast familyBound

/-- `cor:compatible-pair-typeB-routing`: the two fan-closed ports of
`lem:compatible-pair-fan-closure` route through
`prop:fan-closed-port-typeB-routing`. -/
theorem compatiblePairTypeBRoutingAt {core centres : Finset object.Vertex}
    (pairClosure : CompatiblePairFanClosureAt data object core centres)
    (fanClosedRouting : FanClosedPortTypeBRoutingAt data object core centres) :
    CompatiblePairTypeBRoutingAt data object core centres := by
  classical
  intro profile fixed left right normal compatible leftRemainder
    rightRemainder leftAssigned rightAssigned
  obtain ⟨leftClosed, rightClosed, distinct⟩ :=
    pairClosure profile fixed left right compatible leftRemainder rightRemainder
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
  have routed := fanClosedRouting profile fixed normal
    ({left, right} : Finset object.Vertex) fanClosed (by rw [pairCard])
  rw [pairCard] at routed
  exact ⟨routed.1, routed.2.2.1, routed.2.2.2⟩

/-- `prop:triangular-port-typeB-routing`: a recorded and assigned family of
`k - 2` triangular ports at a heavy centre is fan-closed and routes through
`prop:fan-closed-port-typeB-routing` with
`D_B ≥ ((s+1)k - (s(δ+2) - 1))/s`, the manuscript's `(5k - 19)/4`. -/
theorem triangularPortTypeBRoutingAt {core centres : Finset object.Vertex}
    (thresholdEq : data.threshold = 3) (scaleEq : data.dischargeScale = 4)
    (definition : FanClosedPortAt data object core centres)
    (fanClosedRouting : FanClosedPortTypeBRoutingAt data object core centres) :
    TriangularPortTypeBRoutingAt data object core centres := by
  classical
  intro profile fixed ports normal triangular cardPorts heavy remainder assigned
  have fanClosed : ∀ endpoint ∈ ports, profile.IsFanClosed endpoint := by
    intro endpoint member
    have direct : profile.IsFanClosed endpoint :=
      ⟨remainder endpoint member, assigned endpoint member⟩
    exact (definition profile fixed endpoint).2
      ((definition profile fixed endpoint).1 direct)
  have routed := fanClosedRouting profile fixed normal ports fanClosed
    (by omega)
  have normalThree : Graph.NormalForm object 3 profile.marked.fan.hub :=
    thresholdEq ▸ normal
  have canonical := Graph.TypeBFanClosedPorts.triangularPortTypeBRouting
    profile (typeBDischargeProfile data) normalThree scaleEq triangular
      cardPorts (by omega) remainder assigned
  refine ⟨routed.1, ?_, canonical.2.2⟩
  have bound := canonical.2.1
  rw [scaleEq, thresholdEq]
  convert bound using 1
  norm_num

/-! ### The routings at the Type B support of `G` -/

/-- `lem:compatible-pair-fan-closure` at the Type B support of the node-`[65]`
entry, read through `def:fan-closed-port` (`fanClosedPortAt`). -/
theorem compatiblePairFanClosure
    (entry : TypeBFanEntryStatement data object)
    (atOrBelow : SurplusAtOrBelowStatement data object) :
    CompatiblePairFanClosureStatement data object :=
  TypeBLaneAt.imp (fun _ _ _ _ => compatiblePairFanClosureAt fanClosedPortAt)
    (typeBLanes_of_entry entry atOrBelow)

/-- `prop:fan-closed-port-typeB-routing` at the Type B support of the pair
closure fact, read through `def:fan-closed-port`. -/
theorem fanClosedPortTypeBRouting
    (thresholdEq : data.threshold = 3) (scaleEq : data.dischargeScale = 4)
    (pairClosure : CompatiblePairFanClosureStatement data object) :
    FanClosedPortTypeBRoutingStatement data object :=
  TypeBLaneAt.imp (fun _ _ _ _ =>
    fanClosedPortTypeBRoutingAt thresholdEq scaleEq fanClosedPortAt) pairClosure

/-- `cor:compatible-pair-typeB-routing` at the Type B support. -/
theorem compatiblePairTypeBRouting
    (pairClosure : CompatiblePairFanClosureStatement data object)
    (fanClosedRouting : FanClosedPortTypeBRoutingStatement data object) :
    CompatiblePairTypeBRoutingStatement data object :=
  TypeBLaneAt.imp (fun _ _ _ both => compatiblePairTypeBRoutingAt both.1 both.2)
    (TypeBLaneAt.and pairClosure fanClosedRouting)

/-- `prop:triangular-port-typeB-routing` at the Type B support, read through
`def:fan-closed-port`. -/
theorem triangularPortTypeBRouting
    (thresholdEq : data.threshold = 3) (scaleEq : data.dischargeScale = 4)
    (fanClosedRouting : FanClosedPortTypeBRoutingStatement data object) :
    TriangularPortTypeBRoutingStatement data object :=
  TypeBLaneAt.imp (fun _ _ _ holds =>
      triangularPortTypeBRoutingAt thresholdEq scaleEq fanClosedPortAt holds)
    fanClosedRouting

end Hypostructure.Graph.Contracts.TypeB
