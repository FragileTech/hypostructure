import Hypostructure.Graph.Contracts.TypeB.Support
import Hypostructure.Graph.Statements.SurplusPairRouting
import Hypostructure.Graph.Contracts.Spine.ColdSubcubicCharge

/-!
# Contracts: the Type B entries

The assigned Type B support of each entry form of node `[65]`, at the canonical
object of `G` that the producing key fixed: the ordinary support `(X₀, H(X₀))`
(`def:canonical-decomp`), the decorated exit-`(7)` handoff `(X₀, {z})`
(`lem:decorated-fan-admissibility`), the absorbed-germ supports of
`lem:absorbed-germ-fan-data` (ii), and the same-token handoff of
`lem:same-token-bottleneck-routing`.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `σ(X) = Σ_{v ∈ X}(d_G(v) − δ) > 0` forces a vertex above the baseline. -/
theorem exists_highCentre_of_ambientSurplus_pos
    {support : Finset object.Vertex}
    (positive : 0 < object.ambientSurplus support data.threshold) :
    ∃ centre ∈ support, Graph.IsHighCentre object data.threshold centre := by
  classical
  by_contra none
  push Not at none
  have zero : object.ambientSurplus support data.threshold = 0 := by
    unfold Graph.FiniteObject.ambientSurplus
    refine Finset.sum_eq_zero fun vertex member => ?_
    have := none vertex member
    simp only [Graph.IsHighCentre, not_lt] at this
    omega
  omega

/-- The ordinary Type B support `(X₀, H(X₀))` on the Type B arm `σ(X₀) > 0` of
node `[62]`, on the net-cap arm of `[57]`. -/
theorem typeBOrdinaryLane_of_highSurplus
    (cap : NetChargeCapStatement data object)
    (surplus : ∃ piece, canonicalNegativePiece data object = some piece ∧
      0 < object.ambientSurplus piece data.threshold) :
    ∃ piece, TypeBOrdinaryLane data object piece
      (Graph.TypeBRefinedSupport.centres object data.threshold piece) := by
  obtain ⟨piece, pieceEq, positive⟩ := surplus
  exact ⟨piece, cap, by simp [canonicalTypeBOrdinarySupport, pieceEq], positive⟩

/-- `def:canonical-decomp` at the ordinary Type B support: `X₀` is negative and
carries a high centre. -/
theorem typeBAssignedSupport
    (cap : NetChargeCapStatement data object)
    (surplus : ∃ piece, canonicalNegativePiece data object = some piece ∧
      0 < object.ambientSurplus piece data.threshold) :
    TypeBAssignedSupportStatement data object := by
  obtain ⟨piece, lane⟩ := typeBOrdinaryLane_of_highSurplus cap surplus
  obtain ⟨_component, _componentEq, _member, _pieceEq, negative, _subset⟩ :=
    TypeBOrdinaryLane.canonical lane
  exact ⟨piece, _, lane, negative, exists_highCentre_of_ambientSurplus_pos lane.2.2⟩

/-- The ordinary Type B support enters node `[65]` with its own high centres
as assigned centres. -/
theorem typeBFanEntry_of_highSurplus
    (cap : NetChargeCapStatement data object)
    (surplus : ∃ piece, canonicalNegativePiece data object = some piece ∧
      0 < object.ambientSurplus piece data.threshold) :
    TypeBFanEntryStatement data object := by
  obtain ⟨piece, lane⟩ := typeBOrdinaryLane_of_highSurplus cap surplus
  obtain ⟨centre, member, high⟩ := exists_highCentre_of_ambientSurplus_pos lane.2.2
  exact Or.inl (Or.inl ⟨piece, _, lane,
    ⟨centre, Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩,
    TypeBOrdinaryLane.high lane⟩)

/-- The decorated Type B support `(X₀, {z})` of node `[108]`: on the Type A arm
`σ(X₀) = 0` of `[62]` and the exit-`(7)` arm of `[107]` at `X₀`, the canonical
surviving separator `z` of `X₀` exists and its canonical envelope is built
(`lem:typeA-high-degree-handoff`, tex 11110: `z` has degree at least `4`, and
the label-collision absorbing clause is refuted by target avoidance). -/
theorem typeBDecoratedLane_of_handoff
    (cap : NetChargeCapStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (zero : ∃ piece, canonicalNegativePiece data object = some piece ∧
      object.ambientSurplus piece data.threshold = 0)
    (handoff : ∃ piece, canonicalNegativePiece data object = some piece ∧
      SeparatorHandoffAt data object piece) :
    ∃ core centres, TypeBDecoratedLane data object core centres := by
  obtain ⟨piece, pieceEq, zeroSurplus⟩ := zero
  obtain ⟨piece', pieceEq', separated⟩ := handoff
  rw [pieceEq, Option.some.injEq] at pieceEq'
  subst pieceEq'
  have spec := (separatorHandoffAt_iff_exists_spec data object piece).mp separated
  obtain ⟨separation, separationEq, _⟩ := canonicalHandoffSeparationAt_spec spec
  have supportEq : canonicalTypeBDecoratedSupport data object =
      some (piece, {separation.2.separation.separator}) := by
    simp [canonicalTypeBDecoratedSupport, pieceEq, canonicalHandoffSeparatorAt,
      separationEq]
  have envelopeSome : (canonicalTypeBDecoratedEnvelope data object).isSome := by
    unfold canonicalTypeBDecoratedEnvelope
    rw [pieceEq, Option.bind_some]
    exact canonicalHandoffEnvelopeAt_isSome avoids
      (fun separated _ => by
        have four := Graph.DecoratedHandoff.four_le_degree_of_surviving
          separated.2.surviving
        show data.threshold < object.degree separated.2.separation.separator
        omega)
      (fun _centre _first _second collision =>
        avoids (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
          degenerate collision))
      spec
  exact ⟨piece, _, cap, supportEq, zeroSurplus, envelopeSome⟩

/-- `def:decorated-fan-envelope` and `lem:decorated-fan-admissibility`: the
canonical exit-`(7)` envelope of `X₀` is admissible Type B fan-envelope data. -/
theorem typeBDecoratedAssignedSupport
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    {core centres : Finset object.Vertex}
    (lane : TypeBDecoratedLane data object core centres) :
    TypeBDecoratedAssignedSupportStatement data object := by
  obtain ⟨envelope, envelopeEq, coreEq, decorations⟩ :=
    TypeBDecoratedLane.envelope lane
  obtain ⟨component, _componentEq, _member, pieceEq, _negative, _subset⟩ :=
    TypeBDecoratedLane.canonical lane
  have coreInside : envelope.core ⊆
      object.remainderSupport (canonicalWindowPacking data object) := by
    rw [coreEq, ← pieceEq]
    exact object.pieceSupport_subset _ component
  have windowFree : handoffWindowFree data object envelope.core := by
    constructor
    · intro window subset windowInduces
      exact (normalized window
        (subset.trans coreInside)).1 windowInduces
    · intro internal subset
      exact (normalized internal
        (subset.trans coreInside)).2
  have admissible :
      Graph.DecoratedHandoff.Admissible object
        data.LengthOK (handoffUncompressible data object)
        (handoffWindowFree data object) envelope :=
    { dyadicSafe := avoids
      coreWindowFree := windowFree
      uncompressible := handoffUncompressible_of_uncompressible uncompressible
      fanReturnSafe := fun centre centreMember first firstMember second
          secondMember different =>
        (envelope.fanSafe centre centreMember first firstMember second
          secondMember different).1 }
  subst decorations
  exact ⟨core, _, lane, envelope, envelopeEq, coreEq, rfl,
    TypeBDecoratedLane.high lane,
    fun centre member =>
      ⟨envelope.assigned_nonempty centre member,
        envelope.assigned_adj centre member⟩,
    admissible⟩

/-- Node `[108]` at the terminal state of `X₀`: `σ(X₀) = 0` and the canonical
exit-`(7)` separation of `X₀` exists, so `X₀` has a surviving exit-`(7)`
separator (`SeparatorHandoffAt`). -/
theorem exitSevenHandoff_pinned
    (handoff : TypeAExitSevenEnvelopeStatement data object) :
    ∃ piece, canonicalNegativePiece data object = some piece ∧
      object.ambientSurplus piece data.threshold = 0 ∧
      SeparatorHandoffAt data object piece := by
  obtain ⟨piece, pieceEq, _receiver, _receiverEq, zero,
    ⟨separation, separationEq, _, _⟩, _envelope⟩ := handoff
  exact ⟨piece, pieceEq, zero, (separatorHandoffAt_iff_exists_spec data object
    piece).mpr ⟨_, canonicalHandoffSeparationAt_spec_of_eq_some separationEq⟩⟩

/-- Node `[108]` → `[66]` → `[65]`: the canonical exit-`(7)` envelope of `X₀` is
admissible Type B fan-envelope data. -/
theorem typeBDecoratedAssignedSupport_of_handoff
    (cap : NetChargeCapStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (handoff : TypeAExitSevenEnvelopeStatement data object) :
    TypeBDecoratedAssignedSupportStatement data object := by
  obtain ⟨piece, pieceEq, zero, separated⟩ := exitSevenHandoff_pinned handoff
  obtain ⟨_core, _centres, lane⟩ := typeBDecoratedLane_of_handoff cap avoids cubic
    degenerate ⟨piece, pieceEq, zero⟩ ⟨piece, pieceEq, separated⟩
  exact typeBDecoratedAssignedSupport avoids uncompressible normalized lane

/-- The decorated handoff enters node `[65]` with the decoration `{z}` as its
assigned centres (`def:typeB-assigned-ledger`). -/
theorem typeBFanEntry_of_decoratedLane {core centres : Finset object.Vertex}
    (lane : TypeBDecoratedLane data object core centres) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_piece, separator, _separatorEq, centresEq⟩ :=
    decoratedSupport_eq_some lane.2.1
  exact Or.inl (Or.inr (Or.inl ⟨core, centres, lane,
    ⟨separator, by simp [centresEq]⟩, TypeBDecoratedLane.high lane⟩))

/-- The decorated handoff of node `[108]` enters node `[65]`. -/
theorem typeBFanEntry_of_decoratedHandoff
    (cap : NetChargeCapStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (handoff : TypeAExitSevenEnvelopeStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨piece, pieceEq, zero, separated⟩ := exitSevenHandoff_pinned handoff
  obtain ⟨_core, _centres, lane⟩ := typeBDecoratedLane_of_handoff cap avoids cubic
    degenerate ⟨piece, pieceEq, zero⟩ ⟨piece, pieceEq, separated⟩
  exact typeBFanEntry_of_decoratedLane lane


set_option maxHeartbeats 8000000 in
/-- `lem:absorbed-germ-fan-data` (ii): at every selected half-edge, the first
high centre of the retained corridor, with the connected first-failure prefix
as core, is an admissible decorated handoff (node `[177]`). -/
theorem absorbedGermDecoratedAssignedSupport
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (three : 3 ≤ data.threshold)
    (degenerate : ¬ data.LengthOK 2) :
    AbsorbedGermDecoratedAssignedSupportStatement data object := by
  classical
  letI : FinEnum object.Vertex :=
    object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableRel object.graph.Adj :=
    object.decideAdj
  simp only [AbsorbedGermDecoratedAssignedSupportStatement]
  change AbsorbedGermFanDataStatement data object at fanData
  simp only [AbsorbedGermFanDataStatement] at fanData
  obtain ⟨routing, fanData⟩ := fanData
  refine ⟨routing, ?_⟩
  intro epsilon notCandidate
  obtain ⟨firstIndex, firstBound, high, earlierBound,
      neighboursCubic⟩ := fanData epsilon notCandidate
  let classified := coldRoutedClassified data object routing
  let state := classified.state
  let stateOne := Classical.choose_spec state
  let componentAt := Classical.choose stateOne
  let stateTwo := Classical.choose_spec stateOne
  let corridorAt := Classical.choose stateTwo
  let stateThree := Classical.choose_spec stateTwo
  let presentationAt := Classical.choose stateThree
  let stateFour := Classical.choose_spec stateThree
  let indexAt := Classical.choose stateFour
  let routed : ColdEligibleHalfEdge data object := epsilon
  let component := componentAt routed
  let corridor := corridorAt routed
  let _presentation := presentationAt routed
  let _index := indexAt routed
  let centre := corridor.head firstIndex
  change data.threshold < object.degree centre at high
  change (∀ neighbour : object.Vertex,
    object.graph.Adj centre neighbour →
      object.degree neighbour = data.threshold) at neighboursCubic
  refine ⟨centre, ⟨routing, epsilon, rfl, firstIndex, rfl,
    firstBound, high, earlierBound, neighboursCubic, ?_⟩⟩
  let traceEnd := coldRoutedTraceEnd data object routing epsilon
  change firstIndex.1 ≤ traceEnd at firstBound
  let core := corridor.prefixSupport traceEnd
  have centreCore : centre ∈ core := by
    apply (corridor.mem_prefixSupport traceEnd centre).2
    refine ⟨corridor.inside.1.getVert firstIndex.1, ?_, rfl⟩
    have member := SimpleGraph.Walk.getVert_mem_support
      (corridor.inside.1.take traceEnd) firstIndex.1
    simpa only [SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right firstBound] using member
  have coreInside : core ⊆ object.remainderSupport
      (canonicalWindowPacking data object) := by
    exact Contracts.Spine.coldAbsorbedPrefix_subset_remainder data object
      routing epsilon notCandidate
  have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
      object := avoids
  have denied : ∀ c a b,
      ¬ handoffAbsorbing data object
        (canonicalWindowPacking data object) c a b :=
    fun _ _ _ collision => avoids
      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        degenerate collision)
  let assigned := object.graph.neighborFinset centre
  let arm := fun next : object.Vertex =>
    if next ∈ core then [next] else [next, centre]
  let envelope : Graph.DecoratedHandoff.Envelope object
      data.LengthOK (handoffHighDegree data object)
      (handoffAbsorbing data object
        (canonicalWindowPacking data object)) :=
    { core := core
      decorations := {centre}
      decorations_high := by
        intro current member
        simp only [Finset.mem_singleton] at member
        simpa [member] using high
      assigned := fun _ => assigned
      assigned_nonempty := by
        intro current member
        simp only [Finset.mem_singleton] at member
        subst current
        apply Finset.card_pos.mp
        rw [show assigned.card = object.degree centre by
          simp [assigned, Graph.FiniteObject.degree,
            SimpleGraph.card_neighborFinset_eq_degree]]
        exact Nat.zero_lt_of_lt high
      assigned_adj := by
        intro current member next nextMember
        simp only [Finset.mem_singleton] at member
        subst current
        exact (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
      arm := fun _ next => arm next
      arm_issued := by
        intro current member next nextMember
        simp only [Finset.mem_singleton] at member
        subst current
        by_cases nextCore : next ∈ core <;> simp [arm, nextCore]
      arm_chain := by
        intro current member next nextMember
        simp only [Finset.mem_singleton] at member
        subst current
        have adjacent :=
          (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
        by_cases nextCore : next ∈ core
        · simp [arm, nextCore]
        · simpa [arm, nextCore] using adjacent.symm
      arm_nodup := by
        intro current member next nextMember
        simp only [Finset.mem_singleton] at member
        subst current
        have adjacent :=
          (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
        by_cases nextCore : next ∈ core
        · simp [arm, nextCore]
        · simp [arm, nextCore, adjacent.ne.symm]
      arm_lands := by
        intro current member next nextMember
        simp only [Finset.mem_singleton] at member
        subst current
        by_cases nextCore : next ∈ core
        · exact ⟨next, by simp [arm, nextCore], nextCore⟩
        · exact ⟨centre, by simp [arm, nextCore], centreCore⟩
      arm_interior := by
        intro current member next nextMember vertex vertexMember alternative
        simp only [Finset.mem_singleton] at member
        subst current
        have adjacent :=
          (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
        by_cases nextCore : next ∈ core
        · simp only [arm, if_pos nextCore, List.mem_singleton] at vertexMember
          simp [vertexMember, arm, nextCore]
        · simp only [arm, if_neg nextCore, List.mem_cons,
            List.not_mem_nil, or_false] at vertexMember
          rcases vertexMember with rfl | rfl
          · exfalso
            simp only [Finset.mem_singleton] at alternative
            rcases alternative with inCore | equal | equal
            · exact nextCore inCore
            · exact adjacent.ne equal.symm
            · exact adjacent.ne equal.symm
          · simp [arm, nextCore]
      fanSafe := by
        intro current member first firstMember second secondMember different
        simp only [Finset.mem_singleton] at member
        subst current
        have firstAdj :=
          (SimpleGraph.mem_neighborFinset _ _ _).1 firstMember
        have secondAdj :=
          (SimpleGraph.mem_neighborFinset _ _ _).1 secondMember
        exact ⟨Graph.DecoratedHandoff.fanSafe_geometric firstAdj secondAdj
            different avoids,
          denied centre first second⟩ }
  have coreSafe : handoffWindowFree data object core := by
    constructor
    · intro window subset induced
      exact (normalized window
          (subset.trans coreInside)).1 induced
    · intro internal subset
      exact (normalized internal
          (subset.trans coreInside)).2
  have admissible : Graph.DecoratedHandoff.Admissible
      object data.LengthOK
      (handoffUncompressible data object)
      (handoffWindowFree data object) envelope :=
    Graph.DecoratedHandoff.admissible_of_envelope avoids coreSafe
      (handoffUncompressible_of_uncompressible uncompressible)
  have assignedTwo : 1 < assigned.card := by
    rw [show assigned.card = object.degree centre by
      simp [assigned, Graph.FiniteObject.degree,
        SimpleGraph.card_neighborFinset_eq_degree]]
    have thresholdLower := three
    omega
  obtain ⟨first, firstMember, second, secondMember, different⟩ :=
    Finset.one_lt_card.mp assignedTwo
  have firstAssigned : first ∈ envelope.assigned centre := by
    simpa [envelope] using firstMember
  have secondAssigned : second ∈ envelope.assigned centre := by
    simpa [envelope] using secondMember
  refine And.intro (corridor.prefixSupport_connectedOn traceEnd) ?_
  refine And.intro coreInside ?_
  refine Exists.intro envelope ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro admissible ?_
  refine Exists.intro first ?_
  refine Exists.intro second ?_
  exact And.intro different (And.intro firstAssigned secondAssigned)



/-- Node `[177]` → `[65]`: on the failed-collision arm of `[173]`, every selected
half-edge outside the subcubic candidates has its canonical absorbed support,
whose single centre is high. -/
theorem typeBFanEntry_of_absorbedGermFanData
    (fails : ExactCollisionFailsStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (supports : AbsorbedGermDecoratedAssignedSupportStatement data object) :
    TypeBFanEntryStatement data object := by
  classical
  obtain ⟨routing, witnesses⟩ := supports
  refine Or.inl (Or.inr (Or.inr ⟨⟨fails, fanData, routing, ?_⟩, ?_⟩))
  · intro epsilon notCandidate
    obtain ⟨centre, centreEq, _⟩ :=
      canonicalAbsorbedCentre_spec routing (witnesses epsilon notCandidate)
    simp [canonicalTypeBAbsorbedSupport, routing, centreEq]
  · intro epsilon core centres lane
    obtain ⟨_routing, _notCandidate, support⟩ := id lane
    obtain ⟨centre, _centreEq, rfl⟩ := absorbedSupport_eq_some support
    exact ⟨⟨centre, Finset.mem_singleton_self centre⟩,
      TypeBAbsorbedLane.high lane⟩

/-- Node `[144]` → `[65]`: the same-token handoff of G on the strict-surplus arm
of `[19]` enters the common Type B entry at G's canonical same-token support. -/
theorem typeBFanEntry_of_sameTokenHandoff
    (above : SurplusAboveStatement data object)
    (handoff : SameTokenTypeBHandoffStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨core, centres, handoffAt⟩ := handoff
  obtain ⟨⟨core', centres'⟩, selected, handoffAt'⟩ :=
    canonicalChoice_spec (spec := fun support : Finset object.Vertex × Finset object.Vertex =>
      SameTokenHandoffAt data object support.1 support.2) ⟨(core, centres), handoffAt⟩
  exact Or.inr ⟨above, Or.inl ⟨core', centres', selected, handoffAt'⟩⟩

end Hypostructure.Graph.Contracts.TypeB
