import Hypostructure.Graph.Contracts.TypeB.Support
import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contracts: the Type B entries

The assigned Type B supports produced by the ordinary support
(`def:canonical-decomp`), the decorated handoff (`lem:decorated-fan-admissibility`),
the absorbed-germ fan data (`lem:absorbed-germ-fan-data` (ii)) and the
same-token handoff (`lem:same-token-bottleneck-routing`).
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

/-- `def:canonical-decomp` at the ordinary Type B support: its assigned fan
centres are its own high centres, and there is one. -/
theorem typeBAssignedSupport
    (typeB : TypeBHighSurplusStatement data object) :
    TypeBAssignedSupportStatement data object := by
  obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ := typeB
  exact ⟨packing, valid, maximal, component, present, charge, positive,
    exists_highCentre_of_ambientSurplus_pos positive⟩

/-- The ordinary Type B support enters node `[65]` with its high centres as
assigned centres. -/
theorem typeBFanEntry_of_highSurplus
    (typeB : TypeBHighSurplusStatement data object) :
    TypeBFanEntryStatement data object := by
  classical
  apply Or.inl
  obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ := typeB
  obtain ⟨centre, member, high⟩ := exists_highCentre_of_ambientSurplus_pos positive
  refine ⟨packing, valid, maximal, component, present,
    Graph.TypeBRefinedSupport.centres object data.threshold
      (object.pieceSupport (object.remainderSupport packing) component),
    Or.inl ⟨charge, positive, rfl⟩, ?_, ?_⟩
  · exact ⟨centre, Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩
  · intro vertex vertexMem
    exact (Graph.TypeBRefinedSupport.mem_centres.1 vertexMem).2

/-- `lem:typeA-high-degree-handoff` (tex 11110): the surviving first separator
of an exit-`(7)` piece, with its separated connector tails, is a decorated
handoff fan envelope whose counted core is the piece.  By
`lem:typeA-cubic-switch-absorption` the separator has degree at least `4`, and
the label-collision absorbing clause is refuted by target avoidance. -/
theorem handoffEnvelope_of_separatorHandoffAt
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (packing : Finset (Finset object.Vertex)) {piece : Finset object.Vertex}
    (handoff : SeparatorHandoffAt data object piece) :
    ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
        (handoffHighDegree data object) (handoffAbsorbing data object packing),
      envelope.core = piece ∧ envelope.decorations.Nonempty := by
  obtain ⟨_receiver, _receiverMem, _load, separated⟩ := handoff
  exact Graph.Route8.TraceBasin.exists_envelope_of_traceSurvivingSeparator
    separated avoids
    (fun vertex high => by
      show data.threshold < object.degree vertex
      rw [cubic]
      exact high)
    (fun _centre _first _second collision =>
      avoids (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        degenerate collision))

/-- `def:decorated-fan-envelope` and `lem:decorated-fan-admissibility`: the
exit-`(7)` envelope is admissible Type B fan-envelope data. -/
theorem typeBDecoratedAssignedSupport
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (handoff : TypeAExitSevenHandoffStatement data object) :
    TypeBDecoratedAssignedSupportStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
    noCompression, noDelocalization, produced⟩ :=
    handoff
  obtain ⟨envelope, coreEq, nonempty⟩ :=
    handoffEnvelope_of_separatorHandoffAt avoids cubic degenerate packing produced
  let piece := object.pieceSupport
    (object.remainderSupport packing) component
  have inside : piece ⊆
      object.remainderSupport packing :=
    object.pieceSupport_subset
      (object.remainderSupport packing) component
  have coreInside : envelope.core ⊆
      object.remainderSupport packing := by
    intro vertex member
    exact inside (by simpa [piece, coreEq] using member)
  have normalized := normalized
  have windowFree :
      handoffWindowFree data object envelope.core := by
    constructor
    · intro window subset windowInduces
      exact (normalized packing valid maximal window
        (subset.trans coreInside)).1 windowInduces
    · intro internal subset
      exact (normalized packing valid maximal internal
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
  have high : ∀ centre ∈ envelope.decorations,
      Graph.IsHighCentre object data.threshold centre := by
    intro centre member
    simpa [Graph.IsHighCentre] using
      envelope.decorations_high centre member
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
    noCompression, noDelocalization,
    ⟨envelope, coreEq, nonempty, high,
      fun centre member =>
        ⟨envelope.assigned_nonempty centre member,
          envelope.assigned_adj centre member⟩,
      admissible⟩⟩


/-- The decorated handoff enters node `[65]` with the envelope decorations as its
assigned centres (`def:typeB-assigned-ledger`). -/
theorem typeBFanEntry_of_decoratedHandoff
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (handoff : TypeAExitSevenHandoffStatement data object) :
    TypeBFanEntryStatement data object := by
  apply Or.inl
  obtain ⟨packing, _canonical, valid, maximal, component, present, negative, zero,
    _receiver, _isReceiver, _peeled, _peeledSubset, _saturated, _noExitFour,
    _noCompression, _noDelocalization, produced⟩ :=
    handoff
  obtain ⟨envelope, coreEq, nonempty⟩ :=
    handoffEnvelope_of_separatorHandoffAt avoids cubic degenerate packing produced
  refine ⟨packing, valid, maximal, component, present, envelope.decorations,
    Or.inr ⟨negative, zero, envelope, coreEq, rfl, nonempty,
      fun centre member =>
        ⟨envelope.assigned_nonempty centre member,
          envelope.assigned_adj centre member⟩⟩,
    nonempty, fun centre member => ?_⟩
  simpa [Graph.IsHighCentre] using
    envelope.decorations_high centre member


set_option maxHeartbeats 8000000 in
/-- `lem:absorbed-germ-fan-data` (ii): the first high centre of every retained
corridor, with the connected first-failure prefix as core, is an admissible
decorated handoff and enters node `[65]`. -/
theorem typeBFanEntry_of_absorbedGermFanData
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (three : 3 ≤ data.threshold)
    (degenerate : ¬ data.LengthOK 2) :
    TypeBFanEntryStatement data object := by
  classical
  letI : FinEnum object.Vertex :=
    object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableRel object.graph.Adj :=
    object.decideAdj
  change TypeBFanEntryStatement data object
  apply Or.inr
  apply Or.inl
  simp only [AbsorbedGermDecoratedAssignedSupportStatement]
  change AbsorbedGermFanDataStatement data object at fanData
  simp only [AbsorbedGermFanDataStatement] at fanData
  obtain ⟨routing, _incidence, _candidates, _disjointFamily,
      _corridorLoss, _familyWitness, fanData⟩ := fanData
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
  let stateBundle := Classical.choose_spec stateFour
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
    exact (corridor.prefixSupport_subset_component traceEnd).trans
      (stateBundle.2.2.2.1 routed)
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
  have packingSpec := Classical.choose_spec
    (object.exists_windowPacking_card_eq data.windowOrder)
  have packingMaximal : ∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
        ∃ member ∈ canonicalWindowPacking data object,
          ¬ Disjoint window member := by
    intro window induced
    exact object.exists_mem_not_disjoint_of_card_eq
      data.windowOrder_pos packingSpec.1 packingSpec.2 induced
  have coreSafe : handoffWindowFree data object core := by
    constructor
    · intro window subset induced
      exact (normalized (canonicalWindowPacking data object)
        packingSpec.1 packingMaximal window
          (subset.trans coreInside)).1 induced
    · intro internal subset
      exact (normalized (canonicalWindowPacking data object)
        packingSpec.1 packingMaximal internal
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


/-- The same-token handoff enters node `[65]` with its envelope core and
decorations. -/
theorem typeBFanEntry_of_sameTokenHandoff
    (handoff : SameTokenTypeBHandoffStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_active, capacity, _activationEq, _cubic, _certified, _token,
      _role, _tokenMem, _positive, _excess, _forced, _sourceClass,
      _classified, _root, _rootEq, routed⟩ := handoff
  have envelopeOf :
      ∀ envelope : Graph.DecoratedHandoff.Envelope
          object data.LengthOK
          (handoffHighDegree data object)
          (handoffAbsorbing data object capacity.packing),
        envelope.decorations.Nonempty →
          SameTokenTypeBHandoffEnvelopeStatement data
            object :=
    fun envelope decorated =>
      ⟨capacity.packing, capacity.packingValid, capacity.packingMaximal,
        envelope.core, envelope, rfl, decorated⟩
  apply Or.inr
  apply Or.inr
  rcases routed with ⟨_pattern, _subset, _shape, _routed, source⟩ |
      ⟨_centre, _pattern, _subset, _shape, _routed, source⟩ <;>
  · exact
      match source with
      | ⟨_p, _hp, _q, _hq, _pq, _dp, _hdp, _dq, _hdq, _label, _rp,
          _rq, _validP, _validQ, _maximal, _h, _a, _b, _common, _tailP,
          _tailQ, _decompP, _decompQ, _different, _armP, _armQ, _entryP,
          _entryQ, _adjP, _adjQ, _issuedP, _issuedQ, _chainP, _chainQ,
          _nodupP, _nodupQ, _landsP, _landsQ, _interiorP, _interiorQ,
          _high, _avoids, _denied, _deniedSwap, envelope, envelopeEq,
          _escape⟩ =>
        envelopeOf envelope (by
          rw [envelopeEq]
          simp [Graph.DecoratedHandoff.envelopeOfFirstSeparator])


end Hypostructure.Graph.Contracts.TypeB
