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
  exact Or.inl ⟨piece, _, Or.inl lane,
    ⟨centre, Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩,
    TypeBOrdinaryLane.high lane⟩

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
  exact Or.inl ⟨core, centres, Or.inr (Or.inl lane),
    ⟨separator, by simp [centresEq]⟩, TypeBDecoratedLane.high lane⟩

/-- **Node `[65]`, ordinary entry**, read from the assigned support
(`def:typeB-assigned-ledger`, `def:canonical-decomp`): the ordinary support
`(X₀, H(X₀))` enters with its own high centres, one of which exists. -/
theorem typeBFanEntry_of_assignedSupport
    (assigned : TypeBAssignedSupportStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨core, centres, lane, _negative, centre, member, high⟩ := assigned
  obtain ⟨_piece, centresEq⟩ := ordinarySupport_eq_some lane.2.1
  exact Or.inl ⟨core, centres, Or.inl lane,
    ⟨centre, centresEq ▸ Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩,
    TypeBOrdinaryLane.high lane⟩

/-- **Node `[65]`, decorated entry**, read from the decorated assigned support
(`def:decorated-fan-envelope`): the decoration `{z}` enters as the assigned
centres. -/
theorem typeBFanEntry_of_decoratedAssignedSupport
    (assigned : TypeBDecoratedAssignedSupportStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_core, _centres, lane, _rest⟩ := assigned
  exact typeBFanEntry_of_decoratedLane lane

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
/-- `lem:absorbed-germ-fan-data` (ii) (node `[177]`, yes arm): at a selected
half-edge `ε` of G, if a counted remainder core `Y` exists at the first heavy
centre `z` of `ε`'s retained corridor (`AbsorbedRemainderCoreAt`), then the two
corridor segments at `z` are the arms of an admissible decorated handoff
envelope `(Y, {z})` (the paper's `lem:typeA-high-degree-handoff`
configuration).  Everything is proved from G's facts: the incidences are
distinct neighbours of `z`, the segments are simple walks avoiding `z`, the
arms are cut at their first entry into `Y`, and the fan-safe and admissibility
clauses come from the counterexample and node `[14]`/`[25]`--`[27]`. -/
theorem absorbedHandoffAt_of_remainderCore
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (degenerate : ¬ data.LengthOK 2)
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (firstIndex : (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).Segment)
    (firstBound : firstIndex.1 ≤ coldRoutedTraceEnd data object routing epsilon)
    (high : data.threshold < object.degree
      ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head firstIndex))
    (earlierBound : ∀ earlier : (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).Segment,
      earlier.1 < firstIndex.1 →
        object.degree ((coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head earlier) ≤
          data.threshold)
    (neighboursCubic : ∀ neighbour : object.Vertex,
      object.graph.Adj ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head firstIndex)
          neighbour →
        object.degree neighbour = data.threshold)
    (coreAt : AbsorbedRemainderCoreAt data object routing epsilon firstIndex) :
    ∃ handoff, AbsorbedHandoffAt data object routing epsilon handoff := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let classified := coldRoutedClassified data object routing
  let corridor := coldOccurrenceCorridorAt data object classified epsilon
  let centre := corridor.head firstIndex
  change data.threshold < object.degree centre at high
  change (∀ neighbour : object.Vertex,
    object.graph.Adj centre neighbour →
      object.degree neighbour = data.threshold) at neighboursCubic
  obtain ⟨core, connected, coreInside, centreOut, meetsEntry, meetsExit⟩ :=
    coreAt
  have outside : Graph.ColdCorridor.IsOutsideComponent object
      (coldCorridorWindows data object)
      (coldOccurrenceComponentAt data object classified epsilon) :=
    (coldOccurrenceStateFacts data object classified epsilon).1
  let i := firstIndex.1
  have iLe : i ≤ corridor.inside.1.length := Nat.lt_succ_iff.mp firstIndex.2
  have centreAt : centre = corridor.vertexAt i := rfl
  let entry := corridor.entryNeighbour i
  let exit := corridor.exitNeighbour i
  have different : entry ≠ exit :=
    corridor.entryNeighbour_ne_exitNeighbour outside iLe
  let assigned : Finset object.Vertex := {entry, exit}
  let tail : object.Vertex → List object.Vertex := fun first =>
    if first = entry then corridor.entryTail i else corridor.exitTail i
  have tailEntry : tail entry = corridor.entryTail i := if_pos rfl
  have tailExit : tail exit = corridor.exitTail i := if_neg different.symm
  have cases' : ∀ first ∈ assigned, first = entry ∨ first = exit := by
    intro first member
    simpa [assigned] using member
  have denied : ∀ c a b,
      ¬ handoffAbsorbing data object
        (canonicalWindowPacking data object) c a b :=
    fun _ _ _ collision => avoids
      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        degenerate collision)
  have adjacent : ∀ first ∈ assigned, object.graph.Adj centre first := by
    intro first member
    rcases cases' first member with rfl | rfl
    · exact corridor.adj_entryNeighbour iLe
    · exact corridor.adj_exitNeighbour iLe
  let envelope := Graph.DecoratedHandoff.envelopeOfTails data.LengthOK
    (handoffHighDegree data object)
    (handoffAbsorbing data object (canonicalWindowPacking data object))
    core centre high assigned ⟨entry, by simp [assigned]⟩ adjacent tail
    (by
      intro first member
      rcases cases' first member with rfl | rfl
      · rw [tailEntry]; exact corridor.entryTail_head? i
      · rw [tailExit]; exact corridor.exitTail_head? i)
    (by
      intro first member
      rcases cases' first member with rfl | rfl
      · rw [tailEntry]; exact corridor.entryTail_isChain i iLe
      · rw [tailExit]; exact corridor.exitTail_isChain i iLe)
    (by
      intro first member
      rcases cases' first member with rfl | rfl
      · rw [tailEntry]; exact corridor.entryTail_nodup outside i iLe
      · rw [tailExit]; exact corridor.exitTail_nodup outside i iLe)
    (by
      intro first member
      rcases cases' first member with rfl | rfl
      · rw [tailEntry, centreAt]; exact corridor.vertexAt_not_mem_entryTail outside iLe
      · rw [tailExit, centreAt]; exact corridor.vertexAt_not_mem_exitTail outside iLe)
    (by
      intro first member
      rcases cases' first member with rfl | rfl
      · rw [tailEntry]; exact meetsEntry
      · rw [tailExit]; exact meetsExit)
    (by
      intro first firstMember second secondMember different'
      exact ⟨Graph.DecoratedHandoff.fanSafe_geometric
          (adjacent first firstMember) (adjacent second secondMember)
          different' avoids,
        denied centre first second⟩)
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
  refine ⟨(centre, core), firstIndex, rfl, firstBound, high, earlierBound,
    neighboursCubic, connected, coreInside, centreOut, different, envelope, rfl, rfl,
    rfl, ?_, ?_, ?_, admissible⟩
  · change Graph.DecoratedHandoff.firstEntryArm core (tail entry) = _
    rw [tailEntry]
  · change Graph.DecoratedHandoff.firstEntryArm core (tail exit) = _
    rw [tailExit]
  · exact Graph.DecoratedHandoff.centre_not_mem_arm_envelopeOfTails (object := object)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _



/-- **Node `[175]`, read at `[177]`**: some selected corridor meets a
high-degree vertex (`G`'s canonical absorbed half-edge exists), or every
selected corridor is subcubic.  The two arms are the two values of the one
canonical object `canonicalTypeBAbsorbedHalfEdge`. -/
theorem typeBAbsorbedHalfEdge_split
    (_fanData : AbsorbedGermFanDataStatement data object) :
    TypeBAbsorbedHalfEdgeStatement data object ∨
      TypeBAbsorbedHalfEdgeAbsentStatement data object := by
  cases selected : canonicalTypeBAbsorbedHalfEdge data object with
  | none => exact Or.inr selected
  | some epsilon => exact Or.inl ⟨epsilon, selected⟩

/-- The least high index of a corridor is unique: two heavy indices whose
earlier indices are all at the baseline coincide. -/
theorem absorbedFirstIndex_unique
    {routing : ColdFailureRoutingStatement data object}
    {epsilon : ColdEligibleHalfEdge data object}
    {first second : (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).Segment}
    (firstHigh : data.threshold < object.degree
      ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head first))
    (firstEarlier : ∀ earlier : (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).Segment,
      earlier.1 < first.1 →
        object.degree ((coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head earlier) ≤
          data.threshold)
    (secondHigh : data.threshold < object.degree
      ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head second))
    (secondEarlier : ∀ earlier : (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).Segment,
      earlier.1 < second.1 →
        object.degree ((coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head earlier) ≤
          data.threshold) :
    first = second := by
  rcases lt_trichotomy first.1 second.1 with lt | eq | gt
  · exact absurd (secondEarlier first lt) (not_le.mpr firstHigh)
  · exact Fin.ext eq
  · exact absurd (firstEarlier second gt) (not_le.mpr secondHigh)

/-- **Node `[177]`'s test is the existence of the counted core.**  At G's
canonical absorbed half-edge `ε` (outside node `[153]`'s candidates, with the
`[175]` fan data), the canonical absorbed handoff of `ε` is defined exactly
when a counted remainder core exists at `ε`'s heavy centre. -/
theorem canonicalAbsorbedHandoff_isSome_iff_core
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (degenerate : ¬ data.LengthOK 2)
    (fanData : AbsorbedGermFanDataStatement data object)
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (notCandidate : Sum.inl epsilon ∉ coldRoutedCandidates data object routing)
    (firstIndex : (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).Segment)
    (high : data.threshold < object.degree
      ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).head firstIndex))
    (earlierBound : ∀ earlier : (coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).Segment,
      earlier.1 < firstIndex.1 →
        object.degree ((coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).head earlier) ≤
          data.threshold) :
    (canonicalAbsorbedHandoff data object epsilon).isSome ↔
      AbsorbedRemainderCoreAt data object routing epsilon firstIndex := by
  classical
  constructor
  · intro isSome
    obtain ⟨handoff, handoffEq⟩ := Option.isSome_iff_exists.mp isSome
    obtain ⟨_routing', handoffAt⟩ :=
      canonicalAbsorbedHandoff_spec_of_eq_some handoffEq
    obtain ⟨index, centreEq, _bound, indexHigh, indexEarlier, _cubic,
      connected, inside, centreOut, _different, envelope, coreEq, decorationsEq,
      assignedEq, entryArm, exitArm, _simple, _admissible⟩ := handoffAt
    have same : index = firstIndex :=
      absorbedFirstIndex_unique (routing := routing)
        (by rw [← centreEq]; exact indexHigh) indexEarlier high earlierBound
    subst same
    have centreMem : handoff.1 ∈ envelope.decorations := by
      rw [decorationsEq]; exact Finset.mem_singleton_self _
    have lands : ∀ first ∈ envelope.assigned handoff.1, ∀ tail : List object.Vertex,
        (∀ vertex ∈ envelope.arm handoff.1 first, vertex ∈ tail) →
        ∃ vertex ∈ tail, vertex ∈ handoff.2 := by
      intro first member tail sub
      obtain ⟨terminal, lastEq, terminalIn⟩ :=
        envelope.arm_lands handoff.1 centreMem first member
      exact ⟨terminal, sub _ (List.mem_of_getLast? lastEq), coreEq ▸ terminalIn⟩
    refine ⟨handoff.2, connected, inside, centreEq ▸ centreOut,
      lands ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).entryNeighbour index.1)
        ?_ _ ?_,
      lands ((coldOccurrenceCorridorAt data object
        (coldRoutedClassified data object routing) epsilon).exitNeighbour index.1)
        ?_ _ ?_⟩
    · rw [assignedEq]; simp
    · intro vertex member
      rw [entryArm] at member
      exact List.mem_of_mem_take member
    · rw [assignedEq]; simp
    · intro vertex member
      rw [exitArm] at member
      exact List.mem_of_mem_take member
  · intro coreAt
    change AbsorbedGermFanDataStatement data object at fanData
    simp only [AbsorbedGermFanDataStatement] at fanData
    obtain ⟨_routing', fanData⟩ := fanData
    obtain ⟨index, bound, indexHigh, indexEarlier, neighboursCubic⟩ :=
      fanData epsilon notCandidate
    have same : index = firstIndex :=
      absorbedFirstIndex_unique (routing := routing) indexHigh indexEarlier high
        earlierBound
    subst same
    obtain ⟨_, handoffEq, _⟩ := canonicalAbsorbedHandoff_spec routing
      (absorbedHandoffAt_of_remainderCore avoids uncompressible normalized
        degenerate routing epsilon index bound indexHigh indexEarlier
        neighboursCubic coreAt)
    simp [handoffEq]

/-- **Node `[177]`'s decision** at G's canonical absorbed half-edge `ε` (the
`[175]` yes arm): the counted remainder core at `ε`'s heavy centre exists (the
canonical absorbed handoff is defined) or it does not. -/
theorem absorbedHandoffCore_split
    (outside : TypeBAbsorbedHalfEdgeStatement data object) :
    AbsorbedHandoffCoreStatement data object ∨
      AbsorbedHandoffCoreAbsentStatement data object := by
  obtain ⟨epsilon, edgeEq⟩ := outside
  cases handoffEq : canonicalAbsorbedHandoff data object epsilon with
  | none => exact Or.inr ⟨epsilon, edgeEq, handoffEq⟩
  | some handoff => exact Or.inl ⟨epsilon, edgeEq, by simp [handoffEq]⟩

/-- **Node `[177]`, the charge of every discarded half-edge with a counted core**
(`lem:absorbed-germ-fan-data`: "every half-edge it discards is charged to the
Type B ledger"): every selected half-edge `ε` outside the subcubic candidates
whose canonical absorbed handoff `(z_ε, Y_ε)` is defined (the `[177]` yes
configuration at `ε`) has its own pinned absorbed Type B support
`(Y_ε, H_ε)`, `H_ε = {z_ε} ∪ centres(Y_ε)` (`def:typeB-assigned-ledger`), and
that support's negative part is charged to the surplus of `H_ε`
(`lem:typeB-bridge-deficit-bound`).  A half-edge without a counted core is
charged by the (F4) count instead (`absorbedF4Charge`). -/
theorem typeBAbsorbedCharge
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale) :
    TypeBAbsorbedChargeStatement data object := by
  classical
  intro epsilon _outside centre core handoffEq
  obtain ⟨high, inside⟩ := absorbedHandoff_facts handoffEq
  refine ⟨?_, high, inside, ?_⟩
  · simp [canonicalTypeBAbsorbedSupportAt, handoffEq]
  · intro residual
    exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound_assigned object core
      _ massSlack baseline centres_subset_absorbedAssignedCentres residual

/-- Node `[177]`, yes arm: at `G`'s canonical absorbed half-edge `ε`, whose
canonical absorbed handoff `(z, Y)` is defined, its pinned charge
(`typeBAbsorbedCharge`) gives the absorbed Type B support
`(Y, {z} ∪ centres(Y))`: the counted remainder core of its canonical envelope
`(Y, {z})` and its assigned fan centres. -/
theorem typeBAbsorbedLane_of_core
    (fails : ExactCollisionFailsStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (charge : TypeBAbsorbedChargeStatement data object)
    (core : AbsorbedHandoffCoreStatement data object) :
    ∃ core centres, TypeBAbsorbedLane data object core centres := by
  classical
  obtain ⟨epsilon, edgeEq, isSome⟩ := core
  obtain ⟨⟨centre, core⟩, handoffEq⟩ := Option.isSome_iff_exists.mp isSome
  obtain ⟨supportEq, _facts⟩ :=
    charge epsilon (canonicalChoice_spec_of_eq_some edgeEq) centre core handoffEq
  refine ⟨core, absorbedAssignedCentres data object centre core, fails, fanData, ?_⟩
  simp [canonicalTypeBAbsorbedSupport, edgeEq, supportEq]

/-- **Node `[177]`, no arm: the (F4) charge** (user-approved extension of the
cold (F4) exact-count repair).  At `G`'s canonical absorbed half-edge `ε` with
no counted core, on node `[219]`'s canonical extraction: no counted remainder
core exists at `ε`'s heavy centre, `ε` is one of the corridor-loss units (it is
not a candidate, and the non-candidates number exactly the corridor loss), and
the corridor loss is within `(δ+1)·B_cold·σ(G)`. -/
theorem absorbedF4Charge
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (degenerate : ¬ data.LengthOK 2)
    (fanData : AbsorbedGermFanDataStatement data object)
    (germCandidates : ColdGermCandidatesStatement data object)
    (absent : AbsorbedHandoffCoreAbsentStatement data object) :
    AbsorbedF4ChargeStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨epsilon, edgeEq, handoffNone⟩ := absent
  obtain ⟨routing, notCandidate⟩ := canonicalChoice_spec_of_eq_some edgeEq
  obtain ⟨extraction, extractionEq, _routing', witness⟩ :=
    coldGermExtraction?_spec_of_candidates data object germCandidates
  simp only [ColdGermFamilyWitness] at witness
  obtain ⟨_incidenceEq, _candidatesEq, _family, _extracted, _charged, total,
    _selected, lossBound, _quantitative⟩ := witness
  refine ⟨epsilon, edgeEq, handoffNone, routing, ?_, extraction, extractionEq,
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notCandidate⟩, ?_, lossBound⟩
  · intro firstIndex _bound high earlier coreAt
    have isSome := (canonicalAbsorbedHandoff_isSome_iff_core avoids uncompressible
      normalized degenerate fanData routing epsilon notCandidate firstIndex high
      earlier).2 coreAt
    rw [handoffNone] at isSome
    exact Bool.false_ne_true isSome
  · have := Finset.card_sdiff_add_card_inter
      (Finset.univ : Finset (ColdGermOccurrence data object))
      (coldRoutedCandidates data object routing)
    rw [Finset.univ_inter] at this
    omega

/-- Node `[177]` → `[65]`: the absorbed Type B support enters the common Type B
entry with its assigned high centres, `z` among them. -/
theorem typeBFanEntry_of_absorbedLane {core centres : Finset object.Vertex}
    (lane : TypeBAbsorbedLane data object core centres) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_epsilon, _edgeEq, supportAt⟩ := absorbedSupport_eq_some lane.2.2
  obtain ⟨centre, _handoffEq, rfl⟩ := absorbedSupportAt_eq_some supportAt
  exact Or.inl ⟨core, _, Or.inr (Or.inr lane),
    ⟨centre, centre_mem_absorbedAssignedCentres⟩, TypeBAbsorbedLane.high lane⟩

/-- Node `[175]` yes → `[177]` yes → `[65]`. -/
theorem typeBFanEntry_of_absorbedCore
    (fails : ExactCollisionFailsStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (charge : TypeBAbsorbedChargeStatement data object)
    (core : AbsorbedHandoffCoreStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_core, _centres, lane⟩ :=
    typeBAbsorbedLane_of_core fails fanData charge core
  exact typeBFanEntry_of_absorbedLane lane

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
