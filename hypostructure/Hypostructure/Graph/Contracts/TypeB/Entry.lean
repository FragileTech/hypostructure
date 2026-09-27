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
/-- `lem:absorbed-germ-fan-data` (ii) (node `[177]`): at every selected
half-edge `ε` outside the subcubic candidates, the two corridor segments at the
first heavy centre `z` of `ε`'s retained corridor are the arms of an admissible
decorated handoff envelope `(Y, {z})` over the counted remainder core `Y` of
`coldAbsorbedRemainderCore` (the paper's `lem:typeA-high-degree-handoff`
configuration).  Everything except the existence of `Y` is proved here from G's
facts: the incidences are distinct neighbours of `z`, the segments are simple
walks avoiding `z`, the arms are cut at their first entry into `Y`, and the
fan-safe and admissibility clauses come from the counterexample and node
`[14]`/`[25]`--`[27]`. -/
theorem absorbedGermDecoratedAssignedSupport
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (degenerate : ¬ data.LengthOK 2) :
    AbsorbedGermDecoratedAssignedSupportStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp only [AbsorbedGermDecoratedAssignedSupportStatement]
  change AbsorbedGermFanDataStatement data object at fanData
  simp only [AbsorbedGermFanDataStatement] at fanData
  obtain ⟨routing, fanData⟩ := fanData
  refine ⟨routing, ?_⟩
  intro epsilon notCandidate
  obtain ⟨firstIndex, firstBound, high, earlierBound,
      neighboursCubic⟩ := fanData epsilon notCandidate
  let classified := coldRoutedClassified data object routing
  let corridor := coldOccurrenceCorridorAt data object classified epsilon
  let centre := corridor.head firstIndex
  change data.threshold < object.degree centre at high
  change (∀ neighbour : object.Vertex,
    object.graph.Adj centre neighbour →
      object.degree neighbour = data.threshold) at neighboursCubic
  obtain ⟨core, connected, coreInside, centreOut, meetsEntry, meetsExit⟩ :=
    Contracts.Spine.coldAbsorbedRemainderCore data object routing epsilon
      notCandidate firstIndex firstBound high earlierBound
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

/-- **Node `[177]`, the charge of every discarded half-edge**
(`lem:absorbed-germ-fan-data`: "every half-edge it discards is charged to the
Type B ledger"): every selected half-edge outside the subcubic candidates has its
own pinned absorbed Type B support `(Y_ε, H_ε)`, `H_ε = {z_ε} ∪ centres(Y_ε)`
(`def:typeB-assigned-ledger`), and that support's negative part is charged to
the surplus of `H_ε` (`lem:typeB-bridge-deficit-bound`). -/
theorem typeBAbsorbedCharge
    (supports : AbsorbedGermDecoratedAssignedSupportStatement data object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale) :
    TypeBAbsorbedChargeStatement data object := by
  classical
  intro epsilon outside
  obtain ⟨routing, notCandidate⟩ := outside
  obtain ⟨_routing, witnesses⟩ := supports
  obtain ⟨⟨centre, core⟩, handoffEq, _handoff⟩ :=
    canonicalAbsorbedHandoff_spec routing (witnesses epsilon notCandidate)
  obtain ⟨high, inside⟩ := absorbedHandoff_facts handoffEq
  refine ⟨core, centre, ?_, high, inside, ?_⟩
  · simp [canonicalTypeBAbsorbedSupportAt, handoffEq]
  · intro residual
    exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound_assigned object core
      _ massSlack baseline centres_subset_absorbedAssignedCentres residual

/-- Node `[177]`: at `G`'s canonical absorbed half-edge `ε`, which lies outside
the subcubic candidates, its pinned charge (`typeBAbsorbedCharge`) gives the
absorbed Type B support `(Y, {z} ∪ centres(Y))`: the counted remainder core of
its canonical envelope `(Y, {z})` and its assigned fan centres. -/
theorem typeBAbsorbedLane_of_halfEdge
    (fails : ExactCollisionFailsStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (charge : TypeBAbsorbedChargeStatement data object)
    (outside : TypeBAbsorbedHalfEdgeStatement data object) :
    ∃ core centres, TypeBAbsorbedLane data object core centres := by
  classical
  obtain ⟨epsilon, edgeEq⟩ := outside
  obtain ⟨core, centre, supportEq, _facts⟩ :=
    charge epsilon (canonicalChoice_spec_of_eq_some edgeEq)
  refine ⟨core, absorbedAssignedCentres data object centre core, fails, fanData, ?_⟩
  simp [canonicalTypeBAbsorbedSupport, edgeEq, supportEq]

/-- Node `[177]` → `[65]`: the absorbed Type B support enters the common Type B
entry with its assigned high centres, `z` among them. -/
theorem typeBFanEntry_of_absorbedLane {core centres : Finset object.Vertex}
    (lane : TypeBAbsorbedLane data object core centres) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_epsilon, _edgeEq, supportAt⟩ := absorbedSupport_eq_some lane.2.2
  obtain ⟨centre, _handoffEq, rfl⟩ := absorbedSupportAt_eq_some supportAt
  exact Or.inl ⟨core, _, Or.inr (Or.inr lane),
    ⟨centre, centre_mem_absorbedAssignedCentres⟩, TypeBAbsorbedLane.high lane⟩

/-- Node `[175]` yes → `[177]` → `[65]`. -/
theorem typeBFanEntry_of_absorbedHalfEdge
    (fails : ExactCollisionFailsStatement data object)
    (fanData : AbsorbedGermFanDataStatement data object)
    (charge : TypeBAbsorbedChargeStatement data object)
    (outside : TypeBAbsorbedHalfEdgeStatement data object) :
    TypeBFanEntryStatement data object := by
  obtain ⟨_core, _centres, lane⟩ :=
    typeBAbsorbedLane_of_halfEdge fails fanData charge outside
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
