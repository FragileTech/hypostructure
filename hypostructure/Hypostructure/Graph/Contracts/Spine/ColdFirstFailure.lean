import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.CanonicalSurplus
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Statements.ColdResiduals

/-!
# Contracts: the cold-corridor first failure `[153]`

Proof-agnostic contract lemmas for `lem:cold-corridor-first-failure` and the
exchange/extraction step of `lem:cold-germ-extraction`.  Each lemma is stated
over a `Graph.FiniteObject` with the registered `Parameters` as a parameter and
every paper hypothesis explicit; its conclusion is exactly the statement of the
fact it proves.  This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **(F1) never occurs.**  An (F1) completion is a target cycle of the object;
an object avoiding the target has none. -/
theorem coldFailureCycle_of_avoids
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    ColdFailureCycleStatement data object := by
  intro _occurrence _epsilon _segment ⟨_member, _memberMem, _window, _placed, failure⟩
  exact avoids
    (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
      failure)

/-- **(F3) never occurs.**  An (F3) pair, read at G, is a target-complete
compression of a proper support (its replacement glued into G's surroundings
`G − J` has the baseline, is smaller, and has G's target response there, so no
target cycle), which `cor:uncompressible` forbids. -/
theorem coldFailureCompression_of_uncompressible
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object) :
    ColdFailureCompressionStatement data object := by
  intro _occurrence _epsilon _segment ⟨failure, _stage⟩
  exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant avoids
    (fun support compressible => uncompressible support compressible) ⟨failure⟩

/-- **The ordered first failure.**  On the retained cold corridor state, with
the declared handoff registry `ColdDeclaredHandoffSupport`, every eligible half-edge has a first event
in the ordered (F1)--(F5) list: the germ event of the state witnesses that the
set of failing segments is nonempty, and its minimum is the first failure. -/
theorem coldFirstFailureOccurrence_of_state
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (state : ColdCorridorStateStatement data object) :
    ColdFirstFailureOccurrenceStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  refine ⟨⟨state, ?_⟩⟩
  intro Eligible incidence stateOne componentAt stateTwo corridorAt stateTail
    presentationAt indexAt epsilon
  let indexTail := Classical.choose_spec stateTail
  let stateFacts := (Classical.choose_spec indexTail).1
  let germ := incidence epsilon
  let corridor := corridorAt epsilon
  let presentation := presentationAt epsilon
  let index := indexAt epsilon
  let packing := canonicalWindowPacking data object
  let cycleAt : corridor.Segment → Prop := fun segment =>
    ∃ windowSupport ∈ packing,
      ∃ window : Graph.ColdCorridor.Window object data.windowOrder,
        (∀ vertex, vertex ∈ windowSupport ↔
          ∃ position, window.place position = vertex) ∧
        corridor.FirstFailureCycle window data.LengthOK segment
  let defectAt : corridor.Segment → Prop := fun segment =>
    ∃ left : corridor.Segment,
      left.1 < segment.1 ∧
        Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation
          index (Graph.HasCycleWithLength data.LengthOK)
          (fun stage => corridor.prefixSupport stage.1) left segment
  let compressionAt : corridor.Segment → Prop := fun segment =>
    ∃ failure : Graph.ColdCorridor.Corridor.FirstFailureCompression corridor
        presentation index (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK)
        (fun stage => corridor.prefixSupport stage.1),
      failure.stage = segment
  let handoffAt : corridor.Segment → Prop := fun segment =>
    Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor
      (ColdDeclaredHandoffSupport data object) segment
  let germAt : corridor.Segment → Prop := fun segment =>
    (corridor.TerminalCorridor data.coldSignature ∧
      germ.support = corridor.prefixSupport corridor.statesRead ∧
      (let terminal : corridor.Segment :=
        ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
       germ.record = corridor.recordAt presentation index terminal) ∧
      segment.1 = corridor.inside.1.length) ∨
    ∃ left right : corridor.Segment,
      right.1 ≤ Graph.ColdCorridor.stateBound data.coldSignature ∧
      left.1 < right.1 ∧
      presentation.state (index left) = presentation.state (index right) ∧
      (∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
        presentation.support (index left) coordinate ⊆
            ↑(presentation.activeInterface (index left)) →
          presentation.reading (index left) coordinate =
            presentation.reading (index right) coordinate) ∧
      (∀ earlierLeft earlierRight : corridor.Segment,
        earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
          presentation.state (index earlierLeft) ≠
            presentation.state (index earlierRight)) ∧
      germ.support = corridor.intervalSupport left right ∧
      germ.record = corridor.recordAt presentation index left ∧
      germ.record = corridor.recordAt presentation index right ∧
      segment = right
  let failureAt : corridor.Segment → Prop := fun segment =>
    ColdFirstFailureEvent data object corridor presentation index germ
      (ColdDeclaredHandoffSupport data object) segment
  change ∃ first : corridor.Segment,
    failureAt first ∧
      ∀ earlier : corridor.Segment, earlier.1 < first.1 →
        ¬ failureAt earlier
  have germWitness : corridor.FirstFailureGermWitness
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      presentation index germ :=
    (stateFacts epsilon).2.2.2
  have germEvent : ∃ segment : corridor.Segment, germAt segment := by
    rcases germWitness.2.2 with terminal | repeated
    · let segment : corridor.Segment :=
        ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
      exact ⟨segment, Or.inl
        ⟨terminal.1, terminal.2.1, terminal.2.2, rfl⟩⟩
    · obtain ⟨left, right, rightBound, before, same, readings, first,
        supportEq, leftRecord, rightRecord⟩ := repeated
      exact ⟨right, Or.inr
        ⟨left, right, rightBound, before, same, readings, first,
          supportEq, leftRecord, rightRecord, rfl⟩⟩
  let failures : Finset corridor.Segment :=
    Finset.univ.filter failureAt
  have failuresNonempty : failures.Nonempty := by
    obtain ⟨segment, event⟩ := germEvent
    exact ⟨segment, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      .germ event⟩⟩
  let first := failures.min' failuresNonempty
  have firstMember : first ∈ failures :=
    Finset.min'_mem failures failuresNonempty
  refine ⟨first, (Finset.mem_filter.1 firstMember).2, ?_⟩
  intro earlier earlierBefore earlierFailure
  have earlierMember : earlier ∈ failures :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, earlierFailure⟩
  have firstLeEarlier := Finset.min'_le failures earlier earlierMember
  exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore

/-- The target of G accepts every dyadic length `2^k`, `k ≥ 2`, read from the
presentation identity `LengthOK ↔ PowerOfTwoLength` (`K .cubicBaseline`). -/
theorem lengthOK_twoPow (data : Parameters)
    (dyadic : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    ∀ k, 2 ≤ k → data.LengthOK (2 ^ k) := fun k two =>
  (dyadic _).2 ⟨⟨k, by have := Nat.lt_two_pow_self (n := k); omega⟩, two, rfl⟩

/-- **(F2) is decided at G** (`lem:cold-corridor-first-failure` (ii), read at
G): no segment of any corridor of G carries (F2), because G's two readings of a
prefix, glued into G's own surroundings, are subgraphs of G and G avoids the
target (`Graph.ColdCorridor.Corridor.not_firstFailureDefect`). -/
theorem not_coldFirstFailureDefectAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (right : corridor.Segment) :
    ¬ ColdFirstFailureDefectAt data object corridor presentation index right := by
  rintro ⟨left, _lt, defect⟩
  exact Graph.ColdCorridor.Corridor.not_firstFailureDefect avoids corridor presentation
    index (fun stage => corridor.prefixSupport stage.1) left right defect

/-- **Node `[153]`, `lem:cold-corridor-first-failure` (ii), read at G** (tex
7240, 7265-7270): no segment of G's retained corridor of any selected
half-edge carries (F2).  Lean improvement: the (F2) arm is empty at G. -/
theorem coldFailureDefectRoutes_of_avoids (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    ColdFailureDefectRoutesStatement data object :=
  fun occurrence epsilon segment =>
    not_coldFirstFailureDefectAt data object avoids
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (coldOccurrencePresentationAt data object occurrence epsilon)
      (coldOccurrenceIndexAt data object occurrence epsilon) segment

/-- **The pinned cut state reads G's degree at the head.**  On a presentation
pinned to `coldCutStatePresentation` (the `Sigma` equation of `[30]`), the head
entry of the boundary-degree profile of segment `s` is `min (d_G(head s)) D`. -/
theorem pinned_headBoundaryDegree (data : Parameters) (object : Graph.FiniteObject.{u})
    {component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object (coldCorridorWindows data object)
      component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (pin : (⟨presentation, index⟩ : Σ p : Graph.ColdCorridor.Presentation
        data.coldSignature object, corridor.Segment → p.Segment) =
      ⟨coldCutStatePresentation data object corridor, fun segment => ULift.up segment⟩)
    (segment : corridor.Segment) :
    ((presentation.state (index segment)).boundaryDegrees 1).1 =
      min (object.degree (corridor.head segment)) data.coldSignature.degreeBound := by
  cases pin
  rfl

set_option maxHeartbeats 1600000 in
/-- **The residual of `[153]`, constructed at G.**  If (★) fails at G, some
retained corridor of G has two equal pinned states at segments up to a segment
with no earlier event.  Take the least `right` carrying an earlier equal state
and such a `left`: `(left, right)` is G's first equal-state pair, no event
precedes `right`, G's two readings of `J_right` are profile-separated
(`ColdEqualStates.prefix_profile_ne`), and the glue vertices `head left`,
`head right` carry the same capped G-degree (through the `[30]` pin,
`pinned_headBoundaryDegree`).  The residual is read at G's canonical witness
`coldRepeatWitness?`. -/
theorem coldRepeatedStateResidual_of_not_distinct (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (repeated : ¬ ColdCutStatesDistinctStatement data object) :
    ColdRepeatedStateResidualStatement data object := by
  classical
  unfold ColdCutStatesDistinctStatement at repeated
  push Not at repeated
  obtain ⟨occurrence, epsilon, first, minimal, left₀, right₀, lt₀, le₀, same₀⟩ :=
    repeated
  let corridor := coldOccurrenceCorridorAt data object occurrence epsilon
  let presentation := coldOccurrencePresentationAt data object occurrence epsilon
  let index := coldOccurrenceIndexAt data object occurrence epsilon
  let repeats : Finset corridor.Segment := Finset.univ.filter fun right =>
    ∃ left : corridor.Segment, left.1 < right.1 ∧
      presentation.state (index left) = presentation.state (index right)
  have nonempty : repeats.Nonempty :=
    ⟨right₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, left₀, lt₀, same₀⟩⟩
  let right := repeats.min' nonempty
  have rightMem := (Finset.mem_filter.1 (repeats.min'_mem nonempty)).2
  obtain ⟨left, lt, same⟩ := rightMem
  have rightLe : right ≤ right₀ :=
    repeats.min'_le right₀ (Finset.mem_filter.2 ⟨Finset.mem_univ _, left₀, lt₀, same₀⟩)
  have rightLeFirst : right.1 ≤ first.1 := le_trans (Fin.le_def.1 rightLe) le₀
  have outside :=
    (coldOccurrenceStateFacts data object occurrence epsilon).1
  have noEvent : ∀ earlier : corridor.Segment, earlier.1 < right.1 →
      ¬ ColdFirstFailureEvent data object corridor presentation index
        (coldOccurrenceIncidence data object occurrence epsilon)
        (ColdDeclaredHandoffSupport data object) earlier :=
    fun earlier before => minimal earlier (by omega)
  have spec : ColdRepeatedStateSpecAt data object occurrence epsilon left right := by
    refine ⟨outside, lt, same, ?_, noEvent, ?_, ?_, ?_⟩
    · intro earlierLeft earlierRight earlierLt earlierBefore earlierSame
      have before : earlierRight.1 < right.1 := earlierBefore
      have member : earlierRight ∈ repeats :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, earlierLeft, earlierLt, earlierSame⟩
      have := repeats.min'_le earlierRight member
      exact absurd (Fin.le_def.1 this) (by omega)
    · exact Graph.ColdEqualStates.prefix_profile_ne outside corridor left right lt
    · exact congrArg Graph.ColdCorridor.CutState.boundaryDegrees same
    · have pin := ((coldOccurrenceStateFacts data object occurrence epsilon).2.2.1).2
      have degrees := congrArg
        (fun state : Graph.ColdCorridor.CutState data.coldSignature =>
          (state.boundaryDegrees 1).1) same
      exact (pinned_headBoundaryDegree data object _ _ _ pin left).symm.trans
        (degrees.trans (pinned_headBoundaryDegree data object _ _ _ pin right))
  obtain ⟨witness, pinned⟩ := coldRepeatWitness?_eq_some
    ⟨⟨occurrence, epsilon, left, right⟩, spec⟩
  exact ⟨witness, pinned, coldRepeatWitness?_spec pinned⟩

/-- **The `[153]` residual refutes (★).**  Its witness carries an equal-state
pair `left < right` with no event before `right`. -/
theorem not_distinct_of_coldRepeatedStateResidual (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (residual : ColdRepeatedStateResidualStatement data object) :
    ¬ ColdCutStatesDistinctStatement data object := by
  intro distinct
  obtain ⟨witness, _, outside, lt, same, _, noEvent, _⟩ := residual
  exact distinct witness.occurrence witness.epsilon witness.right noEvent
    witness.left witness.right lt le_rfl same

/-- **`lem:cold-corridor-first-failure`, the routing** (tex 7234-7295): (F1)
is a target cycle and (F3) a target-complete compression, both excluded by the
ledger; (F2) is empty at G (`ColdFailureDefectRoutesStatement`: G's two
readings of a prefix never separate in G's own surroundings); every other first
failure is routed as
the lemma states -- (F5) a cold bounded configuration or (F4) an already named
handoff of the declared registry `ColdDeclaredHandoffSupport` (G's heavy
handoff centres). -/
theorem coldFailureRouting_of_failures
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceStatement data object)
    (failureCycle : ColdFailureCycleStatement data object)
    (failureCompression : ColdFailureCompressionStatement data object)
    (defectRoutes : ColdFailureDefectRoutesStatement data object) :
    ColdFailureRoutingStatement data object := by
  let occurrenceData := Classical.choice occurrence
  refine ⟨⟨occurrenceData, ?_⟩⟩
  intro epsilon
  obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
  cases event with
  | cycle cycle =>
      exact (failureCycle occurrenceData epsilon first cycle).elim
  | defect defect =>
      exact (defectRoutes occurrenceData epsilon first defect).elim
  | compression compression =>
      exact (failureCompression occurrenceData epsilon first compression).elim
  | handoff handoff => exact Or.inr ⟨first, handoff, minimal⟩
  | germ germ => exact Or.inl ⟨⟨first, germ, minimal⟩⟩

/-- **The first-failure exchange is bounded by `M_cold`.** -/
theorem coldExchangeBound_holds
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ColdExchangeBoundStatement data object :=
  ⟨routing, fun epsilon terminal =>
    (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).exchange_card_le terminal⟩

end Hypostructure.Graph.Contracts.Spine
