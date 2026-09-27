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

/-- **(F3) never occurs.**  An (F3) pair is a target-complete compression of a
proper support, which `cor:uncompressible` forbids. -/
theorem coldFailureCompression_of_uncompressible
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (uncompressible : UncompressibleStatement data object) :
    ColdFailureCompressionStatement data object := by
  intro _occurrence _epsilon _segment ⟨failure, _stage⟩
  exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
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

/-- **At G, (F2) at a segment is exactly an earlier equal cut state**
(`lem:cold-corridor-first-failure` (ii), tex 7192-7195): the forward direction
is the clause's state equality; conversely, for `left < right` with equal
states, the path context `ColdEqualStates.prefixContext` separates
`retainedPiece J_right J_left` from `piece J_right`, because G has no accepted
cycle. -/
theorem coldFirstFailureDefectAt_iff (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (accept : ∀ k, 2 ≤ k → data.LengthOK (2 ^ k))
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {windows component : Finset object.Vertex}
    (outside : Graph.ColdCorridor.IsOutsideComponent object windows component)
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (right : corridor.Segment) :
    ColdFirstFailureDefectAt data object corridor presentation index right ↔
      ∃ left : corridor.Segment, left.1 < right.1 ∧
        presentation.state (index left) = presentation.state (index right) := by
  constructor
  · rintro ⟨left, lt, same, _⟩
    exact ⟨left, lt, same⟩
  · rintro ⟨left, lt, same⟩
    exact ⟨left, lt, same,
      Graph.ColdEqualStates.prefix_targetDefect data.LengthOK accept avoids outside
        corridor left right lt⟩

/-- **`lem:cold-corridor-first-failure` (ii) on the distinct-states arm of
`[153]`** (tex 7265-7270): when G's pinned cut states along every retained
corridor are pairwise distinct up to the first failure
(`ColdCutStatesDistinctStatement`, the arm where the paper's claim holds), the
first failure of a selected half-edge `ε` of G, read on G's retained
occurrence, is not (F2): an (F2) clause at `first` carries an earlier segment
with the same state. -/
theorem coldFailureDefect_excluded (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (distinct : ColdCutStatesDistinctStatement data object)
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment)
    (minimal : ∀ earlier :
        (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) :
    ¬ ColdFirstFailureDefectAt data object
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (coldOccurrencePresentationAt data object occurrence epsilon)
      (coldOccurrenceIndexAt data object occurrence epsilon) first := by
  rintro ⟨left, lt, same, _⟩
  exact distinct occurrence epsilon first minimal left first lt le_rfl same

/-- **Node `[153]`, `lem:cold-corridor-first-failure` (ii)** (tex 7240,
7265-7270), at G's retained occurrence, on the distinct-states arm: an (F2)
first failure of G's retained corridor is a named sparse surplus exit of G --
vacuously, since on this arm no first failure of G is (F2)
(`coldFailureDefect_excluded`). -/
theorem coldFailureDefectRoutes_of_distinct (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (distinct : ColdCutStatesDistinctStatement data object) :
    ColdFailureDefectRoutesStatement data object :=
  fun occurrence epsilon first minimal defect =>
    (coldFailureDefect_excluded data object distinct occurrence epsilon first
      minimal defect).elim

set_option maxHeartbeats 1600000 in
/-- **The residual of `[153]`, constructed at G.**  If (★) fails at G, some
retained corridor of G has two equal pinned states at segments up to a segment
with no earlier event.  Take the least `right` carrying an earlier equal state
and such a `left`: `(left, right)` is G's first equal-state pair, no event
precedes `right`, the (F2) clause holds at `right` through the path context
(`coldFirstFailureDefectAt_iff`), the context closes an accepted cycle with
`piece J_right` and none with the `J_left` reading, and the two readings are
profile-separated (`ColdEqualStates.prefix_profile_ne`). -/
theorem coldRepeatedStateResidual_of_not_distinct (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (accept : ∀ k, 2 ≤ k → data.LengthOK (2 ^ k))
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
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
  refine ⟨occurrence, epsilon, outside, left, right, lt, same, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro earlierLeft earlierRight earlierLt earlierBefore earlierSame
    have member : earlierRight ∈ repeats :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, earlierLeft, earlierLt, earlierSame⟩
    have := repeats.min'_le earlierRight member
    exact absurd (Fin.le_def.1 this) (by omega)
  · intro earlier before
    exact minimal earlier (by omega)
  · exact (coldFirstFailureDefectAt_iff data object accept avoids outside corridor
      presentation index right).2 ⟨left, lt, same⟩
  · exact Graph.ColdEqualStates.prefixContext_piece_cycle data.LengthOK accept outside
      corridor right (by omega)
  · exact Graph.ColdEqualStates.prefixContext_retained_noCycle data.LengthOK avoids
      outside corridor left right lt
  · exact Graph.ColdEqualStates.prefix_profile_ne outside corridor left right lt

/-- **`lem:cold-corridor-first-failure`, the routing** (tex 7234-7295): (F1)
is a target cycle and (F3) a target-complete compression, both excluded by the
ledger; (F2) is a sparse exit (node `[422]`, `ColdFailureDefectRoutesStatement`,
at G's retained occurrence and first failure) excluded by the node-`[125]`
survivor; every other first failure is routed as
the lemma states -- (F5) a cold bounded configuration or (F4) an already named
handoff of the declared registry `ColdDeclaredHandoffSupport` (G's heavy
handoff centres). -/
theorem coldFailureRouting_of_failures
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceStatement data object)
    (failureCycle : ColdFailureCycleStatement data object)
    (failureCompression : ColdFailureCompressionStatement data object)
    (defectRoutes : ColdFailureDefectRoutesStatement data object)
    (survivor : DeclaredSparseSurvivor data object) :
    ColdFailureRoutingStatement data object := by
  let occurrenceData := Classical.choice occurrence
  refine ⟨⟨occurrenceData, ?_⟩⟩
  intro epsilon
  obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
  cases event with
  | cycle cycle =>
      exact (failureCycle occurrenceData epsilon first cycle).elim
  | defect defect =>
      exact (survivor (defectRoutes occurrenceData epsilon first minimal
        defect)).elim
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
