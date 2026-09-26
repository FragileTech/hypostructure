import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[153]`: select the first event in the manuscript's ordered
(F1)--(F5) list for every retained cold corridor. -/
@[reducible] noncomputable def coldFirstFailureOccurrenceRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureOccurrence
    { Requires := [K .coldCorridorState, K .coldDeclaredHandoffLedger]
      Produces := [K .coldFirstFailureOccurrence]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      let handoffLedger := (inputs.get (K .coldDeclaredHandoffLedger)).down
      let Handoff : Finset inputs.current.object.Vertex → Prop :=
        Classical.choose handoffLedger
      let handoffAbsent := Classical.choose_spec handoffLedger
      -- The occurrence is constructed over the abstract current object, so
      -- the retained state's `Classical.choose` projections are compared
      -- without unfolding the executor's input record.
      let occurrence : ColdFirstFailureOccurrenceStatement data.toParameters
          inputs.current.object :=
        (fun (object : Graph.FiniteObject.{u})
            (state : ColdCorridorStateStatement data.toParameters object)
            (Handoff : Finset object.Vertex → Prop)
            (handoffAbsent : ∀ support, ¬ Handoff support) =>
          (show ColdFirstFailureOccurrenceStatement data.toParameters object from by
            classical
            letI : FinEnum object.Vertex := object.vertices
            refine ⟨⟨Handoff, handoffAbsent, state, ?_⟩⟩
            intro Eligible incidence stateOne componentAt stateTwo corridorAt stateTail
              presentationAt indexAt epsilon
            let indexTail := Classical.choose_spec stateTail
            let stateFacts := (Classical.choose_spec indexTail).1
            let germ := incidence epsilon
            let corridor := corridorAt epsilon
            let presentation := presentationAt epsilon
            let index := indexAt epsilon
            let packing := canonicalWindowPacking data.toParameters object
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
              Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment
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
              ColdFirstFailureEvent data.toParameters object corridor presentation index germ
                Handoff segment
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
            exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore))
          inputs.current.object state Handoff handoffAbsent
      .cons (key := K .coldFirstFailureOccurrence) ⟨occurrence⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
