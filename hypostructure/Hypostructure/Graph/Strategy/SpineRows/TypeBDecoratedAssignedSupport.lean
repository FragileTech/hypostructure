import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBDecoratedAssignedSupportRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.typeBDecoratedAssignedSupport
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .typeAExitSevenHandoff]
      Produces := [K .typeBDecoratedAssignedSupport, K .typeBFanEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let handoff := (inputs.get (K .typeAExitSevenHandoff)).down
      .cons (key := K .typeBDecoratedAssignedSupport)
        ⟨by
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, envelope, coreEq, nonempty⟩ :=
            handoff
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          have inside : piece ⊆
              inputs.current.object.remainderSupport packing :=
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
          have coreInside : envelope.core ⊆
              inputs.current.object.remainderSupport packing := by
            intro vertex member
            exact inside (by simpa [piece, coreEq] using member)
          have normalized := (inputs.get (K .remainderNormalized)).down
          have windowFree :
              handoffWindowFree data inputs.current.object envelope.core := by
            constructor
            · intro window subset windowInduces
              exact (normalized packing valid maximal window
                (subset.trans coreInside)).1 windowInduces
            · intro internal subset
              exact (normalized packing valid maximal internal
                (subset.trans coreInside)).2
          have admissible :
              Graph.DecoratedHandoff.Admissible inputs.current.object
                data.LengthOK (handoffUncompressible data inputs.current.object)
                (handoffWindowFree data inputs.current.object) envelope :=
            { dyadicSafe := (inputs.get (K .selection)).down.1
              coreWindowFree := windowFree
              uncompressible := (inputs.get (K .uncompressible)).down
              fanReturnSafe := fun centre centreMember first firstMember second
                  secondMember different =>
                (envelope.fanSafe centre centreMember first firstMember second
                  secondMember different).1 }
          have high : ∀ centre ∈ envelope.decorations,
              Graph.IsHighCentre inputs.current.object data.threshold centre := by
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
              admissible⟩⟩⟩
        (.cons (key := K .typeBFanEntry)
          -- Node `[65]`, after routing-only input `[66]`: publish the common
          -- Type B fan entry with the envelope decorations as its assigned
          -- centres (`def:typeB-assigned-ledger`).
          ⟨by
            apply Or.inl
            obtain ⟨packing, _canonical, valid, maximal, component, present, negative, zero,
              _receiver, _isReceiver, _peeled, _peeledSubset, _saturated, _noExitFour,
              _noCompression, _noDelocalization, envelope, coreEq, nonempty⟩ :=
              handoff
            refine ⟨packing, valid, maximal, component, present, envelope.decorations,
              Or.inr ⟨negative, zero, envelope, coreEq, rfl, nonempty,
                fun centre member =>
                  ⟨envelope.assigned_nonempty centre member,
                    envelope.assigned_adj centre member⟩⟩,
              nonempty, fun centre member => ?_⟩
            simpa [Graph.IsHighCentre] using
              envelope.decorations_high centre member⟩
          .nil))
    0 0

end Hypostructure.Graph.Strategy.Spine
