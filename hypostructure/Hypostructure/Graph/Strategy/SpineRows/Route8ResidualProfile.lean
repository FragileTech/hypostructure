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
@[reducible] noncomputable def route8ResidualProfileRow
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
    `Hypostructure.Graph.Strategy.Spine.route8ResidualProfile
    { Requires := [K .typeAExitSevenFree]
      Produces := [K .route8ResidualProfile]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeAExitSevenFree)
      .cons (key := K .route8ResidualProfile)
        ⟨by
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, routing,
            noCompression, noDelocalization, noHandoff⟩ := residual.down
          exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, routing,
            noCompression, noDelocalization, noHandoff⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
