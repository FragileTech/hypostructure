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

/-! ## `lem:single-open-port-suppression-witness`

The generic tight-vertex suppression theorem already formalizes the paper's
argument: minimality gives an accepted cycle after suppression, avoidance
forces that cycle through the new shoulder chord, and deleting that chord
reconstructs the predecessor-length path in `G - x`.  This row exposes that
existing proof on the selected ExactLedger object. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def singleOpenPortSuppressionWitnessRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.singleOpenPortSuppressionWitness
    { Requires := [K .selection]
      Produces := [K .singleOpenPortSuppressionWitness]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .singleOpenPortSuppressionWitness) ⟨by
        change SingleOpenPortSuppressionWitnessStatement data
          inputs.current.object
        classical
        intro configuration centreHigh
        obtain ⟨_certificate, ⟨reconstructed⟩⟩ :=
          configuration.singleSuppressionWitness_of_minimal
            (LengthOK := data.LengthOK) (threshold := data.threshold)
            inputs.current.baseline selection.1
            (fun smaller smallerDecrease baseline =>
              selection.2.sizeMinimal smaller smallerDecrease baseline)
            centreHigh
        exact Graph.FiniteObject.SurplusPort.openPortWitness_of_deleted
          (endpoint := configuration.vertex) reconstructed.path
            reconstructed.isPath reconstructed.restored_length_ok⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
