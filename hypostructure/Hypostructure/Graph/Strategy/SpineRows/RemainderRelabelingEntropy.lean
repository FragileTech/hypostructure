import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineRemainder

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

/- Exact finite relabelling-orbit lower bound for every support in a
normalized remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def remainderRelabelingEntropyRow :
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
    `Hypostructure.Graph.Strategy.Spine.remainderRelabelingEntropy
    { Requires := [K .remainderNormalized]
      Produces := [K .remainderRelabelingEntropy]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .remainderRelabelingEntropy)
        ⟨Contracts.Spine.remainderRelabelingEntropy_of_normalized data.toParameters
          inputs.current.object (inputs.get (K .remainderNormalized)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
