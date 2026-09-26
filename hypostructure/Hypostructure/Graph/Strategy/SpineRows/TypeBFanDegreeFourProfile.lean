import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[78]`--`[79]`: `cor:degree-four-local-activation` and the degree-four
fan profile at every assigned centre on the no arm of `[68]`. -/
@[reducible] noncomputable def typeBFanDegreeFourProfileRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeFourProfile
    { Requires := [K .highCentreNormalForm, K .typeBFanDegreeFourCentres]
      Produces := [K .typeBFanDegreeFourProfile]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanDegreeFourProfile)
        ⟨Contracts.TypeB.typeBFanDegreeFourProfile (inputs.get (K .highCentreNormalForm)).down
          (inputs.get (K .typeBFanDegreeFourCentres)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
