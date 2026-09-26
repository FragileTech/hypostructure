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

/-- Node `[69]`, `lem:same-center-open-port-compatibility`, read from the normal
form of node `[67]`. -/
@[reducible] noncomputable def sameCenterOpenPortCompatibilityRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameCenterOpenPortCompatibility
    { Requires := [K .highCentreNormalForm]
      Produces := [K .sameCenterOpenPortCompatibility]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameCenterOpenPortCompatibility)
        ⟨Contracts.TypeB.sameCenterOpenPortCompatibility (inputs.get (K .highCentreNormalForm)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
