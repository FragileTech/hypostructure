import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Triangular

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[80]`, `lem:triangular-first-landing`. -/
@[reducible] noncomputable def triangularFirstLandingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularFirstLanding
    { Requires := [K .triangularShoulderCompletion]
      Produces := [K .triangularFirstLanding]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularFirstLanding)
        ⟨Contracts.TypeB.triangularFirstLanding (inputs.get (K .triangularShoulderCompletion)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
