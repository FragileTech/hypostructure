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
    { Requires := [K .triangularShoulderCompletion, K .triangularPortReturn]
      Produces := [K .triangularFirstLanding]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- tex 1880: first landing is read after `lem:triangular-port-return`.
      let _portReturn := (inputs.get (K .triangularPortReturn)).down
      .cons (key := K .triangularFirstLanding)
        ⟨Contracts.TypeB.triangularFirstLanding (inputs.get (K .triangularShoulderCompletion)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
