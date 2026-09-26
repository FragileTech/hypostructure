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

/-- Node `[81]`, `lem:triangular-cross-shoulder`. -/
@[reducible] noncomputable def triangularCrossShoulderRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularCrossShoulder
    { Requires := [K .selection]
      Produces := [K .triangularCrossShoulder]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularCrossShoulder)
        ⟨Contracts.TypeB.triangularCrossShoulder (inputs.get (K .selection)).down.1
          data.quadrilateralAccepted⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
