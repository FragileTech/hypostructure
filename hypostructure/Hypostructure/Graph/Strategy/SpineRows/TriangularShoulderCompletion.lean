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

/-- Nodes `[78]`--`[79]`, `lem:triangular-shoulder-completion`. -/
@[reducible] noncomputable def triangularShoulderCompletionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularShoulderCompletion
    { Requires := [K .highCentreNormalForm]
      Produces := [K .triangularShoulderCompletion]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularShoulderCompletion)
        ⟨Contracts.TypeB.triangularShoulderCompletion (inputs.get (K .highCentreNormalForm)).down
          data.threshold_eq_three data.three_le_threshold inputs.current.baseline⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
