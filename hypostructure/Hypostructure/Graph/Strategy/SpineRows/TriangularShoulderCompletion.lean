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
    { Requires := [K .highCentreNormalForm, K .cubicBaseline]
      Produces := [K .triangularShoulderCompletion]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularShoulderCompletion)
        ⟨Contracts.TypeB.triangularShoulderCompletion (inputs.get (K .highCentreNormalForm)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (le_of_eq (inputs.get (K .cubicBaseline)).down.1.1.symm) inputs.current.baseline⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
