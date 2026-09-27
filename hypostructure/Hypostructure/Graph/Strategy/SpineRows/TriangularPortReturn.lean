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

/-- Node `[79]`, `lem:triangular-port-return`. -/
@[reducible] noncomputable def triangularPortReturnRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularPortReturn
    { Requires := [K .bridgeless, K .selection, K .highCentreNormalForm,
        K .triangularShoulderCompletion, K .cubicBaseline]
      Produces := [K .triangularPortReturn]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularPortReturn)
        ⟨Contracts.TypeB.triangularPortReturn (inputs.get (K .bridgeless)).down
          (inputs.get (K .selection)).down.1 (inputs.get (K .highCentreNormalForm)).down
          (inputs.get (K .triangularShoulderCompletion)).down
          (inputs.get (K .cubicBaseline)).down.1
          (inputs.get (K .cubicBaseline)).down.2.2.2.2.2.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
