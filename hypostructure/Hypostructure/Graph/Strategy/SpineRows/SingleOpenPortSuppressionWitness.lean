import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.OpenPort

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- `lem:single-open-port-suppression-witness`. -/
@[reducible] noncomputable def singleOpenPortSuppressionWitnessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.singleOpenPortSuppressionWitness
    { Requires := [K .selection]
      Produces := [K .singleOpenPortSuppressionWitness]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .singleOpenPortSuppressionWitness)
        ⟨Contracts.TypeB.singleOpenPortSuppressionWitness inputs.current.baseline
          (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
