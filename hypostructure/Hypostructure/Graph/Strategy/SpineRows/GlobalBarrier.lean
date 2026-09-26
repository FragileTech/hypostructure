import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BranchD

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

@[reducible] noncomputable def globalBarrierRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.globalBarrier
    { Requires := [K .globalDelocalization]
      Produces := [K .globalBarrier]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .globalBarrier)
        ⟨Contracts.Spine.globalBarrier_of_globalDelocalization data.toParameters
          inputs.current.object (inputs.get (K .globalDelocalization)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
