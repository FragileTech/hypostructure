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

/-- Node `[79]`, `def:triangular-fan-core`. -/
@[reducible] noncomputable def triangularFanCoreRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularFanCore
    { Requires := [K .highCentreNormalForm]
      Produces := [K .triangularFanCore]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularFanCore)
        ⟨Contracts.TypeB.triangularFanCore (inputs.get (K .highCentreNormalForm)).down
          data.threshold_eq_three⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
