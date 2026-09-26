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

/-- `lem:open-port-suppression-safe`. -/
@[reducible] noncomputable def openPortSuppressionSafeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.openPortSuppressionSafe
    { Requires := [K .openPortSuppression]
      Produces := [K .openPortSuppressionSafe]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .openPortSuppressionSafe)
        ⟨Contracts.TypeB.openPortSuppressionSafe (inputs.get (K .openPortSuppression)).down
          data.three_le_threshold inputs.current.baseline⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
