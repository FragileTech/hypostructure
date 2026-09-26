import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.VisibleResidual

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[184]`, `lem:typeA-unified-visible-ownership`**: the silent
coordinate of the unchanged unified entries is zero. -/
@[reducible] noncomputable def route8UnifiedVisibleResidualRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleResidual
    { Requires := [K .route8UnifiedEntryCensus]
      Produces := [K .route8UnifiedVisibleResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedVisibleResidual)
        ⟨Graph.Contracts.RouteEight.route8UnifiedVisibleResidual data.toParameters inputs.current.object
          (inputs.get (K .route8UnifiedEntryCensus)).down
          inputs.current.baseline
          data.three_le_threshold⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
