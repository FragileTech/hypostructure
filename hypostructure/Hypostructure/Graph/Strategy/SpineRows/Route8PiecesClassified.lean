import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- `thm:branch-kill`'s all-pieces classification. -/
@[reducible] noncomputable def route8PiecesClassifiedRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PiecesClassified
    { Requires := [K .typeAExclusion, K .typeBBridgeReduction]
      Produces := [K .route8PiecesClassified]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PiecesClassified)
        ⟨Graph.Contracts.RouteEight.route8PiecesClassified data.toParameters inputs.current.object
          (inputs.get (K .typeAExclusion)).down
          (inputs.get (K .typeBBridgeReduction)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
