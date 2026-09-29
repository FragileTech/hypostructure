import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.FoldPeels

/-!
# Route 8 read on the pieces constructed from G (idx 8700)

At every unified entry of the route-`8` ledger, the realizations of the
declared trace-response state are the pieces constructed from G at the selected
basin (`Graph.GConstructedPiece`), read in G's own surroundings `G − B_u`.  A
fold of two interior basin vertices with no common neighbour is such a piece
and a strictly smaller baseline graph once glued, so it carries a target cycle:
alternative (a) occurs and the load is an exit-`(4)` peel (Q3).  A nonempty
essential core means the declared family determines the target, and every
complete carrier set holds every fold pair.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Route 8 read on the pieces constructed from G**
(`Route8FoldPeelsStatement`). -/
@[reducible] noncomputable def route8FoldPeelsRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8FoldPeels
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .route8FoldPeels]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8FoldPeels)
        ⟨Graph.Contracts.RouteEight.route8FoldPeels data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          inputs.current.baseline
          (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
