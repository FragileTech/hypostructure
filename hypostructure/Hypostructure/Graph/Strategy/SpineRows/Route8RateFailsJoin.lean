import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.RateFailsJoin
import Hypostructure.Graph.Contracts.RouteEight.RateFailsPiece

/-!
# The failed private-carrier rate against the exact window join at G

Structural accounting of `Route8RateFailsOutcome`: the rate's supply `|∂R| = e(R,W)`
is bounded by the `[146]`-no lower bound without the cross-window incidences
`2e_×(W)` of G's canonical packing.  The row publishes the exact join identity
at `P₀` (`lem:exact-window-join-identity`) and the failed rate read against it.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The failed rate against the exact window join, at G's canonical packing. -/
@[reducible] noncomputable def route8RateFailsJoinRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateFailsJoin
    { Requires := [K .route8RateFails, K .cubicBaseline]
      Produces := [K .route8RateFailsJoin]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8RateFailsJoin)
        ⟨Graph.Contracts.RouteEight.route8RateFailsJoin data.toParameters
          inputs.current.object inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          (inputs.get (K .route8RateFails)).down⟩ .nil)
    0 0

/-- The failed rate on the connected pieces of G's remainder (`H03`). -/
@[reducible] noncomputable def route8RateFailsPieceRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateFailsPiece
    { Requires := [K .route8RateFails]
      Produces := [K .route8RateFailsPiece]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8RateFailsPiece)
        ⟨Graph.Contracts.RouteEight.route8RateFailsPiece data.toParameters
          inputs.current.object
          (inputs.get (K .route8RateFails)).down⟩ .nil)
    0 0

/-- The cross-window incidences against the density cap at G. -/
@[reducible] noncomputable def route8RateFailsCrossBoundRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateFailsCrossBound
    { Requires := [K .route8RateFailsJoin, K .densityCap, K .surplusAtOrBelow,
        K .cubicBaseline]
      Produces := [K .route8RateFailsCrossBound]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down.2.2.2
      .cons (key := K .route8RateFailsCrossBound)
        ⟨Graph.Contracts.RouteEight.route8RateFailsCrossBound data.toParameters
          inputs.current.object (laws.2.2.1 inputs.current.object.vertexCount)
          (inputs.get (K .surplusAtOrBelow)).down inputs.current.baseline
          (inputs.get (K .densityCap)).down
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
