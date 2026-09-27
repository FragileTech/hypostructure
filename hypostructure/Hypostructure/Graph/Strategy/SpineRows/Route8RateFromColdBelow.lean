import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Rate

/-!
# Nodes `[120]`--`[122]`, the private-carrier rate on the cold `[147]` arm

`rem:route8-carrier-margin`, `prop:typeA-route8-carrier-reduction`: on the
`[147]` arm the census rate is read from `K .coldRoute8Below` through
`|∂R| = e(R,W) ≤ stubs·p + σ_W ≤ stubs·p + T(n)`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The census rate on the cold `[147]` arm. -/
@[reducible] noncomputable def route8RateFromColdBelowRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateFromColdBelow
    { Requires := [K .coldRoute8Below, K .surplusAtOrBelow, K .cubicBaseline]
      Produces := [K .route8Rate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8Rate)
        ⟨Graph.Contracts.RouteEight.route8RateFromColdBelow data.toParameters
          inputs.current.object inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1; omega)
          (inputs.get (K .coldRoute8Below)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
