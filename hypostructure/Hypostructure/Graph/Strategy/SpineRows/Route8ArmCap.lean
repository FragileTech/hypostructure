import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.ArmCap

/-!
# Net-cap excess, clean landings, and the arm-closure residual (keys 9804–9807)

Published on the common prefix of `Route8QuotientOutcome` and `Route8JointBalanceOutcome`,
after the blob-structure rows (key `9902` is read).  Thin adapters of
`Contracts/RouteEight/ArmCap.lean`:

* `route8NetCapExcessRow` (key `9804`) reads `K .netDeficiencyCap` (key `222`) and
  `K .route8PiecewiseRate` (key `9902`);
* `route8CleanLandingRulesRow` (key `9805`) and `route8CleanLandingCapRow` (key `9806`) read
  no predecessor fact (`P₀` is G's canonical maximum packing, read off the object);
* `route8ArmClosureResidualRow` (key `9807`) reads keys `9804`, `9806` and `9902`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Key `9804`**: the net-cap excess. -/
@[reducible] noncomputable def route8NetCapExcessRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8NetCapExcess
    { Requires := [K .netDeficiencyCap, K .route8PiecewiseRate]
      Produces := [K .route8NetCapExcess]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8NetCapExcess)
        ⟨Graph.Contracts.RouteEight.route8NetCapExcess data.toParameters
          inputs.current.object (inputs.get (K .netDeficiencyCap)).down
          (inputs.get (K .route8PiecewiseRate)).down⟩ .nil)
    0 0

/-- **Key `9805`**: the pair and triple landing rules. -/
@[reducible] noncomputable def route8CleanLandingRulesRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CleanLandingRules
    { Requires := []
      Produces := [K .route8CleanLandingRules]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CleanLandingRules)
        ⟨Graph.Contracts.RouteEight.route8CleanLandingRules data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9806`**: the clean-landing cap. -/
@[reducible] noncomputable def route8CleanLandingCapRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CleanLandingCap
    { Requires := []
      Produces := [K .route8CleanLandingCap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CleanLandingCap)
        ⟨Graph.Contracts.RouteEight.route8CleanLandingCap data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9807`**: the arm-closure residual. -/
@[reducible] noncomputable def route8ArmClosureResidualRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ArmClosureResidual
    { Requires := [K .route8NetCapExcess, K .route8CleanLandingCap, K .route8PiecewiseRate]
      Produces := [K .route8ArmClosureResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ArmClosureResidual)
        ⟨Graph.Contracts.RouteEight.route8ArmClosureResidual data.toParameters
          inputs.current.object (inputs.get (K .route8NetCapExcess)).down
          (inputs.get (K .route8CleanLandingCap)).down
          (inputs.get (K .route8PiecewiseRate)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
