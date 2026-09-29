import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.PackingExchange
import Hypostructure.Graph.Contracts.RouteEight.HubPieceMass

/-!
# Exchange at the maximum packing `P₀`, and the hub-piece mass (keys 9800–9803)

Published on the common prefix of `Route8QuotientOutcome` and `Route8JointBalanceOutcome`.
The rows are thin adapters of `Contracts/RouteEight/PackingExchange.lean` and
`Contracts/RouteEight/HubPieceMass.lean`:

* `route8PackingExchangeRow` (key `9800`), `route8ArmExchangeRow` (key `9801`) and
  `route8FullArmLandingCapRow` (key `9802`) read no predecessor fact: `P₀` is G's canonical
  maximum packing (`canonicalWindowPacking_spec`), read off the object;
* `route8HubPieceMassRow` (key `9803`) reads `K .typeBSublinearLedger`, `K .typeBBridgeMass`
  and `K .minDegreeBaseline`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Key `9800`**: the `k`-fold exchange at `P₀`. -/
@[reducible] noncomputable def route8PackingExchangeRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PackingExchange
    { Requires := []
      Produces := [K .route8PackingExchange]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PackingExchange)
        ⟨Graph.Contracts.RouteEight.route8PackingExchange data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9801`**: arm exchange at one window of `P₀`. -/
@[reducible] noncomputable def route8ArmExchangeRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ArmExchange
    { Requires := []
      Produces := [K .route8ArmExchange]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ArmExchange)
        ⟨Graph.Contracts.RouteEight.route8ArmExchange data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9802`**: full arms landing on distinct positions of one window of `P₀` intersect. -/
@[reducible] noncomputable def route8FullArmLandingCapRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8FullArmLandingCap
    { Requires := []
      Produces := [K .route8FullArmLandingCap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8FullArmLandingCap)
        ⟨Graph.Contracts.RouteEight.route8FullArmLandingCap data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9803`**: the mass of the negative hub pieces of `R`. -/
@[reducible] noncomputable def route8HubPieceMassRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8HubPieceMass
    { Requires := [K .typeBSublinearLedger, K .typeBBridgeMass, K .minDegreeBaseline]
      Produces := [K .route8HubPieceMass]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8HubPieceMass)
        ⟨Graph.Contracts.RouteEight.route8HubPieceMass data.toParameters
          inputs.current.object (inputs.get (K .typeBSublinearLedger)).down
          (inputs.get (K .typeBBridgeMass)).down
          (inputs.get (K .minDegreeBaseline)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
