import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.WindowExchange

/-!
# Exchanges at one window of `P₀` (keys `9810`–`9812`)

Published on the common prefix of `Route8QuotientOutcome` and `Route8JointBalanceOutcome`,
after key `9706`.  Thin adapters of `Contracts/RouteEight/WindowExchange.lean`; G's target
avoidance is read from `K .selection` and the dyadic target law from `K .cubicBaseline`:

* `route8X15DoubleLandingRow` (key `9810`) reads `cubicBaseline`, `selection`;
* `route8ArmPairTriggerRow` (key `9811`) reads no prerequisite: it is a theorem about the
  maximum window packing `P₀` of G alone;
* `route8X15HeavyPairRow` (key `9812`) reads `cubicBaseline`, `selection`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Key `9810`**: legal double landings of `X15` on one window of `P₀`. -/
@[reducible] noncomputable def route8X15DoubleLandingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8X15DoubleLanding
    { Requires := [K .cubicBaseline, K .selection]
      Produces := [K .route8X15DoubleLanding]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8X15DoubleLanding)
        ⟨Graph.Contracts.RouteEight.route8X15DoubleLanding data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          laws.2.1.2.1⟩ .nil)
    0 0

/-- **Key `9811`**: two arms on one window of `P₀` trigger. -/
@[reducible] noncomputable def route8ArmPairTriggerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ArmPairTrigger
    { Requires := []
      Produces := [K .route8ArmPairTrigger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ArmPairTrigger)
        ⟨Graph.Contracts.RouteEight.route8ArmPairTrigger data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- **Key `9812`**: a copy of `X15` with exits on two windows of `P₀` bounds their rungs. -/
@[reducible] noncomputable def route8X15HeavyPairRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8X15HeavyPair
    { Requires := [K .cubicBaseline, K .selection]
      Produces := [K .route8X15HeavyPair]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8X15HeavyPair)
        ⟨Graph.Contracts.RouteEight.route8X15HeavyPair data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          laws.2.1.2.1⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
