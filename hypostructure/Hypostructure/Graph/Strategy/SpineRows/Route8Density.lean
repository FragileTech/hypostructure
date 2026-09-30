import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Density
import Hypostructure.Graph.WindowLabelCensus

/-!
# The density theorem at the pieces of `R`, the arm closure, and the net-cap size split
(keys `9700`–`9706`)

Published on the common prefix of `Route8QuotientOutcome` and `Route8JointBalanceOutcome`,
after key `9807`.  Thin adapters of `Contracts/RouteEight/Density.lean`; the presentation
identities `δ = 3`, `s = 4`, `W = 13` (from the registered label census), the dyadic target
law and `δ + 2 + s ≤ F·s` are read from `K .cubicBaseline`:

* `route8HubFreeDensityRow` (key `9700`) reads `cubicBaseline`, `selection`,
  `minDegreeBaseline`, `remainderPathBounds`;
* `route8X15LongLandingsRow` (key `9701`) reads `cubicBaseline`, `selection`,
  `minDegreeBaseline`, `route8PackingExchange`;
* `route8HubFreePiRow` (key `9702`) reads `cubicBaseline`, `minDegreeBaseline`, `9700`, `9701`;
* `route8HubPieceExcessRow` (key `9703`) reads `minDegreeBaseline`, `route8HubPieceMass`;
* `route8ArmClosureRow` (key `9704`) reads `cubicBaseline`, `minDegreeBaseline`,
  `surplusAtOrBelow`, `9807`, `9702`, `9703`;
* `route8NetCapDichotomy` decides `9705` / `9706` after `9704`; the large arm is closed by
  `instIncompatibleRoute8ArmClosureNetCapLarge`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Key `9700`**: the density theorem at the hub-free pieces. -/
@[reducible] noncomputable def route8HubFreeDensityRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8HubFreeDensity
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline,
        K .remainderPathBounds]
      Produces := [K .route8HubFreeDensity]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8HubFreeDensity)
        ⟨Graph.Contracts.RouteEight.route8HubFreeDensity data.toParameters
          inputs.current.object laws.1.1 laws.1.2.1 laws.2.1.2.1
          (inputs.get (K .selection)).down.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .remainderPathBounds)).down⟩ .nil)
    0 0

/-- **Key `9701`**: the long landings of a hub-free `X15` piece. -/
@[reducible] noncomputable def route8X15LongLandingsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8X15LongLandings
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline,
        K .route8PackingExchange]
      Produces := [K .route8X15LongLandings]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8X15LongLandings)
        ⟨Graph.Contracts.RouteEight.route8X15LongLandings data.toParameters
          inputs.current.object laws.1.1
          (Graph.WindowCurvature.order_eq_of_sizeDistribution_head laws.1.2.2.2.2.2)
          laws.2.1.2.1
          (inputs.get (K .selection)).down.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .route8PackingExchange)).down⟩ .nil)
    0 0

/-- **Key `9702`**: `Π` at the hub-free pieces. -/
@[reducible] noncomputable def route8HubFreePiRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8HubFreePi
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .route8HubFreeDensity,
        K .route8X15LongLandings]
      Produces := [K .route8HubFreePi]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8HubFreePi)
        ⟨Graph.Contracts.RouteEight.route8HubFreePi data.toParameters
          inputs.current.object laws.1.1 laws.1.2.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .route8HubFreeDensity)).down
          (inputs.get (K .route8X15LongLandings)).down⟩ .nil)
    0 0

/-- **Key `9703`**: the excess of a hub piece. -/
@[reducible] noncomputable def route8HubPieceExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8HubPieceExcess
    { Requires := [K .minDegreeBaseline, K .route8HubPieceMass]
      Produces := [K .route8HubPieceExcess]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8HubPieceExcess)
        ⟨Graph.Contracts.RouteEight.route8HubPieceExcess data.toParameters
          inputs.current.object
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .route8HubPieceMass)).down⟩ .nil)
    0 0

/-- **Key `9704`**: the arm closure. -/
@[reducible] noncomputable def route8ArmClosureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ArmClosure
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .surplusAtOrBelow,
        K .route8ArmClosureResidual, K .route8HubFreePi, K .route8HubPieceExcess]
      Produces := [K .route8ArmClosure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down
      .cons (key := K .route8ArmClosure)
        ⟨Graph.Contracts.RouteEight.route8ArmClosure data.toParameters
          inputs.current.object laws.1.1 laws.1.2.1
          (Graph.WindowCurvature.order_eq_of_sizeDistribution_head laws.1.2.2.2.2.2)
          laws.2.1.2.2.2.2
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .surplusAtOrBelow)).down
          (inputs.get (K .route8ArmClosureResidual)).down
          (inputs.get (K .route8HubFreePi)).down
          (inputs.get (K .route8HubPieceExcess)).down⟩ .nil)
    0 0

/-- **The net-cap size split**: `F ≤ 14 ∧ SufficientlyLargeForNetCap` at G's order, or its
negation, decided after the arm closure is published. -/
noncomputable def route8NetCapDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8ArmClosure) known]
    (largeFresh : K .route8NetCapLarge ∉ known)
    (smallFresh : K .route8NetCapSmall ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8NetCapLarge) (K .route8NetCapSmall) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8NetCapLarge) (K .route8NetCapSmall)
    `Hypostructure.Graph.Strategy.Spine.route8NetCapDichotomy
    (by
      classical
      letI : FactSystem (Input BranchState Presentation presentation data) :=
        factSystem BranchState Presentation presentation data
      have _closure := (previous.get (K .route8ArmClosure)).down
      exact if large : Route8NetCapLargeStatement data.toParameters current.object then
        .inl ⟨large⟩
      else
        .inr ⟨large⟩)
    largeFresh smallFresh

/-- **The large arm of the net-cap split closes** against the arm closure. -/
noncomputable instance instIncompatibleRoute8ArmClosureNetCapLarge :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8ArmClosure) (K .route8NetCapLarge) where
  contradiction := fun _ closure large => closure.down large.down.1 large.down.2

end Hypostructure.Graph.Strategy.Spine
