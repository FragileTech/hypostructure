import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.RateFailsJoin
import Hypostructure.Graph.Contracts.RouteEight.RateFailsPiece
import Hypostructure.Graph.Contracts.RouteEight.RateFailsFlow
import Hypostructure.Graph.Contracts.RouteEight.RateFailsAccounting
import Hypostructure.Graph.Contracts.RouteEight.RateFailsRoute
import Hypostructure.Graph.Contracts.RouteEight.WindowRPath

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

/-- The integral stub-to-deficit flow and the failed rate in deficit currency (`H07`). -/
@[reducible] noncomputable def route8RateFailsFlowRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateFailsFlow
    { Requires := [K .route8RateFails, K .route8RateFailsJoin, K .cubicBaseline]
      Produces := [K .route8RateFailsFlow]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8RateFailsFlow)
        ⟨Graph.Contracts.RouteEight.route8RateFailsFlow data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .route8RateFails)).down
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

/-- The carriers-to-cut injection of the canonical route-8 entries (`H06`). -/
@[reducible] noncomputable def route8CarrierInjectionRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CarrierInjection
    { Requires := [K .route8RateFails]
      Produces := [K .route8CarrierInjection]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CarrierInjection)
        ⟨Graph.Contracts.RouteEight.route8CarrierInjection data.toParameters
          inputs.current.object⟩ .nil)
    0 0

/-- The rate at G's exact surplus next to the ceiling version (`H08`). -/
@[reducible] noncomputable def route8RateExactSlackRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8RateExactSlack
    { Requires := [K .route8RateFails]
      Produces := [K .route8RateExactSlack]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8RateExactSlack)
        ⟨Graph.Contracts.RouteEight.route8RateExactSlack data.toParameters
          inputs.current.object
          (inputs.get (K .route8RateFails)).down⟩ .nil)
    0 0

/-- The stub-deficit identity at G. -/
@[reducible] noncomputable def route8StubDeficitRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8StubDeficit
    { Requires := [K .route8RateFailsJoin, K .cubicBaseline]
      Produces := [K .route8StubDeficit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8StubDeficit)
        ⟨Graph.Contracts.RouteEight.route8StubDeficit data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

/-- The deficit against the window stubs, or the isolated windows. -/
@[reducible] noncomputable def route8DeficitVsStubsRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8DeficitVsStubs
    { Requires := [K .route8StubDeficit, K .cubicBaseline]
      Produces := [K .route8DeficitVsStubs]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8DeficitVsStubs)
        ⟨Graph.Contracts.RouteEight.route8DeficitVsStubs data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          (inputs.get (K .route8StubDeficit)).down⟩ .nil)
    0 0

/-- The route-8 entries against the large-budget deficit test. -/
@[reducible] noncomputable def route8EntryLowerBoundRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8EntryLowerBound
    { Requires := [K .route8BasinBurden, K .route8RateFailsJoin]
      Produces := [K .route8EntryLowerBound]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8EntryLowerBound)
        ⟨Graph.Contracts.RouteEight.route8EntryLowerBound data.toParameters
          inputs.current.object
          (inputs.get (K .route8BasinBurden)).down
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

/-- Every route-8 census core is empty at G. -/
@[reducible] noncomputable def route8CoreEmptyRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CoreEmpty
    { Requires := [K .selection]
      Produces := [K .route8CoreEmpty]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CoreEmpty)
        ⟨Graph.Contracts.RouteEight.route8CoreEmpty data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1⟩ .nil)
    0 0

/-- The strong rate or the thin remainder. -/
@[reducible] noncomputable def route8StrongRateRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8StrongRate
    { Requires := [K .route8BasinBurden, K .selection, K .cubicBaseline]
      Produces := [K .route8StrongRate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8StrongRate)
        ⟨Graph.Contracts.RouteEight.route8StrongRate data.toParameters
          inputs.current.object inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.2.1; omega)
          (inputs.get (K .selection)).down.1
          (inputs.get (K .route8BasinBurden)).down⟩ .nil)
    0 0

/-- The thin remainder isolates the windows. -/
@[reducible] noncomputable def route8ThinIsolationRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ThinIsolation
    { Requires := [K .netDeficiencyCap, K .route8RateFailsJoin]
      Produces := [K .route8ThinIsolation]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ThinIsolation)
        ⟨Graph.Contracts.RouteEight.route8ThinIsolation data.toParameters
          inputs.current.object
          (inputs.get (K .netDeficiencyCap)).down
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

/-- The exact stub count of each window and its distribution. -/
@[reducible] noncomputable def route8WindowStubRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8WindowStub
    { Requires := [K .route8RateFailsJoin]
      Produces := [K .route8WindowStub]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8WindowStub)
        ⟨Graph.Contracts.RouteEight.route8WindowStub data.toParameters
          inputs.current.object inputs.current.baseline⟩ .nil)
    0 0

/-- The thin remainder forces a small order. -/
@[reducible] noncomputable def route8ThinSmallRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ThinSmall
    { Requires := [K .route8RateFailsJoin, K .densityCap, K .surplusAtOrBelow, K .cubicBaseline]
      Produces := [K .route8ThinSmall]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ThinSmall)
        ⟨Graph.Contracts.RouteEight.route8ThinSmall data.toParameters
          inputs.current.object inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          ((inputs.get (K .cubicBaseline)).down.2.2.2.2.2.1 inputs.current.object.vertexCount)
          (inputs.get (K .surplusAtOrBelow)).down
          (inputs.get (K .densityCap)).down
          (inputs.get (K .route8RateFailsJoin)).down⟩ .nil)
    0 0

/-- Cycles through two windows via the remainder avoid every power of two. -/
@[reducible] noncomputable def route8WindowRPathGapRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8WindowRPathGap
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .route8WindowRPathGap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8WindowRPathGap)
        ⟨Graph.Contracts.RouteEight.route8WindowRPathGap data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩ .nil)
    0 0

/-- The stubs to hubs. -/
@[reducible] noncomputable def route8HubStubsRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8HubStubs
    { Requires := [K .route8RateFailsJoin]
      Produces := [K .route8HubStubs]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8HubStubs)
        ⟨Graph.Contracts.RouteEight.route8HubStubs data.toParameters
          inputs.current.object inputs.current.baseline⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
