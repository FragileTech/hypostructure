import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.BlobStructure

/-!
# The pieces of the remainder against the windows of `P₀` (keys 9900–9902)

Blob structure on the rate arm (`K .route8Rate`), published on the common prefix of
`Route8QuotientOutcome` and `Route8JointBalanceOutcome`.  The three rows are thin adapters of
`Contracts/RouteEight/BlobStructure.lean`:

* `route8PieceWindowAttachmentRow` (key `9900`) reads G's target avoidance (`K .selection`)
  and the dyadic length law (`K .cubicBaseline`);
* `route8PieceChainCycleRow` (key `9901`) reads the same two facts;
* `route8PiecewiseRateRow` (key `9902`) reads the private-carrier rate `K .route8Rate`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Key `9900`**: a piece attached twice to one window of `P₀`. -/
@[reducible] noncomputable def route8PieceWindowAttachmentRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PieceWindowAttachment
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .route8PieceWindowAttachment]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PieceWindowAttachment)
        ⟨Graph.Contracts.RouteEight.route8PieceWindowAttachment data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩ .nil)
    0 0

/-- **Key `9901`**: chain cycles through distinct pieces and distinct windows of `P₀`. -/
@[reducible] noncomputable def route8PieceChainCycleRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PieceChainCycle
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .route8PieceChainCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PieceChainCycle)
        ⟨Graph.Contracts.RouteEight.route8PieceChainCycle data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩ .nil)
    0 0

/-- **Key `9902`**: the private-carrier rate written over the canonical pieces of `R`. -/
@[reducible] noncomputable def route8PiecewiseRateRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PiecewiseRate
    { Requires := [K .route8Rate]
      Produces := [K .route8PiecewiseRate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PiecewiseRate)
        ⟨Graph.Contracts.RouteEight.route8PiecewiseRate data.toParameters
          inputs.current.object (inputs.get (K .route8Rate)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
