import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers`** (node
`[123]`) on the quotient-free arm. -/
@[reducible] noncomputable def route8UnifiedEntryCensusRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedEntryCensus
    { Requires := [K .route8QuotientFree, K .selection, K .replacementExclusion]
      Produces := [K .route8UnifiedEntryCensus]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedEntryCensus)
        ⟨Graph.Contracts.RouteEight.route8UnifiedEntryCensus data.toParameters inputs.current.object
          (inputs.get (K .route8QuotientFree)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2
          (inputs.get (K .replacementExclusion)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
