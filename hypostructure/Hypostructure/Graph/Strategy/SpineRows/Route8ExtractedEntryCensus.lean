import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **`def:typeA-unified-entries` at the extracted route-`8` cores**
(`lem:typeB-bridge-with-route8-core`). -/
@[reducible] noncomputable def route8ExtractedEntryCensusRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ExtractedEntryCensus
    { Requires := [K .selection, K .replacementExclusion, K .cubicBaseline]
      Produces := [K .route8ExtractedEntryCensus]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ExtractedEntryCensus)
        ⟨Graph.Contracts.RouteEight.route8ExtractedEntryCensus data.toParameters inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2
          (inputs.get (K .replacementExclusion)).down
          (inputs.get (K .cubicBaseline)).down.1
          data.degenerateClosureRejected⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
