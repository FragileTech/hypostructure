import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! The terminal decision of node `[123]`.  Finite exit-(4) descent either
reaches a true two-support entry — sent to `[124]` — or exhibits a recorded
failed-rate stage.  The failed arm retains `StageAccounting`; it is routed to
the target-defect demand ledger and node `[181]`, not treated as a
contradiction. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8StageOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8PeelingDescent) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8UnifiedEntryCensus) known]
    (survivorFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (failedFresh : K .route8StageRateFailed ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8UnifiedTrueTwoCarrierEntry) (K .route8StageRateFailed)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8UnifiedTrueTwoCarrierEntry) (K .route8StageRateFailed)
    `Hypostructure.Graph.Strategy.Spine.route8StageOutcomeDichotomy
    (by
      classical
      letI : DecidableEq current.object.Vertex :=
        Graph.Route8.vertexDecEq current.object
      apply Classical.choice
      obtain ⟨final, chain, accounting, ends⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .route8PeelingDescent)).down
      rcases ends with ⟨_rate, index, isTrue⟩ | rateFails
      · have transported := Graph.Route8Pressure.trueEntry_transport
          current.object (canonicalWindowPacking data current.object)
          (route8UnifiedEntries data current.object) data.threshold
          data.dischargeScale data.LengthOK final.toFinset isTrue
        have entryFacts :=
          (@ExactLedger.get (Input BranchState Presentation presentation data) _
            (factSystem BranchState Presentation presentation data)
            current known previous (K .route8UnifiedEntryCensus)).down index
            transported.1
        rcases entryFacts.2.2 with routeEntry | targetDefect
        · exact ⟨.inl ⟨⟨⟨index, transported.1, transported.2.1,
            entryFacts, routeEntry, transported.2.2⟩⟩⟩⟩
        · obtain ⟨witness, witnessLoad⟩ := targetDefect.2.2.2.2
          have fresh : index ∉ final.toFinset :=
            (Finset.mem_sdiff.mp isTrue.1).2
          have currentDefect := Graph.Route8Pressure.targetDefectAt_of_empty
            current.object data.threshold data.dischargeScale
            (Graph.HasCycleWithLength data.LengthOK) final.toFinset index
            fresh witness witnessLoad
          exact (isTrue.2.2 currentDefect).elim
      · exact ⟨.inr ⟨⟨final, chain, accounting, rateFails⟩⟩⟩)
    survivorFresh failedFresh

end Hypostructure.Graph.Strategy.Spine
