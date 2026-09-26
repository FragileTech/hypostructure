import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! Node `[153]`: eliminate (F1)--(F4) on the literal surviving-cold
residual and retain the manuscript's (F5) conclusion. -/

@[reducible] noncomputable def coldFirstFailureRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureRouting
    { Requires := [K .coldFirstFailureOccurrence, K .coldFailureCycle,
        K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldFailureHandoff,
        K .sparseSurplusSurvivor]
      Produces := [K .coldFailureRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let occurrence := (inputs.get (K .coldFirstFailureOccurrence)).down
      let failureCycle := (inputs.get (K .coldFailureCycle)).down
      let failureDefectRoute :=
        (inputs.get (K .coldFailureDefectRoute)).down
      let failureCompression := (inputs.get (K .coldFailureCompression)).down
      let failureHandoff := (inputs.get (K .coldFailureHandoff)).down
      let sparseSurvivor := (inputs.get (K .sparseSurplusSurvivor)).down
      -- The routing argument is stated over the abstract current object, so
      -- the nested `Classical.choose` projections of the retained occurrence
      -- are compared without unfolding the executor's input record.
      let surviving : ColdSurvivingFirstFailureStatement data
          inputs.current.object :=
        (fun (object : Graph.FiniteObject.{u})
            (occurrence : ColdFirstFailureOccurrenceStatement data object)
            (failureCycle : ColdFailureCycleStatement data object)
            (failureDefectRoute : ColdFailureDefectRoutesStatement data object)
            (failureCompression : ColdFailureCompressionStatement data object)
            (failureHandoff : ∀ (windows component : Finset object.Vertex)
              (corridor : Graph.ColdCorridor.Corridor object windows component)
              (Handoff : Finset object.Vertex → Prop)
              (segment : corridor.Segment),
              Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff
                  segment →
                ∃ support, Handoff support ∧ corridor.head segment ∈ support)
            (sparseSurvivor : Graph.SurvivesSparseExits
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object) =>
          let occurrenceData := Classical.choice occurrence
          (Classical.choice (show Nonempty
              (ColdSurvivingFirstFailureStatement data object) from
            by
              refine ⟨⟨⟨occurrenceData, ?_⟩⟩⟩
              intro epsilon
              obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
              cases event with
              | cycle cycle =>
                  exact (failureCycle _ _ _ _ _ _
                    (Classical.choose_spec
                      (Classical.choose_spec cycle).2).2).elim
              | defect defect =>
                  exact (sparseSurvivor
                    (failureDefectRoute _ _ _ _ _ (Classical.choose defect) first
                      (Classical.choose_spec defect).2)).elim
              | compression compression =>
                  exact (failureCompression _ _ _ _ _ _
                    ⟨Classical.choose compression⟩).elim
              | handoff handoff =>
                  obtain ⟨support, supportHandoff, _⟩ :=
                    failureHandoff _ _ _ _ _ handoff
                  exact (occurrenceData.handoffAbsent support supportHandoff).elim
              | germ germ => exact ⟨⟨first, germ, minimal⟩⟩)))
          inputs.current.object occurrence failureCycle failureDefectRoute
          failureCompression failureHandoff sparseSurvivor
      .cons (key := K .coldFailureRouting)
        ⟨⟨sparseSurvivor, surviving⟩⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
