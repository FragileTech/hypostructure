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

/-! ## Provenance-preserving node-`[94]` lane

The shared visible/silent schemas above are intentionally adequate for the
paper's exit questions, but an unindexed existential cannot later be matched
with node `[184]`'s entry family.  The following four decisions run the same
local exit tests while retaining node `[94]`'s exact support and receiver in
the same existential.  No new mathematical premise is introduced. -/

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- Finite exit-`(4)` descent on the exact node-`[94]` silent origin.  The
terminal arm retains the origin; the unsaturated arm is the existing charged
receiver output. -/
noncomputable def typeASilentExitFourTerminalDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleFirstExcess) known]
    (freeFresh : K .typeASilentExitFourFree ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitFourReceiverDischarged) (K .typeASilentExitFourFree)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitFourReceiverDischarged) (K .typeASilentExitFourFree)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitFourTerminalDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative,
        zero, noVisible, receiver, isReceiver, originalSaturated, silent,
        count⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleFirstExcess)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      let origin : SilentExitOriginAt data current.object piece receiver :=
        ⟨noVisible, originalSaturated, silent, count⟩
      let start : Finset current.object.Vertex := ∅
      have startInside : start ⊆
          current.object.routedLoads piece data.threshold receiver :=
        Finset.empty_subset _
      have startSaturated : Graph.ExitFour.SaturatedAfter piece data.threshold
          data.dischargeScale receiver start :=
        (Graph.ExitFour.saturatedAfter_empty piece data.threshold
          data.dischargeScale receiver).mpr originalSaturated
      have startWitnessed : Graph.ExitFour.PeeledByWitnesses
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
          data.dischargeScale receiver start :=
        Graph.ExitFour.peeledByWitnesses_empty _ piece data.threshold
          data.dischargeScale receiver
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 := by
          unfold Graph.FiniteObject.ambientSurplus at zero
          exact Finset.sum_eq_zero_iff.mp zero vertex member
        omega
      have descent := Graph.ExitFour.terminal_or_unsaturated_from piece
        data.threshold data.dischargeScale receiver
        (Retained := Graph.ExitFour.PeeledByWitnesses
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            data.dischargeScale receiver)
        (Terminal := fun state =>
          Graph.ExitFour.SaturatedAfter piece data.threshold
              data.dischargeScale receiver state ∧
            ExitFourFreeAt data current.object piece receiver state)
        startInside startWitnessed
        (by
          intro state stateInside stateWitnessed stateSaturated
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
              data.threshold data.dischargeScale receiver state
              (exactDegree receiver isReceiver.1) isReceiver stateSaturated with
            visible | silent
          · obtain ⟨package⟩ := Graph.ExitFour.visibleFourUnpeeledPackage piece
              data.threshold data.dischargeScale receiver state visible
            by_cases occurs :
                ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                    data.dischargeScale receiver state,
                  ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                      data.threshold data.dischargeScale receiver package.outside
                      state,
                    witness.load = load
            · obtain ⟨next, _load, _selected, _equal⟩ := occurs
              exact Or.inr ⟨next.load, next.routed, next.fresh,
                Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩
            · refine Or.inl ⟨stateSaturated, Or.inl ⟨package, occurs, ?_⟩⟩
              rcases package.exists_witness_or_pairwise_targetComplete
                  (Target := Graph.HasCycleWithLength data.LengthOK) with
                ⟨witness, selected⟩ | complete
              · exact False.elim (occurs ⟨witness, witness.load, selected, rfl⟩)
              · exact complete
          · by_cases occurs :
                ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                    data.dischargeScale receiver state,
                  witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                    data.threshold data.dischargeScale receiver state
            · obtain ⟨next, _supported⟩ := occurs
              exact Or.inr ⟨next.load, next.routed, next.fresh,
                Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩
            · exact Or.inl ⟨stateSaturated, Or.inr ⟨silent, occurs⟩⟩)
      rcases descent with
        ⟨final, finalInside, _finalWitnessed, finalSaturated, finalFree⟩ |
        ⟨final, finalInside, finalWitnessed, finalUnsaturated⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, origin, final, finalInside,
          finalSaturated, finalFree⟩⟩⟩
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, final, finalInside,
          finalWitnessed, finalUnsaturated,
          (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
            data.dischargeScale receiver final).mp finalUnsaturated⟩⟩⟩)
    dischargedFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
