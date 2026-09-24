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

/-! ## Node `[102]` → `[89]`: "recompute `L₄`" — the finite exit-`(4)` descent

Figure 8 sends the peeled receiver back to node `[89]` with its residual load
`L₄`.  `lem:typeA-exit4-finite-descent` / `lem:typeA-saturated-handoff`: each
peel strictly decreases `L₄(w)` (`lem:typeA-exit4-discharge`), so the loop
`[89] → [93]/[94] → [101] → [102] → [89]` terminates, either at a peeling
state where the receiver is still saturated but no exit-`(4)` witness of the
applicable kind remains — the hypothesis under which exits `(5)`--`(8)` are
asked — or at a peeling state where the receiver is unsaturated, where
`lem:typeA-exit4-peeling-charge` gives it nonnegative remaining charge and the
peeled loads stand in the target-defect ledger.  The descent
(`Graph.ExitFour.terminal_or_unsaturated_from`) is run at the peeling state
node `[102]` committed; every intermediate step is one more exit-`(4)` witness
at the corresponding state, so the terminal peeling set is witnessed. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitFourPeeled) known]
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, _saturated, witnessed, witness,
        _unpeeled, nextSubset, _drop⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitFourPeeled)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other => current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      -- The descent from the peeled state.
      have descent := Graph.ExitFour.terminal_or_unsaturated_from piece
        data.threshold data.dischargeScale receiver
        (Retained := Graph.ExitFour.PeeledByWitnesses
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale receiver)
        (Terminal := fun state =>
          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
              receiver state ∧
            ExitFourFreeAt data current.object piece receiver state)
        nextSubset
        (Graph.ExitFour.peeledByWitnesses_nextPeeled witnessed witness)
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
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                    receiver state,
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
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                    receiver state,
                  witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                    data.threshold data.dischargeScale receiver state
            · obtain ⟨next, _supported⟩ := occurs
              exact Or.inr ⟨next.load, next.routed, next.fresh,
                Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩
            · exact Or.inl ⟨stateSaturated, Or.inr ⟨silent, occurs⟩⟩)
      rcases descent with
        ⟨final, finalInside, _finalWitnessed, finalSaturated, finalNoWitness⟩ |
        ⟨final, finalInside, finalWitnessed, finalUnsaturated⟩
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, final, finalInside, finalSaturated,
          finalNoWitness⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, final, finalInside, finalWitnessed,
          finalUnsaturated,
          (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
            data.dischargeScale receiver final).mp finalUnsaturated⟩⟩⟩)
    freeFresh dischargedFresh

end Hypostructure.Graph.Strategy.Spine
