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

/-! ## Node `[101]`: exit `(4)`, the target-defective peeling witness

`def:typeA-saturated-exits` (4) and `def:typeA-exit4-family`: at the selected
saturated receiver and its current peeling set, does a generated
target-defective quotient of the receiver family support one of the unpeeled
routed loads under discussion?  `lem:typeA-exit4-residual-routing` names the
loads: in the visible case (a completion port carries the registered number of
unpeeled visible returns) the selected visible loads of the canonical package,
in the silent case the canonical residual excess set `E₄(w)`; the two cases are
exhaustive at a saturated receiver of exact baseline degree
(`visibleFourUnpeeled_or_silentUnpeeledExcess`, `lem:typeA-silent-excess-count`).
The yes arm is charged at node `[102]`; the no arm is the hypothesis exit `(5)`
is asked under. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedExitEntry) known]
    (exitFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedHandoffExitFour) (K .typeASaturatedHandoffExitFourFree)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedHandoffExitFour) (K .typeASaturatedHandoffExitFourFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, witnessed⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedExitEntry)).down
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
      rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
          data.threshold data.dischargeScale receiver peeled
          (exactDegree receiver isReceiver.1) isReceiver saturated with
        visible | silent
      · obtain ⟨package⟩ := Graph.ExitFour.visibleFourUnpeeledPackage piece
          data.threshold data.dischargeScale receiver peeled visible
        by_cases occurs :
            ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                receiver peeled,
              ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled,
                witness.load = load
        · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            Or.inl ⟨package, occurs⟩⟩⟩⟩
        · refine ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inl ⟨package, occurs, ?_⟩⟩⟩⟩
          rcases package.exists_witness_or_pairwise_targetComplete
              (Target := Graph.HasCycleWithLength data.LengthOK) with
            ⟨witness, selected⟩ | complete
          · exact False.elim (occurs ⟨witness, witness.load, selected, rfl⟩)
          · exact complete
      · by_cases occurs :
            ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                receiver peeled,
              witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled
        · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            Or.inr ⟨silent, occurs⟩⟩⟩⟩
        · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
