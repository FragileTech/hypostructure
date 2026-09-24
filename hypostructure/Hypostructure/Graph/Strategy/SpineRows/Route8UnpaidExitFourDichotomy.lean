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

/-! ## Node 183: maximal-ledger exit-(4) reduction

The first descendant of node 181 uses the first coordinate of the demand
ledger's lexicographic maximality.  A one-entry augmentation proves that every
entry in Xi2 union Xi-res is two-carrier.  The unified census then gives the
exact dichotomy: a no-witness entry is the already closed node-124 input;
otherwise every unpaid entry carries its canonical exit-(4) witness.  The
right arm therefore removes both the high-private-carrier and true-route-8
possibilities without deleting any entry or any inherited key. -/
set_option maxHeartbeats 20000000 in
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8UnpaidExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8PeeledDemandResidual) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8UnifiedEntryCensus) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8ExtractedEntryCensus) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .selection) known]
    (survivorFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (residualFresh : K .route8UnpaidExitFourResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8UnifiedTrueTwoCarrierEntry)
      (K .route8UnpaidExitFourResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    factSystem BranchState Presentation presentation data
  let alternatives :
      Sum
        (PLift (Route8UnifiedTrueTwoCarrierEntryStatement data current.object))
        (PLift (Route8UnpaidExitFourResidualStatement data current.object)) := by
      classical
      apply Classical.choice
      letI : DecidableEq current.object.Vertex :=
        Graph.Route8.vertexDecEq current.object
      let entries := route8UnifiedEntries data current.object
      let core := route8DemandCore data current.object
      have node181 :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .route8PeeledDemandResidual)).down
      have census :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .route8UnifiedEntryCensus)).down
      have demand : Route8DemandLedgerStatement data current.object :=
        node181.2.1
      obtain ⟨P, pinnedP, maximalP, _raw, _defect, _records⟩ :=
        Classical.choice demand
      have twoCarrier : ∀ index ∈ P.two ∪ P.residual,
          Graph.Route8.IndexedTwoCarrierCore entries core
            (data.threshold - 1) index := by
        intro index unpaid
        have privateLe :=
          Graph.DemandPartition.Partition.privateAvailable_card_le_two_of_mem_unpaid_of_maximal
              P (Graph.Route8.indexedPrivateCoreCarriers entries core)
              pinnedP maximalP unpaid
              (Graph.Route8.indexedPrivateCoreCarriers_subset_core
                entries core index)
              (by
                intro other otherMem otherNe
                rw [Finset.disjoint_left]
                intro carrier inPrivate inOther
                exact (Finset.mem_filter.mp inPrivate).2 other otherMem
                  otherNe inOther)
        simpa [Graph.Route8.IndexedTwoCarrierCore,
          Graph.Route8.indexedPrivateCoreCount, data.threshold_eq_three] using
          privateLe
      by_cases noWitness : ∃ index ∈ P.two ∪ P.residual,
          ¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
              data.dischargeScale index.2.1 ∅,
            witness.load = index.2.2
      · obtain ⟨index, unpaid, noExitFour⟩ := noWitness
        have indexMem : index ∈ entries := by
          rcases Finset.mem_union.mp unpaid with inTwo | inResidual
          · exact P.two_subset_entries inTwo
          · exact P.residual_subset_entries inResidual
        have facts := census index indexMem
        have minimal :
            Graph.Route8.TraceBasin.TargetCompleteMinimal current.object
              index.1 data.threshold data.LengthOK index.2.1 index.2.2
              (Graph.Route8Census.basin current.object data.threshold index) := by
          rcases facts.2.2 with targetComplete | targetDefect
          · exact targetComplete
          · exact False.elim (noExitFour targetDefect.2.2.2.2)
        exact ⟨.inl ⟨⟨⟨index, indexMem, twoCarrier index unpaid, facts,
          minimal, noExitFour⟩⟩⟩⟩
      · refine ⟨.inr ⟨⟨⟨P, pinnedP, maximalP, ?_⟩⟩⟩⟩
        intro index unpaid
        refine ⟨twoCarrier index unpaid, ?_⟩
        have atEmpty : ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
              data.dischargeScale index.2.1 ∅,
            witness.load = index.2.2 := by
          by_contra absent
          exact noWitness ⟨index, unpaid, absent⟩
        obtain ⟨witness, witnessLoad⟩ := atEmpty
        intro peeled unpeeled
        refine ⟨{
          load := witness.load
          unpeeled := ?_
          member := witness.member }, witnessLoad⟩
        simpa only [witnessLoad] using unpeeled
  Decision.run previous (K .route8UnifiedTrueTwoCarrierEntry)
    (K .route8UnpaidExitFourResidual)
    `Hypostructure.Graph.Strategy.Spine.route8UnpaidExitFourDichotomy
    alternatives survivorFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
