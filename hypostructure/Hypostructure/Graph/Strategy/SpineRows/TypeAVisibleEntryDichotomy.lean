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

/-! ## Node `[93]`: does a port of the saturated receiver see `s` visible
receiver-entry returns?

`def:typeA-visible-load` counts, at each completion port of the saturated
receiver, the distinct routed loads for which some receiver-entry return through
that port is visible.  The yes arm is `lem:typeA-visible-entry`'s hypothesis and
enters the exit chain `def:typeA-saturated-exits` (1)--(7) at node `[95]`; the
no arm is node `[94]`, where `lem:typeA-silent-excess-count` turns the absence of
a visible-saturated port into the quantitative excess
`S_sil^exc(X) ≥ s·D_A(X)`.

The no arm is *proved*, not assumed: `card_le_sum_silentExcess_add_positive`
`Deficiency` is the manuscript's own count, and its three hypotheses are read
off this branch -- the support sits exactly at the baseline because it carries no
ambient surplus, the routing is total by node `[88]`'s committed fact, and no
saturated receiver has a visible-saturated port because that is the alternative
not taken.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so the exit chain cannot read the excess bound and node `[109]` cannot
read the visible-entry hypothesis. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAReceiverRouting) known]
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedReceiver) known]
    (visibleFresh : K .typeAVisibleEntry ∉ known)
    (excessFresh : K .typeAVisibleFirstExcess ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess)
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy
    (by
      classical
      letI : DecidableEq current.object.Vertex :=
        Graph.Route8.vertexDecEq current.object
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        selectedReceiver, selectedIsReceiver, selectedSaturated⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedReceiver)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have inside : piece ⊆ current.object.remainderSupport packing :=
        current.object.pieceSupport_subset
          (current.object.remainderSupport packing) component
      have routing := (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAReceiverRouting)).down
      have routed := routing packing valid maximal piece inside zero
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline
            (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other =>
                current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      have capped : ∀ vertex ∈ piece,
          current.object.internalDegree piece vertex ≤ data.threshold :=
        fun vertex member => (exactDegree vertex member) ▸
          current.object.internalDegree_le_degree piece vertex
      by_cases visible :
          ∃ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver ∧
              current.object.Saturated piece data.threshold
                  data.dischargeScale receiver ∧
              Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
                data.dischargeScale receiver ∅
      · obtain ⟨receiver, isReceiver, saturated, overloaded⟩ := visible
        exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated,
            Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver ∅ overloaded⟩⟩⟩
      · have noVisiblePorts : ∀ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver →
            current.object.Saturated piece data.threshold data.dischargeScale
              receiver →
            ∀ outside ∈ Graph.VisibleEntry.completionPorts current.object piece
              receiver,
              (Graph.VisibleEntry.visibleLoadsAt current.object piece
                data.threshold receiver outside).card + 1 ≤
                  data.dischargeScale := by
          intro receiver isReceiver saturated outside port
          have notOverloaded : ¬ data.dischargeScale ≤
              (Graph.VisibleEntry.visibleLoadsAt current.object piece
                data.threshold receiver outside).card := by
            intro overloaded
            apply visible
            refine ⟨receiver, isReceiver, saturated, outside, port, ?_⟩
            have atEmpty :
                Graph.ExitFour.unpeeledVisibleLoadsAt piece data.threshold
                    receiver outside ∅ =
                  Graph.VisibleEntry.visibleLoadsAt current.object piece
                    data.threshold receiver outside := by
              ext load
              constructor
              · intro member
                exact (Finset.mem_inter.mp member).1
              · intro member
                exact Finset.mem_inter.mpr ⟨member, by
                  simp [Graph.ExitFour.unpeeledLoads,
                    Graph.VisibleEntry.visibleLoadsAt_subset current.object
                      piece data.threshold receiver outside member]⟩
            exact atEmpty.symm ▸ overloaded
          omega
        have supportBound :=
          Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
            current.object piece data.threshold data.dischargeScale
            data.dischargeScale_pos exactDegree capped routed.1 noVisiblePorts
        have selectedAfter : Graph.ExitFour.SaturatedAfter piece data.threshold
            data.dischargeScale selectedReceiver ∅ :=
          (Graph.ExitFour.saturatedAfter_empty piece data.threshold
            data.dischargeScale selectedReceiver).mpr selectedSaturated
        have selectedSilent : Graph.ExitFour.SilentUnpeeledExcessAt piece
            data.threshold data.dischargeScale selectedReceiver ∅ := by
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
              piece data.threshold data.dischargeScale selectedReceiver ∅
              (exactDegree selectedReceiver selectedIsReceiver.1)
              selectedIsReceiver selectedAfter with overloaded | silent
          · exact False.elim (visible
              ⟨selectedReceiver, selectedIsReceiver, selectedSaturated,
                overloaded⟩)
          · exact silent
        have noVisibleAtSelected : ∀ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver →
              current.object.Saturated piece data.threshold data.dischargeScale
                receiver →
              ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
                data.dischargeScale receiver ∅ := by
          intro receiver isReceiver saturated overloaded
          exact visible ⟨receiver, isReceiver, saturated, overloaded⟩
        exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
            noVisibleAtSelected, selectedReceiver, selectedIsReceiver, selectedSaturated,
            selectedSilent, supportBound⟩⟩⟩)
    visibleFresh excessFresh

end Hypostructure.Graph.Strategy.Spine
