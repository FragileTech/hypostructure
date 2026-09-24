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

/-! The clause-(L1) dichotomy of `def:typeA-pressure-ledger`, at the
failed-rate stage of `thm:large-budget-route8-only`.  A minimal unified entry
holding at most `δ − 1` private essential incidences and no exit-(4) witness
is the terminal two-support route-8 obstruction — the left arm republishes
exactly the `[124]` survivor fact, and `route8UnifiedTerminalNoGoRow` closes
it.  Otherwise the maximal pinned 2/3-demand ledger over the unified
collection exists — pinning every minimal entry with `δ` or more private
incidences, maximizing first `N₃` then `N₂` — with the raw no-overcount
counts of `lem:typeA-pressure-ledger-no-overcount` and the canonical demand
records of `lem:typeA-pressure-records-canonical` on the unpaid target-defect
entries; the right arm publishes that ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8DemandLedgerDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .selection) known]
    (survivorFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (ledgerFresh : K .route8DemandLedger ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8UnifiedTrueTwoCarrierEntry) (K .route8DemandLedger)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8UnifiedTrueTwoCarrierEntry) (K .route8DemandLedger)
    `Hypostructure.Graph.Strategy.Spine.route8DemandLedgerDichotomy
    (by
      classical
      apply Classical.choice
      letI : DecidableEq current.object.Vertex :=
        Graph.Route8.vertexDecEq current.object
      by_cases survivor :
          Route8UnifiedTrueTwoCarrierEntryStatement data current.object
      · exact ⟨.inl ⟨survivor⟩⟩
      ·
        have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
            current.object :=
          (@ExactLedger.get (Input BranchState Presentation presentation data)
            _ (factSystem BranchState Presentation presentation data)
            current known previous (K .selection)).down.1
        obtain ⟨P, pinnedP, maximalP⟩ :=
          Graph.Route8Census.exists_maximal_demandLedger current.object
            (route8UnifiedEntries data current.object) data.threshold
            data.LengthOK
            (route8DemandPinned data current.object)
            (by
              intro index memPinned
              exact (mem_route8DemandPinned data current.object index).mp
                memPinned |>.1)
            (fun index memPinned => by
              have bound :=
                ((mem_route8DemandPinned data current.object index).mp
                  memPinned).2.2
              unfold Graph.Route8.indexedPrivateCoreCount at bound
              exact le_trans data.three_le_threshold bound)
        have counts := Graph.Route8Census.demandLedger_no_overcount
          current.object (canonicalWindowPacking data current.object)
          (route8UnifiedComponents data current.object)
          data.threshold data.dischargeScale data.LengthOK P
        refine ⟨.inr ⟨⟨⟨P, pinnedP, maximalP, counts.1, counts.2, ?_⟩⟩⟩⟩
        intro index _memUnion defect
        exact Graph.Route8.TraceBasin.exists_record_of_traceLocalTargetDefect
          defect avoids)
    survivorFresh ledgerFresh

end Hypostructure.Graph.Strategy.Spine
