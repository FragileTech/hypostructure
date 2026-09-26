import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the demand ledger and node `[181]`

* `def:typeA-pressure-ledger` with `lem:typeA-pressure-ledger-no-overcount`
  and `lem:typeA-pressure-records-canonical` on the unified collection
  (`route8DemandLedger`);
* `thm:typeA-unpaid-exit4-reduction`: the one-entry augmentation (168.1)
  (`route8UnpaidTwoCarrier`), the exact node-`[181]` dichotomy
  (`route8UnpaidExitFourResidual_of_not_witnessFree`), and the identification
  of outcome (i) with the terminal input of `thm:typeA-two-carrier-nogo`
  (`route8UnpaidTrueEntry`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`def:typeA-pressure-ledger`** on the unified collection `Ξ̃`, with
`lem:typeA-pressure-ledger-no-overcount` and
`lem:typeA-pressure-records-canonical`: pinning every minimal entry with at
least `δ ≥ 3` private essential incidences, a maximal `2/3`-demand ledger
exists; its assignments satisfy the raw and defect no-overcount inequalities;
and, since the selected object has no target cycle, every unpaid
target-defect entry carries its canonical demand record. -/
theorem route8DemandLedger (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold)
    (avoids : ¬ HasCycleWithLength data.LengthOK object) :
    Route8DemandLedgerStatement data object := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  obtain ⟨P, pinnedP, maximalP⟩ :=
    Route8Census.exists_maximal_demandLedger object
      (route8UnifiedEntries data object) data.threshold data.LengthOK
      (route8DemandPinned data object)
      (fun index memPinned =>
        ((mem_route8DemandPinned data object index).mp memPinned).1)
      (fun index memPinned => by
        have bound :=
          ((mem_route8DemandPinned data object index).mp memPinned).2.2
        unfold Route8.indexedPrivateCoreCount at bound
        exact le_trans threeLe bound)
  have counts := Route8Census.demandLedger_no_overcount object
    (canonicalWindowPacking data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale data.LengthOK P
  refine ⟨⟨P, pinnedP, maximalP, counts.1, counts.2, ?_⟩⟩
  intro index _memUnion defect
  exact Route8.TraceBasin.exists_record_of_traceLocalTargetDefect defect avoids

/-- **(168.1) of `thm:typeA-unpaid-exit4-reduction`**: in a maximal ledger an
unpaid entry with three private essential incidences could be moved to `Ξ₃`
with those incidences, contradicting the first maximality coordinate.  Hence
every unpaid entry has at most two, i.e. at most `δ − 1`, private essential
incidences. -/
theorem route8UnpaidTwoCarrier (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold) :
    Route8UnpaidTwoCarrierStatement data object := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  intro P maximal index unpaid
  let entries := route8UnifiedEntries data object
  let core := route8DemandCore data object
  have privateLe :=
    DemandPartition.Partition.privateAvailable_card_le_two_of_mem_unpaid_of_maximal
      P (Route8.indexedPrivateCoreCarriers entries core) maximal.1 maximal.2
      unpaid (Route8.indexedPrivateCoreCarriers_subset_core entries core index)
      (by
        intro other otherMem otherNe
        rw [Finset.disjoint_left]
        intro carrier inPrivate inOther
        exact (Finset.mem_filter.mp inPrivate).2 other otherMem otherNe inOther)
  change Route8.indexedPrivateCoreCount entries core index ≤ data.threshold - 1
  unfold Route8.indexedPrivateCoreCount
  omega

/-- **Node `[181]` is an exact dichotomy**: the negation of outcome (i) is
outcome (ii), (168.2) on every maximal ledger. -/
theorem route8UnpaidExitFourResidual_of_not_witnessFree (data : Parameters)
    (object : FiniteObject.{u})
    (none : ¬ Route8UnpaidWitnessFreeStatement data object) :
    Route8UnpaidExitFourResidualStatement data object := by
  classical
  intro P maximal index unpaid
  by_contra absent
  exact none ⟨P, maximal, index, unpaid, absent⟩

/-- **Outcome (i) of `thm:typeA-unpaid-exit4-reduction` is the terminal input
of `thm:typeA-two-carrier-nogo`**: an unpaid entry without an exit-`(4)`
witness cannot be target-defective (the census attaches the witness to that
alternative), so its basin is target-complete-minimal; with (168.1) and the
census bound `α ≥ 2` it is the terminal true two-support route-`8` entry. -/
theorem route8UnpaidTrueEntry (data : Parameters) (object : FiniteObject.{u})
    (witnessFree : Route8UnpaidWitnessFreeStatement data object)
    (twoCarrier : Route8UnpaidTwoCarrierStatement data object)
    (census : Route8UnifiedEntryCensusFact data object) :
    Route8UnifiedTrueTwoCarrierEntryStatement data object := by
  classical
  obtain ⟨P, maximal, index, unpaid, noExitFour⟩ := witnessFree
  have indexMem : index ∈ route8UnifiedEntries data object := by
    rcases Finset.mem_union.mp unpaid with inTwo | inResidual
    · exact P.two_subset_entries inTwo
    · exact P.residual_subset_entries inResidual
  have facts := census index indexMem
  have minimal :
      Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Route8Census.basin object data.threshold index) := by
    rcases facts.2.2 with targetComplete | targetDefect
    · exact targetComplete
    · exact False.elim (noExitFour targetDefect.2.2.2.2)
  exact ⟨⟨index, indexMem, twoCarrier P maximal index unpaid, facts, minimal,
    noExitFour⟩⟩

end Hypostructure.Graph.Contracts.RouteEight
