import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.TraceBasinAlternatives

/-!
# The census demand reduction: `prop:typeA-external-pressure-reduction`

After the route-8 two-support exclusion, the chosen 2/3-demand ledger
accounts for every unified entry exactly once: the pinned surviving route-8
entries are fully paid in `Ξ₃` from their private essential carriers
(`Route8Census.exists_maximal_demandLedger`), the charge accounting of the
paid classes is `Route8Census.demandLedger_no_overcount`, the class partition
is `DemandPartition.Partition.card_entries_eq`, and — this module — every
entry of `Ξ₂ ⊔ Ξ_res` is a target-defect entry carrying its canonical actual
or profile demand record (`def:typeA-two-terminal-pressure-records`,
`lem:typeA-pressure-records-canonical`).  No entry is discarded and no
incidence is counted twice.
-/

namespace Hypostructure.Graph.Route8DemandLedger

open Hypostructure
open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u})

attribute [local instance] Route8.vertexDecEq

/-- **`prop:typeA-external-pressure-reduction`, the record row**: on a
clause-(L1) ledger pinning the surviving route-8 entries, every entry of
`Ξ₂ ∪ Ξ_res` is a target-defect entry and carries its canonical actual or
profile demand record at its selected basin. -/
theorem records_of_two_residual (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (P : DemandPartition.Partition
      (Route8Census.entries object packing threshold discharge)
      (Route8Census.core object threshold LengthOK))
    (pinned : Finset (Route8Census.Index object))
    (pinnedThree : pinned ⊆ P.three)
    (unpinnedDefect : ∀ index ∈
        Route8Census.entries object packing threshold discharge,
      index ∉ pinned →
      Route8.TraceBasin.TraceLocalTargetDefect object index.1 threshold
        LengthOK index.2.1 index.2.2
        (Route8Census.basin object threshold index)) :
    ∀ index ∈ P.two ∪ P.residual,
      Route8.TraceBasin.CanonicalDemandRecord object
        (Route8Census.basin object threshold index) LengthOK := by
  classical
  intro index memUnion
  have memEntries : index ∈
      Route8Census.entries object packing threshold discharge := by
    rcases Finset.mem_union.mp memUnion with mem | mem
    · exact P.two_subset_entries mem
    · exact P.residual_subset_entries mem
  have notThree : index ∉ P.three := by
    intro three
    rcases Finset.mem_union.mp memUnion with mem | mem
    · exact (Finset.disjoint_left.mp P.three_disj_two) three mem
    · exact (Finset.disjoint_left.mp P.three_disj_residual) three mem
  have notPinned : index ∉ pinned := fun mem => notThree (pinnedThree mem)
  exact Route8.TraceBasin.exists_record_of_traceLocalTargetDefect
    (unpinnedDefect index memEntries notPinned) avoids

end Hypostructure.Graph.Route8DemandLedger
