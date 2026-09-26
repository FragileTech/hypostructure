import Hypostructure.Graph.Contracts.RouteEight.Terminal

/-!
# Contracts: node `[118]`, the selected two-carrier entry

At the two-support entry selected by node `[117]` on the route-`8`
collection `𝒳_A`:

* the entry is a true route-`8` entry: `K .route8TrueResidual`'s absence of
  the canonical exit-`(4)` family, read at that entry
  (`route8TrueTwoCarrierEntry`);
* its canonical essential core carries the declared carrier-deletion
  witnesses (`route8CarrierDeletionWitnesses`).

This module imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[118]`: the selected two-support entry is a true route-8 entry.**
On the pure collection selected at `[111]`, the true route-`8` residual
records clauses (R1)--(R4), including the absence of the canonical
exit-`(4)` family; at the entry selected by `[117]` the load's silent excess is
its excess basin (every vertex of a zero-surplus piece has degree exactly the
threshold), so that no-exit fact applies to the selected entry.  The
target-defect alternative belongs only to the unified peeling ledger of
`[123]`. -/
theorem trueTwoCarrierEntry_at (data : Parameters)
    (object : FiniteObject.{u})
    (trueResidual : Route8TrueResidual data object)
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale)
    {index : Graph.Route8Census.Index object}
    (selected : Route8TwoCarrierEntrySpec data object index) :
    ¬ ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
        index.1 data.threshold data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2 := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨indexMem, _two⟩ := selected
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp indexMem
  have survives := (Finset.mem_filter.mp componentMem).2
  have componentFacts := trueResidual component componentMem
  have receiverFacts := componentFacts.2 index.2.1 (pieceEq ▸ receiverMem)
  have exactDegree : ∀ vertex ∈ object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component,
      object.degree vertex = data.threshold := by
    intro vertex vertexMem
    have nonneg := degree_ge_of_minDegree data object baseline vertex
    have summand : object.degree vertex - data.threshold = 0 :=
      Nat.eq_zero_of_le_zero
        (survives.2.1 ▸ Finset.single_le_sum
          (f := fun other => object.degree other - data.threshold)
          (fun _ _ => Nat.zero_le _) vertexMem)
    omega
  have silentLoadMem : index.2.2 ∈ Graph.VisibleEntry.silentExcess object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold data.dischargeScale index.2.1 := by
    rw [Graph.VisibleEntry.silentExcess_eq_excessBasin object _ data.threshold
      data.dischargeScale (exactDegree index.2.1 receiverFacts.1.1)
      receiverFacts.1 scalePos
      (fun saturated => componentFacts.1 index.2.1 receiverFacts.1 saturated)]
    exact pieceEq ▸ loadMem
  have noExitFour := (receiverFacts.2.2 index.2.2 silentLoadMem).2.2
  exact pieceEq ▸ noExitFour

/-- **Node `[118]` at `ι₂`**: the two-support entry of `𝒳_A` fixed by node
`[117]` is a true route-`8` entry.  On the pure collection selected at `[111]`
the true route-`8` residual records (R2), the absence of the canonical
exit-`(4)` family, and at `ι₂` the load's silent excess is its excess basin
(every vertex of a zero-surplus piece has degree exactly the threshold). -/
theorem route8TrueTwoCarrierEntry (data : Parameters)
    (object : FiniteObject.{u})
    (selected : Route8TwoCarrierEntryStatement data object)
    (trueResidual : Route8TrueResidual data object)
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale) :
    Route8TrueTwoCarrierEntryStatement data object := by
  obtain ⟨index, pin, spec⟩ := canonicalRoute8TwoCarrierIndex_spec data object
    ((route8TwoCarrierEntry_iff_exists_spec data object).mp selected)
  exact ⟨index, pin,
    trueTwoCarrierEntry_at data object trueResidual baseline scalePos spec⟩

/-- **Node `[118]`, clause (T5) of `def:typeA-terminal-two-carrier`, at `ι₂`**:
the declared deletion witnesses of the canonical essential core of the
two-support entry fixed by node `[117]`. -/
theorem route8CarrierDeletionWitnesses (data : Parameters)
    (object : FiniteObject.{u})
    (selected : Route8TwoCarrierEntryStatement data object) :
    Route8CarrierDeletionWitnesses data object := by
  obtain ⟨index, pin, spec⟩ := canonicalRoute8TwoCarrierIndex_spec data object
    ((route8TwoCarrierEntry_iff_exists_spec data object).mp selected)
  exact ⟨index, pin, twoCarrier_deletionWitnesses data.LengthOK object
    (canonicalWindowPacking data object) (route8SurvivorComponents data object)
    data.threshold data.dischargeScale spec.2⟩

end Hypostructure.Graph.Contracts.RouteEight
