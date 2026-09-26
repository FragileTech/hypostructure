import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: node `[185]`, visible-first prefix exhaustion

`lem:typeA-unified-visible-overload` on the unified entry family
(`route8UnifiedVisibleOverload`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`lem:typeA-unified-visible-overload`** (node `[185]`).

The selected entries are still the literal members of the unified
visible-first excess basins.  Node `[184]` makes each such load visible.  If
its receiver had no overloaded completion port, the standard port-cap count
would put every visible load in the payable prefix, contradicting membership
in the excess basin.  Hence every entry retains the canonical actual
visible-four package, and the non-overloaded subfamily is empty. -/
theorem route8UnifiedVisibleOverload (data : Parameters)
    (object : FiniteObject.{u})
    (visible : Route8UnifiedVisibleResidualStatement data object)
    (baseline : data.threshold ≤ object.minDegree) :
    Route8UnifiedVisibleOverloadStatement data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have overloaded : ∀ index ∈ route8UnifiedEntries data object,
      ExitFour.VisibleFourUnpeeledAt index.1 data.threshold
        data.dischargeScale index.2.1 ∅ := by
    intro index indexMem
    have loadVisible := visible.1 index indexMem
    obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
      mem_entriesOfComponents.mp indexMem
    obtain ⟨piece, receiver, load⟩ := index
    simp only at pieceEq receiverMem loadMem loadVisible ⊢
    subst pieceEq
    have zeroSurplus : object.ambientSurplus
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component) data.threshold = 0 :=
      (Finset.mem_filter.mp componentMem).2.1
    have exactDegree : ∀ vertex ∈ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object))
        component, object.degree vertex = data.threshold := by
      intro vertex vertexMem
      have lower := degree_ge_of_minDegree data object baseline vertex
      have summand : object.degree vertex - data.threshold = 0 :=
        Nat.eq_zero_of_le_zero
          (zeroSurplus ▸ Finset.single_le_sum
            (f := fun other => object.degree other - data.threshold)
            (fun _ _ => Nat.zero_le _) vertexMem)
      omega
    set piece := object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component
    have receiverFacts :
        receiver ∈ object.receivers piece data.threshold ∧
          object.Saturated piece data.threshold data.dischargeScale
            receiver := by
      simpa [VisibleEntry.saturatedReceivers] using receiverMem
    have isReceiver := object.mem_receivers.mp receiverFacts.1
    by_contra noOverload
    have portCap : ∀ outside ∈
        VisibleEntry.completionPorts object piece receiver,
        (VisibleEntry.visibleLoadsAt object piece data.threshold receiver
            outside).card + 1 ≤ data.dischargeScale := by
      intro outside port
      have notLarge : ¬ data.dischargeScale ≤
          (VisibleEntry.visibleLoadsAt object piece data.threshold receiver
            outside).card := by
        intro large
        have atEmpty :
            ExitFour.unpeeledVisibleLoadsAt piece data.threshold receiver
                outside ∅ =
              VisibleEntry.visibleLoadsAt object piece data.threshold
                receiver outside := by
          ext candidate
          constructor
          · intro member
            exact (Finset.mem_inter.mp member).1
          · intro member
            exact Finset.mem_inter.mpr ⟨member, by
              simp [ExitFour.unpeeledLoads,
                VisibleEntry.visibleLoadsAt_subset object piece
                  data.threshold receiver outside member]⟩
        exact noOverload ⟨outside, port, atEmpty.symm ▸ large⟩
      omega
    have visibleBound := VisibleEntry.card_visibleLoads_le object piece
      data.threshold data.dischargeScale (exactDegree receiver isReceiver.1)
      portCap
    have receiverStrict :
        object.internalDegree piece receiver < data.threshold :=
      isReceiver.2
    have missingPositive :
        1 ≤ object.missingPorts piece data.threshold receiver := by
      unfold FiniteObject.missingPorts
      omega
    have paid :
        (VisibleEntry.visibleLoads object piece data.threshold
            receiver).card ≤
          data.dischargeScale *
              object.missingPorts piece data.threshold receiver - 1 := by
      have positiveBound :
          (VisibleEntry.visibleLoads object piece data.threshold
              receiver).card + 1 ≤
            data.dischargeScale *
              object.missingPorts piece data.threshold receiver :=
        le_trans (Nat.add_le_add_left missingPositive _) visibleBound
      omega
    have paidVisible := VisibleEntry.visibleLoads_subset_payableSet object
      piece data.threshold data.dischargeScale receiver paid loadVisible
    exact (Finset.mem_sdiff.mp loadMem).2 paidVisible
  unfold Route8UnifiedVisibleOverloadStatement
  refine ⟨fun index indexMem =>
    ExitFour.visibleFourUnpeeledPackage index.1 data.threshold
      data.dischargeScale index.2.1 ∅ (overloaded index indexMem), ?_⟩
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro index indexMem noOverload
  exact noOverload (overloaded index indexMem)

end Hypostructure.Graph.Contracts.RouteEight
