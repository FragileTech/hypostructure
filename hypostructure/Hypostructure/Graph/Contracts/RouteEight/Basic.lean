import Hypostructure.Graph.Statements.RouteEightPinned

/-!
# Contracts: route-8 basic facts

Small proof-agnostic facts shared by the route-`8` contract lemmas: the
degree baseline at every vertex, and the unified entry family is a family of
census entries.  The canonical packing's validity and maximality are
`canonicalWindowPacking_spec`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The minimum-degree baseline at every vertex. -/
theorem degree_ge_of_minDegree (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree) (vertex : object.Vertex) :
    data.threshold ≤ object.degree vertex :=
  le_trans baseline (object.minDegree_le_degree vertex)

/-- Membership in the indexed entry family of a component collection. -/
theorem mem_entriesOfComponents {object : FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    {components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing))}
    {threshold scale : Nat} {index : Route8Census.Index object} :
    index ∈ Route8Census.entriesOfComponents object packing components
        threshold scale ↔
      ∃ component ∈ components,
        index.1 = object.pieceSupport (object.remainderSupport packing)
            component ∧
          index.2.1 ∈ VisibleEntry.saturatedReceivers object index.1 threshold
            scale ∧
          index.2.2 ∈ VisibleEntry.excessBasin object index.1 threshold scale
            index.2.1 := by
  classical
  obtain ⟨piece, receiver, load⟩ := index
  simp only [Route8Census.entriesOfComponents, Finset.mem_biUnion,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨component, componentMem, receiver', receiverMem, load', loadMem,
      rfl, rfl, rfl⟩
    exact ⟨component, componentMem, rfl, receiverMem, loadMem⟩
  · rintro ⟨component, componentMem, rfl, receiverMem, loadMem⟩
    exact ⟨component, componentMem, receiver, receiverMem, load, loadMem,
      rfl, rfl, rfl⟩

/-- The unified entry family consists of census entries: every unified
component is a negative zero-surplus canonical piece, and a saturated receiver
is a receiver. -/
theorem route8UnifiedEntries_subset_entries (data : Parameters)
    (object : FiniteObject.{u}) :
    route8UnifiedEntries data object ⊆
      Route8Census.entries object (canonicalWindowPacking data object)
        data.threshold data.dischargeScale := by
  classical
  intro index member
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp member
  apply (Route8Census.mem_entries object).2
  refine ⟨?_, (Finset.mem_filter.1 receiverMem).1, loadMem⟩
  rw [pieceEq]
  simp only [Route8Census.typeAPieces, Finset.mem_filter, Finset.mem_image]
  have selected := (Finset.mem_filter.1 componentMem).2
  exact ⟨⟨component, (Finset.mem_filter.1 componentMem).1, rfl⟩,
    selected.2.1, selected.1⟩

end Hypostructure.Graph.Contracts.RouteEight
