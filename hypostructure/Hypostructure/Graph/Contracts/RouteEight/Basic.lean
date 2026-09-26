import Hypostructure.Graph.Statements.RouteEight

/-!
# Contracts: route-8 basic facts

Small proof-agnostic facts shared by the route-`8` contract lemmas: the
canonical window packing is a maximal valid packing, and the unified entry
family is a family of census entries.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The canonical window packing is a valid packing of maximum size, hence
maximal: every induced window meets one of its windows. -/
theorem canonicalWindowPacking_valid_maximal (data : Parameters)
    (object : FiniteObject.{u}) :
    object.IsWindowPacking data.windowOrder (canonicalWindowPacking data object) ∧
      ∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
          ∃ member ∈ canonicalWindowPacking data object, ¬ Disjoint window member := by
  have packingSpec := Classical.choose_spec
    (object.exists_windowPacking_card_eq data.windowOrder)
  refine ⟨packingSpec.1, fun window induces => ?_⟩
  exact object.exists_mem_not_disjoint_of_card_eq data.windowOrder_pos
    packingSpec.1 packingSpec.2 induces

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
