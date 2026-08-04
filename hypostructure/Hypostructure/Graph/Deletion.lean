import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Hypostructure.Graph.Induced

/-!
# Primitive finite graph deletions

Vertex deletion is induced restriction to the erased full support.  Edge
deletion removes one certified Mathlib edge and retains the incoming vertex
schedule.  Neither operation carries a baseline or target assumption.
-/

namespace Hypostructure.Graph

namespace FiniteObject

/-- Delete one certified undirected edge while retaining every vertex. -/
def deleteEdge (object : FiniteObject) (edge : object.graph.edgeSet) :
    FiniteObject where
  Vertex := object.Vertex
  graph := object.graph.deleteEdges {edge.1}
  vertices := object.vertices
  decideAdj := by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel object.graph.Adj := object.decideAdj
    infer_instance

@[simp]
theorem deleteEdge_adj (object : FiniteObject)
    (edge : object.graph.edgeSet) (left right : object.Vertex) :
    (object.deleteEdge edge).graph.Adj left right ↔
      object.graph.Adj left right ∧ s(left, right) ≠ edge.1 := by
  simp [deleteEdge]

theorem deleteEdge_le (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).graph ≤ object.graph :=
  object.graph.deleteEdges_le {edge.1}

@[simp]
theorem vertexCount_deleteEdge (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).vertexCount = object.vertexCount :=
  rfl

/-- Deleting a certified edge decreases the edge count by exactly one. -/
theorem edgeCount_deleteEdge_add_one (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).edgeCount + 1 = object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {edge.1}).edgeFinset.card + 1 =
    object.graph.edgeFinset.card
  have edgeFinsetEq :
      (object.graph.deleteEdges {edge.1}).edgeFinset =
        object.graph.edgeFinset.erase edge.1 := by
    ext other
    simp [SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [edgeFinsetEq]
  exact Finset.card_erase_add_one
    (SimpleGraph.mem_edgeFinset.mpr edge.2)

theorem edgeCount_deleteEdge_lt (object : FiniteObject)
    (edge : object.graph.edgeSet) :
    (object.deleteEdge edge).edgeCount < object.edgeCount := by
  have exactDrop := object.edgeCount_deleteEdge_add_one edge
  omega

/-- Delete a vertex by inducing on the erased full support. -/
def deleteVertex (object : FiniteObject) (vertex : object.Vertex) :
    FiniteObject :=
  object.induce
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

/-- Canonical embedding of a vertex-deleted graph into its source. -/
def deleteVertexEmbedding (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).graph ↪g object.graph :=
  object.induceEmbedding
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

theorem deleteVertex_le (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).graph.map
        (object.deleteVertexEmbedding vertex).toEmbedding ≤ object.graph :=
  object.induce_le
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex)

/-- Deleting one vertex decreases the vertex count by exactly one. -/
theorem vertexCount_deleteVertex_add_one (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).vertexCount + 1 = object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  rw [deleteVertex, vertexCount_induce]
  simpa [object.card_vertexFinset] using
    Finset.card_erase_add_one (object.mem_vertexFinset vertex)

/-- Vertex deletion removes exactly the edges incident with that vertex. -/
theorem edgeCount_deleteVertex (object : FiniteObject)
    (vertex : object.Vertex) :
    (object.deleteVertex vertex).edgeCount =
      object.edgeCount - object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have supportEq :
      ((@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Finset object.Vertex) :
          Set object.Vertex) = ({vertex}ᶜ : Set object.Vertex) := by
    ext other
    simp [vertexFinset]
  rw [(object.deleteVertex vertex).edgeCount_eq_ncard_edgeSet,
    object.edgeCount_eq_ncard_edgeSet,
    object.degree_eq_ncard_neighborSet]
  change (object.graph.induce
      ((@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Finset object.Vertex) :
        Set object.Vertex)).edgeSet.ncard =
    object.graph.edgeSet.ncard - (object.graph.neighborSet vertex).ncard
  rw [supportEq]
  let complement :=
    object.graph.induce ({vertex}ᶜ : Set object.Vertex)
  have exactCount :
      complement.edgeFinset.card =
        object.graph.edgeFinset.card - object.graph.degree vertex := by
    rw [object.graph.card_edgeFinset_induce_compl_singleton,
      object.graph.card_edgeFinset_deleteIncidenceSet]
  have complementBridge :
      complement.edgeSet.ncard = complement.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have sourceBridge :
      object.graph.edgeSet.ncard = object.graph.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have degreeBridge :
      (object.graph.neighborSet vertex).ncard =
        object.graph.degree vertex := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  calc
    complement.edgeSet.ncard = complement.edgeFinset.card := complementBridge
    _ = object.graph.edgeFinset.card - object.graph.degree vertex := exactCount
    _ = object.graph.edgeSet.ncard -
        (object.graph.neighborSet vertex).ncard := by
      rw [sourceBridge, degreeBridge]

/-- Deleting a vertex drops the degree of each of its former neighbours by
exactly one; every other vertex keeps its degree
(`degree_induce_of_neighborSet_subset`). -/
theorem degree_deleteVertex_of_adj (object : FiniteObject) (vertex : object.Vertex)
    (w : (object.deleteVertex vertex).Vertex) (adj : object.graph.Adj vertex w.1) :
    (object.deleteVertex vertex).degree w + 1 = object.degree w.1 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let induced := object.deleteVertex vertex
  letI : FinEnum induced.Vertex := induced.vertices
  letI : DecidableRel induced.graph.Adj := induced.decideAdj
  rw [degree, degree]
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  classical
  have hcompl :
      Fintype.card {n : object.graph.neighborSet w.1 // (n.1 : object.Vertex) ≠ vertex} =
        Fintype.card (object.graph.neighborSet w.1) -
          Fintype.card {n : object.graph.neighborSet w.1 // (n.1 : object.Vertex) = vertex} :=
    Fintype.card_subtype_compl (fun n : object.graph.neighborSet w.1 => (n.1 : object.Vertex) = vertex)
  have hone :
      Fintype.card {n : object.graph.neighborSet w.1 // (n.1 : object.Vertex) = vertex} = 1 := by
    letI : Unique {n : object.graph.neighborSet w.1 // (n.1 : object.Vertex) = vertex} :=
      { default := ⟨⟨vertex, adj.symm⟩, rfl⟩
        uniq := fun n => Subtype.ext (Subtype.ext n.2) }
    exact Fintype.card_unique
  have hequiv :
      Fintype.card (induced.graph.neighborSet w) =
        Fintype.card
          {n : object.graph.neighborSet w.1 // (n.1 : object.Vertex) ≠ vertex} := by
    apply Fintype.card_congr
    exact
      { toFun := fun neighbor =>
          ⟨⟨neighbor.1.1, neighbor.2⟩,
            fun h => (Finset.mem_erase.mp neighbor.1.2).1 h⟩
        invFun := fun neighbor =>
          ⟨⟨neighbor.1.1,
              Finset.mem_erase.mpr
                ⟨neighbor.2, object.mem_vertexFinset neighbor.1.1⟩⟩,
            neighbor.1.2⟩
        left_inv := fun neighbor => by ext; rfl
        right_inv := fun neighbor => by ext; rfl }
  have hpos : 1 ≤ Fintype.card (object.graph.neighborSet w.1) := by
    have : Nonempty (object.graph.neighborSet w.1) := ⟨⟨vertex, adj.symm⟩⟩
    exact Fintype.card_pos
  rw [hequiv, hcompl, hone]
  omega

/-- If the deleted vertex has degree at most `k` and every one of its
neighbours had degree strictly above `k`, every vertex of the resulting
graph keeps degree at least `k` (a "safe" deletion relative to the
threshold `k`, independent of any particular application). -/
theorem degree_deleteVertex_of_safe (object : FiniteObject) (k : Nat)
    (vertex : object.Vertex) (baseline : k ≤ object.minDegree)
    (safe : ∀ w, object.graph.Adj vertex w -> k < object.degree w) :
    ∀ w : (object.deleteVertex vertex).Vertex,
      k ≤ (object.deleteVertex vertex).degree w := by
  intro w
  letI : DecidableRel object.graph.Adj := object.decideAdj
  by_cases adj : object.graph.Adj vertex w.1
  · have hdrop := object.degree_deleteVertex_of_adj vertex w adj
    have := safe w.1 adj
    omega
  · have hclosed : object.graph.neighborSet w.1 ⊆
        (@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Set object.Vertex) := by
      intro other hother
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, mem_vertexFinset,
        Set.mem_singleton_iff, true_and]
      rintro rfl
      exact adj hother.symm
    have hkeep := object.degree_induce_of_neighborSet_subset
      (@Finset.erase object.Vertex object.vertices.decEq
        object.vertexFinset vertex) w hclosed
    have hmin := object.minDegree_le_degree w.1
    change (object.deleteVertex vertex).degree w = object.degree w.1 at hkeep
    omega

/-- Deleting a "safe" vertex (degree bounded by `k`, every neighbour of
degree strictly above `k`) keeps minimum degree at least `k`.  The
witnessed neighbour (any one of the vertex's neighbours) survives deletion,
so the resulting graph is nonempty and `minDegree` is not vacuously
computed. -/
theorem minDegree_deleteVertex_of_safe (object : FiniteObject) (k : Nat)
    (vertex neighbor : object.Vertex) (hadj : object.graph.Adj vertex neighbor)
    (baseline : k ≤ object.minDegree)
    (safe : ∀ w, object.graph.Adj vertex w -> k < object.degree w) :
    k ≤ (object.deleteVertex vertex).minDegree := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (object.deleteVertex vertex).Vertex :=
    (object.deleteVertex vertex).vertices
  letI : DecidableRel (object.deleteVertex vertex).graph.Adj :=
    (object.deleteVertex vertex).decideAdj
  letI : Nonempty (object.deleteVertex vertex).Vertex :=
    ⟨⟨neighbor, Finset.mem_erase.mpr
      ⟨object.graph.ne_of_adj hadj |>.symm, object.mem_vertexFinset neighbor⟩⟩⟩
  exact (object.deleteVertex vertex).graph.le_minDegree_of_forall_le_degree k
    (object.degree_deleteVertex_of_safe k vertex baseline safe)

end FiniteObject

end Hypostructure.Graph
