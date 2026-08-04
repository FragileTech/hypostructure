import Mathlib.Combinatorics.SimpleGraph.Circulant
import Hypostructure.Graph.Deletion
import Hypostructure.Graph.Target
import Hypostructure.Graph.DeletionCriticality

/-!
# Graph layer bootstrap fixtures

These examples exercise the packed representation, induced restriction,
isomorphism transport, exact deletion accounting, and direct cycle targets on
small concrete graphs.
-/

namespace Hypostructure.Fixtures.GraphBasics

open Graph

/-- The complete graph on four explicitly scheduled vertices. -/
abbrev k4 : FiniteObject where
  Vertex := Fin 4
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

theorem k4_vertexCount : k4.vertexCount = 4 := by
  simp [k4, FiniteObject.vertexCount]

theorem k4_edgeCount : k4.edgeCount = 6 := by
  change (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  decide

theorem k4_degree (vertex : k4.Vertex) : k4.degree vertex = 3 := by
  change (⊤ : SimpleGraph (Fin 4)).degree vertex = 3
  simp

/-- A concrete three-vertex support inside `k4`. -/
def firstThree : Finset (Fin 4) := {0, 1, 2}

theorem firstThree_card : firstThree.card = 3 := by
  decide

theorem k4_induced_vertexCount :
    (k4.induce firstThree).vertexCount = 3 := by
  rw [FiniteObject.vertexCount_induce, firstThree_card]

theorem k4_induced_embedding_reflects_adjacency
    (left right : (k4.induce firstThree).Vertex)
    (adjacent : (k4.induce firstThree).graph.Adj left right) :
    k4.graph.Adj (k4.induceEmbedding firstThree left)
      (k4.induceEmbedding firstThree right) :=
  (k4.induceEmbedding firstThree).toHom.map_adj adjacent

/-- A nonidentity relabeling of `k4`. -/
def swapFirstTwo : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

def k4RelabelIso : k4.Iso k4 := by
  change (⊤ : SimpleGraph (Fin 4)) ≃g (⊤ : SimpleGraph (Fin 4))
  exact SimpleGraph.Iso.completeGraph swapFirstTwo

theorem k4_relabel_preserves_edgeCount :
    k4.edgeCount = k4.edgeCount :=
  FiniteObject.edgeCount_eq_of_iso k4RelabelIso

/-- One certified edge of `k4`. -/
def k4Edge : k4.graph.edgeSet :=
  ⟨s((0 : Fin 4), (1 : Fin 4)), by
    change (⊤ : SimpleGraph (Fin 4)).Adj 0 1
    decide⟩

theorem k4_deleteEdge_edgeCount :
    (k4.deleteEdge k4Edge).edgeCount = 5 := by
  have exactDrop := k4.edgeCount_deleteEdge_add_one k4Edge
  rw [k4_edgeCount] at exactDrop
  omega

theorem k4_deleteVertex_vertexCount :
    (k4.deleteVertex (0 : Fin 4)).vertexCount = 3 := by
  have exactDrop := k4.vertexCount_deleteVertex_add_one (0 : Fin 4)
  rw [k4_vertexCount] at exactDrop
  omega

/-- The canonical four-cycle with its deterministic finite data. -/
abbrev c4 : FiniteObject where
  Vertex := Fin 4
  graph := SimpleGraph.cycleGraph 4
  vertices := inferInstance
  decideAdj := inferInstance

def c4Certificate : CycleCertificate c4 (fun length => length = 4) where
  vertex := (0 : Fin 4)
  walk := SimpleGraph.cycleGraph.cycle 1
  isCycle := SimpleGraph.cycleGraph.isCycle_cycle
  length_ok := by
    exact SimpleGraph.cycleGraph.length_cycle

theorem c4_has_four_cycle :
    HasCycleWithLength (fun length => length = 4) c4 :=
  ⟨c4Certificate⟩

/-! ## A cycle certificate inside a graph that is not itself a cycle

`c4Certificate` reads its cycle off the cycle graph, where the whole object is
the certificate.  The certificate below is the harder direction the target
interface actually has to support: a literal accepted closed walk selected
inside a denser object, together with the minimum-degree baseline that object
satisfies.  Both are checked by the kernel, with no numeric parameter beyond
the accepted length itself. -/

/-- The literal closed walk `0-1-2-3-0` inside the complete graph `k4`. -/
def k4FourCycle : k4.graph.Walk (0 : Fin 4) (0 : Fin 4) :=
  .cons (v := 1) (by change (⊤ : SimpleGraph (Fin 4)).Adj 0 1; decide)
    (.cons (v := 2) (by change (⊤ : SimpleGraph (Fin 4)).Adj 1 2; decide)
      (.cons (v := 3) (by change (⊤ : SimpleGraph (Fin 4)).Adj 2 3; decide)
        (.cons (v := 0) (by change (⊤ : SimpleGraph (Fin 4)).Adj 3 0; decide)
          .nil)))

theorem k4FourCycle_length : k4FourCycle.length = 4 :=
  rfl

theorem k4FourCycle_isCycle : k4FourCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

/-- The selected walk is an accepted cycle certificate for `k4`. -/
def k4Certificate : CycleCertificate k4 (fun length => length = 4) where
  vertex := (0 : Fin 4)
  walk := k4FourCycle
  isCycle := k4FourCycle_isCycle
  length_ok := k4FourCycle_length

theorem k4_has_four_cycle :
    HasCycleWithLength (fun length => length = 4) k4 :=
  ⟨k4Certificate⟩

/-- `k4` realizes the minimum-degree-three baseline. -/
theorem k4_minimumDegreeAtLeast_three : MinimumDegreeAtLeast 3 k4 := by
  change 3 ≤ (⊤ : SimpleGraph (Fin 4)).minDegree
  simp

/-- A simple baseline used to exercise Core semantic-equivalence registration. -/
def AtLeastTwoVertices (object : FiniteObject) : Prop :=
  2 ≤ object.vertexCount

def atLeastTwoVerticesInvariant :
    FiniteObject.IsomorphismInvariant AtLeastTwoVertices where
  iff_of_iso := by
    intro left right equivalent
    rw [AtLeastTwoVertices, AtLeastTwoVertices,
      FiniteObject.vertexCount_eq_of_isomorphic equivalent]

def graphSemantics :=
  isomorphismEquivalence AtLeastTwoVertices (fun _ => Unit)
    atLeastTwoVerticesInvariant

def fourCycleCoreInvariant :
    Core.TargetInvariant graphSemantics
      (HasCycleWithLength (fun length => length = 4)) :=
  (cycleTargetInterface (fun length => length = 4)).coreInvariant
    AtLeastTwoVertices (fun _ => Unit) atLeastTwoVerticesInvariant

#print axioms k4_induced_vertexCount
#print axioms k4_deleteEdge_edgeCount
#print axioms c4_has_four_cycle
#print axioms k4_has_four_cycle
#print axioms k4_minimumDegreeAtLeast_three
#print axioms fourCycleCoreInvariant

end Hypostructure.Fixtures.GraphBasics
