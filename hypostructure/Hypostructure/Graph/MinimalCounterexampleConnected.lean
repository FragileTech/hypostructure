import Hypostructure.Graph.Induced
import Hypostructure.Graph.Minimality

/-!
# Connectivity forced by proper-subgraph minimality

This file contains the graph-generic argument that a nonempty graph carrying a
minimum-degree baseline cannot be disconnected when every proper subgraph is
certified to fail that baseline.  The component is selected from the graph's
own ordered vertex schedule; applications supply neither a component nor a
reduction.
-/

namespace Hypostructure.Graph

universe u v w

namespace FiniteObject

/-- The first vertex in the framework-owned finite vertex schedule. -/
noncomputable def canonicalVertex (object : FiniteObject.{u})
    [Nonempty object.Vertex] : object.Vertex := by
  classical
  have orderedNonempty : object.orderedVertices ≠ [] := by
    intro empty
    let vertex : object.Vertex := Classical.choice inferInstance
    have member := object.mem_orderedVertices vertex
    simp [empty] at member
  exact object.orderedVertices.head orderedNonempty

/-- The ambient connected component of the canonical first vertex, represented
as an explicit finite support in the ambient vertex type. -/
noncomputable def canonicalComponentSupport (object : FiniteObject.{u})
    [Nonempty object.Vertex] : Finset object.Vertex := by
  classical
  exact object.vertexFinset.filter fun vertex =>
    object.graph.connectedComponentMk vertex =
      object.graph.connectedComponentMk object.canonicalVertex

@[simp]
theorem mem_canonicalComponentSupport_iff (object : FiniteObject.{u})
    [Nonempty object.Vertex] (vertex : object.Vertex) :
    vertex ∈ object.canonicalComponentSupport ↔
      object.graph.Reachable vertex object.canonicalVertex := by
  classical
  simp [canonicalComponentSupport,
    SimpleGraph.ConnectedComponent.eq]

theorem canonicalVertex_mem_canonicalComponentSupport
    (object : FiniteObject.{u}) [Nonempty object.Vertex] :
    object.canonicalVertex ∈ object.canonicalComponentSupport := by
  simp

/-- Adjacency cannot cross the selected connected component. -/
theorem neighborSet_canonicalComponent_subset
    (object : FiniteObject.{u}) [Nonempty object.Vertex]
    (vertex : (object.induce object.canonicalComponentSupport).Vertex) :
    object.graph.neighborSet vertex.1 ⊆
      (object.canonicalComponentSupport : Set object.Vertex) := by
  intro neighbor adjacent
  change neighbor ∈ object.canonicalComponentSupport
  rw [object.mem_canonicalComponentSupport_iff]
  exact (show object.graph.Adj vertex.1 neighbor from adjacent).reachable.symm.trans
    ((object.mem_canonicalComponentSupport_iff vertex.1).mp vertex.2)

/-- Inducing on the selected component preserves every vertex degree exactly. -/
theorem degree_induce_canonicalComponent
    (object : FiniteObject.{u}) [Nonempty object.Vertex]
    (vertex : (object.induce object.canonicalComponentSupport).Vertex) :
    (object.induce object.canonicalComponentSupport).degree vertex =
      object.degree vertex.1 :=
  object.degree_induce_of_neighborSet_subset
    object.canonicalComponentSupport vertex
    (object.neighborSet_canonicalComponent_subset vertex)

/-- If the ambient graph is disconnected, the canonical component omits an
ambient vertex and hence has strictly smaller cardinality. -/
theorem canonicalComponentSupport_card_lt_of_not_connected
    (object : FiniteObject.{u}) [Nonempty object.Vertex]
    (disconnected : ¬ object.graph.Connected) :
    object.canonicalComponentSupport.card < object.vertexCount := by
  classical
  have notAllReachable :
      ¬ ∀ vertex : object.Vertex,
        object.graph.Reachable object.canonicalVertex vertex := by
    intro allReachable
    apply disconnected
    exact object.graph.connected_iff_exists_forall_reachable.mpr
      ⟨object.canonicalVertex, allReachable⟩
  push Not at notAllReachable
  rcases notAllReachable with ⟨outside, unreachable⟩
  have outsideNotMem :
      outside ∉ object.canonicalComponentSupport := by
    rw [object.mem_canonicalComponentSupport_iff]
    exact fun reachable => unreachable reachable.symm
  have strict :
      object.canonicalComponentSupport ⊂ object.vertexFinset := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro vertex _
      exact object.mem_vertexFinset vertex
    · intro equal
      exact outsideNotMem (equal ▸ object.mem_vertexFinset outside)
  simpa only [object.card_vertexFinset] using Finset.card_lt_card strict

end FiniteObject

/-- A no-proper-baseline certificate forces connectivity whenever the baseline
is reconstructed uniformly from a minimum-degree threshold and the current
graph satisfies that threshold.

The nonempty hypothesis is mathematically necessary: for threshold zero, the
empty graph satisfies the minimum-degree inequality but is not connected. -/
theorem connected_of_noProperBaseline_of_minDegree
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    [Nonempty ctx.G.Vertex]
    (certificate : NoProperBaselineCertificate ctx)
    (threshold : Nat)
    (baselineOfMinDegree :
      ∀ object : FiniteObject.{u},
        threshold ≤ object.minDegree → Baseline object)
    (currentMinimumDegree : threshold ≤ ctx.G.minDegree) :
    ctx.G.graph.Connected := by
  classical
  by_contra disconnected
  let support := ctx.G.canonicalComponentSupport
  let component : ProperSubgraph ctx.G :=
    ProperSubgraph.ofInducedSupport ctx.G support
      (ctx.G.canonicalComponentSupport_card_lt_of_not_connected disconnected)
  have componentNonempty :
      Nonempty component.value.Vertex :=
    ⟨⟨ctx.G.canonicalVertex,
      ctx.G.canonicalVertex_mem_canonicalComponentSupport⟩⟩
  have componentMinimumDegree :
      threshold ≤ component.value.minDegree := by
    letI : Nonempty component.value.Vertex := componentNonempty
    apply component.value.le_minDegree_of_forall_le_degree threshold
    intro vertex
    rw [show component.value.degree vertex = ctx.G.degree vertex.1 from
      ctx.G.degree_induce_canonicalComponent vertex]
    exact currentMinimumDegree.trans (ctx.G.minDegree_le_degree vertex.1)
  exact certificate.excludes component
    (baselineOfMinDegree component.value componentMinimumDegree)

end Hypostructure.Graph
