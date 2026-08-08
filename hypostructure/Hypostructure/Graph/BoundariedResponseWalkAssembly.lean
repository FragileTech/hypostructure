import Hypostructure.Graph.Strategy.InterfaceReplacement

namespace Hypostructure.Graph.BoundariedResponseWalkAssembly

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {object : FiniteObject.{u}}

namespace SupportAtom

variable (object) (support : Finset object.Vertex)

/-- Encode a supported ambient vertex in the atom side of the canonical cut
decomposition. -/
noncomputable def pieceVertex
    (vertex : {vertex : object.Vertex // vertex ∈ support}) :
    (SupportAtom.boundary object support).Vertex ⊕
      (SupportAtom.piece object support).Internal := by
  classical
  by_cases boundaryMember :
      vertex.1 ∈ SupportAtom.cutBoundary object support
  · exact .inl ⟨vertex.1, boundaryMember⟩
  · exact .inr ⟨vertex.1, vertex.2, boundaryMember⟩

@[simp] theorem pieceDecode_pieceVertex
    (vertex : {vertex : object.Vertex // vertex ∈ support}) :
    SupportAtom.pieceDecode object support
        (pieceVertex object support vertex) = vertex.1 := by
  classical
  by_cases boundaryMember :
      vertex.1 ∈ SupportAtom.cutBoundary object support
  · simp [pieceVertex, boundaryMember, SupportAtom.pieceDecode]
  · simp [pieceVertex, boundaryMember, SupportAtom.pieceDecode]

/-- Canonical inclusion of the induced support graph into its atom-side
boundary piece. -/
noncomputable def inducedToPieceHom :
    object.graph.induce (↑support : Set object.Vertex) →g
      (SupportAtom.piece object support).graph :=
  ⟨fun vertex => pieceVertex object support vertex, by
    intro left right adjacent
    change object.graph.Adj
      (SupportAtom.pieceDecode object support
        (pieceVertex object support left))
      (SupportAtom.pieceDecode object support
        (pieceVertex object support right))
    simpa using adjacent⟩

/-- A walk whose complete support belongs to the selected atom. -/
structure AtomOwnedWalk {start finish : object.Vertex} where
  walk : object.graph.Walk start finish
  owned : ∀ vertex ∈ walk.support, vertex ∈ support

namespace AtomOwnedWalk

variable {object support} {start finish : object.Vertex}

/-- The ambient walk restricted to the induced graph on its owning support. -/
noncomputable def inInduced
    (ownedWalk : AtomOwnedWalk object support (start := start) (finish := finish)) :
    (object.graph.induce (↑support : Set object.Vertex)).Walk
      ⟨start, ownedWalk.owned start ownedWalk.walk.start_mem_support⟩
      ⟨finish, ownedWalk.owned finish ownedWalk.walk.end_mem_support⟩ :=
  ownedWalk.walk.induce (↑support : Set object.Vertex) ownedWalk.owned

theorem inInduced_length
    (ownedWalk : AtomOwnedWalk object support (start := start) (finish := finish)) :
    ownedWalk.inInduced.length = ownedWalk.walk.length := by
  unfold inInduced
  have mapped := SimpleGraph.Walk.length_map
    (f := (SimpleGraph.Embedding.induce
      (↑support : Set object.Vertex)).toHom)
    (p := ownedWalk.walk.induce (↑support : Set object.Vertex) ownedWalk.owned)
  rw [SimpleGraph.Walk.map_induce] at mapped
  exact mapped.symm

/-- The literal walk in the canonical atom-side graph. -/
noncomputable def inPiece
    (ownedWalk : AtomOwnedWalk object support (start := start) (finish := finish)) :
    (SupportAtom.piece object support).graph.Walk
      ((inducedToPieceHom object support)
        ⟨start, ownedWalk.owned start ownedWalk.walk.start_mem_support⟩)
      ((inducedToPieceHom object support)
        ⟨finish, ownedWalk.owned finish ownedWalk.walk.end_mem_support⟩) :=
  ownedWalk.inInduced.map
    (inducedToPieceHom object support)

theorem inPiece_length
    (ownedWalk : AtomOwnedWalk object support (start := start) (finish := finish)) :
    ownedWalk.inPiece.length = ownedWalk.walk.length := by
  unfold inPiece
  rw [SimpleGraph.Walk.length_map, inInduced_length]

end AtomOwnedWalk

/-- A walk owned by the outside side until its terminal cut-boundary entry. -/
structure ContextEntryWalk {start entry : object.Vertex} where
  walk : object.graph.Walk start entry
  entryBoundary : entry ∈ SupportAtom.cutBoundary object support
  outsideBeforeEntry : ∀ vertex ∈ walk.support, vertex ≠ entry →
    vertex ∉ support

namespace ContextEntryWalk

variable {object support} {start entry : object.Vertex}

noncomputable def contextVertex
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry))
    (vertex : object.Vertex) (member : vertex ∈ ownedWalk.walk.support) :
    (SupportAtom.boundary object support).Vertex ⊕
      SupportAtom.OutsideInternal object support := by
  classical
  by_cases terminal : vertex = entry
  · exact .inl ⟨entry, ownedWalk.entryBoundary⟩
  · exact .inr ⟨vertex,
      ownedWalk.outsideBeforeEntry vertex member terminal⟩

@[simp] theorem outsideDecode_contextVertex
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry))
    (vertex : object.Vertex) (member : vertex ∈ ownedWalk.walk.support) :
    SupportAtom.outsideDecode object support
        (ownedWalk.contextVertex vertex member) = vertex := by
  classical
  by_cases terminal : vertex = entry
  · subst vertex
    simp [contextVertex, SupportAtom.outsideDecode]
  · simp [contextVertex, SupportAtom.outsideDecode, terminal]

private noncomputable def toOutsideHom
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry)) :
    ownedWalk.walk.toSubgraph.coe →g
      (SupportAtom.outside object support).graph :=
  ⟨fun vertex => ownedWalk.contextVertex vertex.1
      (ownedWalk.walk.mem_verts_toSubgraph.mp vertex.2), by
    intro left right adjacent
    change object.graph.Adj
      (SupportAtom.outsideDecode object support
        (ownedWalk.contextVertex left.1
          (ownedWalk.walk.mem_verts_toSubgraph.mp left.2)))
      (SupportAtom.outsideDecode object support
        (ownedWalk.contextVertex right.1
          (ownedWalk.walk.mem_verts_toSubgraph.mp right.2)))
    simpa using ownedWalk.walk.toSubgraph.adj_sub adjacent⟩

private theorem mapToSubgraph_length
    (walk : object.graph.Walk start entry) :
    walk.mapToSubgraph.length = walk.length := by
  have mapped := SimpleGraph.Walk.length_map
    (f := walk.toSubgraph.hom) (p := walk.mapToSubgraph)
  rw [walk.map_mapToSubgraph_hom] at mapped
  exact mapped.symm

/-- The literal walk in the canonical outside-context graph. -/
noncomputable def inContext
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry)) :
    (SupportAtom.outside object support).graph.Walk
      (ownedWalk.contextVertex start ownedWalk.walk.start_mem_support)
      (ownedWalk.contextVertex entry ownedWalk.walk.end_mem_support) :=
  (ownedWalk.walk.mapToSubgraph.map ownedWalk.toOutsideHom).copy
    (by rfl) (by rfl)

theorem inContext_length
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry)) :
    ownedWalk.inContext.length = ownedWalk.walk.length := by
  unfold inContext
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map,
    mapToSubgraph_length]

@[simp] theorem contextVertex_entry
    (ownedWalk : ContextEntryWalk object support (start := start) (entry := entry)) :
    ownedWalk.contextVertex entry ownedWalk.walk.end_mem_support =
      .inl ⟨entry, ownedWalk.entryBoundary⟩ := by
  simp [contextVertex]

end ContextEntryWalk
end SupportAtom

end Hypostructure.Graph.BoundariedResponseWalkAssembly
