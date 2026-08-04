/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT11 -> CT6).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Graph.Strategy.Official.Features.CanonicalConnectedSupportHull

/-!
# Canonical cut-boundary decomposition of a connected support

The interface is exactly the ambient cut boundary computed by
`CanonicalConnectedSupportHull.boundary`.  Piece internals are support
vertices outside that boundary, and outside internals are the complement.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.CanonicalSupportDecomposition

open Hypostructure.Graph
open Hypostructure.Graph.SupportComponents.Connected
open CanonicalConnectedSupportHull

universe u

variable (object : FiniteObject.{u}) (support : Finset object.Vertex)

/-- Exhaustive scope split for a selected support.  Properness is discovered
by Graph; callers cannot choose whether the support is treated as a proper
atom or as the closed ambient carrier. -/
inductive Scope where
  | proper (vertex : object.Vertex) (outside : vertex ∉ support)
  | closed (covers : ∀ vertex, vertex ∈ support)

noncomputable def classifyScope : Scope object support := by
  classical
  by_cases proper : ∃ vertex, vertex ∉ support
  · let vertex := Classical.choose proper
    exact .proper vertex (Classical.choose_spec proper)
  · exact .closed (by
      intro vertex
      by_contra outside
      exact proper ⟨vertex, outside⟩)

abbrev BoundaryVertex :=
  {vertex : object.Vertex // vertex ∈ Presentation.boundary object support}

abbrev PieceInternal :=
  {vertex : object.Vertex //
    vertex ∈ support ∧ vertex ∉ Presentation.boundary object support}

abbrev OutsideInternal :=
  {vertex : object.Vertex // vertex ∉ support}

noncomputable def boundary : Boundary.{u} where
  Vertex := BoundaryVertex object support
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ Presentation.boundary object support

private def pieceDecode :
    (boundary object support).Vertex ⊕ PieceInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

private def outsideDecode :
    (boundary object support).Vertex ⊕ OutsideInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

noncomputable def piece : BoundaryPiece (boundary object support) where
  Internal := PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧ vertex ∉ Presentation.boundary object support
  graph := SimpleGraph.comap (pieceDecode object support) object.graph
  decideAdj := Classical.decRel _

noncomputable def outside :
    OutsideContext (boundary object support) where
  Internal := OutsideInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex => vertex ∉ support
  graph := SimpleGraph.comap (outsideDecode object support) object.graph
  decideAdj := Classical.decRel _

/-- Canonical piece vertex corresponding to a supported ambient vertex. -/
noncomputable def supportIntoPiece
    (vertex : {vertex : object.Vertex // vertex ∈ support}) :
    (piece object support).pack.Vertex := by
  classical
  by_cases onBoundary :
      vertex.1 ∈ Presentation.boundary object support
  · exact .inl ⟨vertex.1, onBoundary⟩
  · exact .inr ⟨vertex.1, vertex.2, onBoundary⟩

/-- Ambient value of a canonical piece vertex. -/
def pieceVertexValue :
    (piece object support).pack.Vertex → object.Vertex :=
  pieceDecode object support

@[simp] theorem pieceVertexValue_supportIntoPiece
    (vertex : {vertex : object.Vertex // vertex ∈ support}) :
    pieceVertexValue object support (supportIntoPiece object support vertex) =
      vertex.1 := by
  classical
  by_cases onBoundary :
      vertex.1 ∈ Presentation.boundary object support
  · simp [supportIntoPiece, onBoundary, pieceVertexValue, pieceDecode]
  · simp [supportIntoPiece, onBoundary, pieceVertexValue, pieceDecode]

/-- Piece interiors cannot meet the outside by an ambient edge: such an
incidence would put the piece endpoint in the literal cut boundary. -/
theorem not_adj_pieceInternal_outside
    (inside : PieceInternal object support)
    (outsideVertex : OutsideInternal object support) :
    ¬ object.graph.Adj inside.1 outsideVertex.1 := by
  intro adjacent
  exact inside.2.2
    ((Presentation.mem_boundary_iff object support inside.1).2
      ⟨inside.2.1, outsideVertex.1, adjacent, outsideVertex.2⟩)

private def gluedDecode :
    GluedVertex (piece object support) (outside object support) →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr (.inl vertex) => vertex.1
  | .inr (.inr vertex) => vertex.1

private noncomputable def gluedEncode :
    object.Vertex →
      GluedVertex (piece object support) (outside object support) := by
  classical
  intro vertex
  by_cases onBoundary : vertex ∈ Presentation.boundary object support
  · exact .inl ⟨vertex, onBoundary⟩
  · by_cases inSupport : vertex ∈ support
    · exact .inr (.inl ⟨vertex, inSupport, onBoundary⟩)
    · exact .inr (.inr ⟨vertex, inSupport⟩)

private noncomputable def vertexEquiv :
    GluedVertex (piece object support) (outside object support) ≃
      object.Vertex where
  toFun := gluedDecode object support
  invFun := gluedEncode object support
  left_inv := by
    classical
    intro vertex
    rcases vertex with boundaryVertex | internal
    · simp [gluedDecode, gluedEncode, boundaryVertex.2]
    · rcases internal with pieceVertex | outsideVertex
      · have notBoundary := pieceVertex.2.2
        have inSupport := pieceVertex.2.1
        simp [gluedDecode, gluedEncode, notBoundary, inSupport]
      · have notSupport := outsideVertex.2
        have notBoundary :
            outsideVertex.1 ∉ Presentation.boundary object support := by
          intro boundaryMember
          exact notSupport
            ((Presentation.mem_boundary_iff object support outsideVertex.1).1
              boundaryMember).1
        simp [gluedDecode, gluedEncode, notBoundary, notSupport]
  right_inv := by
    classical
    intro vertex
    by_cases onBoundary : vertex ∈ Presentation.boundary object support
    · simp [gluedDecode, gluedEncode, onBoundary]
    · by_cases inSupport : vertex ∈ support
      · simp [gluedDecode, gluedEncode, onBoundary, inSupport]
      · simp [gluedDecode, gluedEncode, onBoundary, inSupport]

/-- Exact ownership decomposition over the literal cut boundary. -/
noncomputable def decomposition : OwnedDecomposition object where
  interface := boundary object support
  piece := piece object support
  outside := outside object support
  vertexEquiv := vertexEquiv object support
  ownsAdjacency := by
    intro left right
    constructor
    · intro adjacent
      rcases left with left | left
      · rcases right with right | right
        · exact Or.inl ⟨.inl left, .inl right, adjacent, rfl, rfl⟩
        · rcases right with right | right
          · exact Or.inl ⟨.inl left, .inr right, adjacent, rfl, rfl⟩
          · exact Or.inr ⟨.inl left, .inr right, adjacent, rfl, rfl⟩
      · rcases left with left | left
        · rcases right with right | right
          · exact Or.inl ⟨.inr left, .inl right, adjacent, rfl, rfl⟩
          · rcases right with right | right
            · exact Or.inl ⟨.inr left, .inr right, adjacent, rfl, rfl⟩
            · exact False.elim
                (not_adj_pieceInternal_outside object support left right adjacent)
        · rcases right with right | right
          · exact Or.inr ⟨.inr left, .inl right, adjacent, rfl, rfl⟩
          · rcases right with right | right
            · exact False.elim
                (not_adj_pieceInternal_outside object support right left
                  ((object.graph.adj_comm _ _).mp adjacent))
            · exact Or.inr ⟨.inr left, .inr right, adjacent, rfl, rfl⟩
    · rintro (owned | owned)
      · rcases owned with ⟨left', right', adjacent, leftEq, rightEq⟩
        subst left
        subst right
        rcases left' with left' | left' <;>
          rcases right' with right' | right' <;>
          exact adjacent
      · rcases owned with ⟨left', right', adjacent, leftEq, rightEq⟩
        subst left
        subst right
        rcases left' with left' | left' <;>
          rcases right' with right' | right' <;>
          exact adjacent

private noncomputable def pieceInducedIso :
    (piece object support).graph ≃g (object.induce support).graph where
  toEquiv :=
    { toFun
        | .inl boundaryVertex =>
            ⟨boundaryVertex.1,
              ((Presentation.mem_boundary_iff object support boundaryVertex.1).1
                boundaryVertex.2).1⟩
        | .inr internalVertex =>
            ⟨internalVertex.1, internalVertex.2.1⟩
      invFun := by
        intro supported
        classical
        by_cases onBoundary :
            supported.1 ∈ Presentation.boundary object support
        · exact .inl ⟨supported.1, onBoundary⟩
        · exact .inr ⟨supported.1, supported.2, onBoundary⟩
      left_inv := by
        classical
        intro vertex
        rcases vertex with vertex | vertex
        · simp [vertex.2]
        · simp [vertex.2.2]
      right_inv := by
        classical
        intro vertex
        by_cases onBoundary :
            vertex.1 ∈ Presentation.boundary object support
        · simp [onBoundary]
        · simp [onBoundary] }
  map_rel_iff' := by
    intro left right
    rcases left with left | left <;>
      rcases right with right | right <;>
      rfl

private theorem induced_connected
    (connected : ConnectedOn object support) :
    (object.induce support).graph.Connected := by
  rcases connected.1 with ⟨root, rootMember⟩
  letI : Nonempty (object.induce support).Vertex :=
    ⟨⟨root, rootMember⟩⟩
  refine { preconnected := ?_ }
  intro left right
  obtain ⟨path, _isPath, contained⟩ :=
    connected.2 left.2 right.2
  exact ⟨path.induce (support : Set object.Vertex) contained⟩

/-- Raw proper connected support to exact proper boundaried atom. -/
noncomputable def properAtom
    (connected : ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) :
    ProperBoundariedAtom object where
  decomposition := decomposition object support
  connected :=
    (pieceInducedIso object support).connected_iff.mpr
      (induced_connected object support connected)
  proper := by
    intro notProper
    rcases proper with ⟨vertex, outsideSupport⟩
    let outsideVertex : OutsideInternal object support :=
      ⟨vertex, outsideSupport⟩
    obtain ⟨preimage, preimageEq⟩ := notProper.1 outsideVertex.1
    rcases preimage with boundaryVertex | internalVertex
    · change boundaryVertex.1 = outsideVertex.1 at preimageEq
      have valEq : boundaryVertex.1 = vertex := preimageEq
      exact outsideSupport (by
        rw [← valEq]
        exact ((Presentation.mem_boundary_iff object support boundaryVertex.1).1
          boundaryVertex.2).1)
    · change internalVertex.1 = outsideVertex.1 at preimageEq
      have valEq : internalVertex.1 = vertex := preimageEq
      exact outsideSupport (by
        rw [← valEq]
        exact internalVertex.2.1)

end Hypostructure.Graph.Strategy.Official.Features.CanonicalSupportDecomposition
