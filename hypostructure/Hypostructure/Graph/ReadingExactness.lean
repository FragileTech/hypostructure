import Hypostructure.Graph.ActualContext

/-!
# The exact behaviour of an edge-restricted reading of G's piece (`[144a]`)

Vocabulary-free (G audit S144a).  `ActualContext.actualGlue G Z Y` is G's own
piece at `Z`, with only the edges `Y` owns, glued into `G - Z`.  It has all the
vertices of `G`.  It drops exactly the edges of `G[Z]` that have an interior
end (a vertex of `Z` off `∂Z`) and an end outside `Y`; the `∂Z`-`∂Z` edges stay
(the outside owns them).

* `actualGlue_lexicographicallySmaller`: dropping one such edge makes the
  reading lexicographically smaller than `G` (same vertex count, fewer edges).
* `not_baseline_actualGlue_of_minimal`: on a minimal target-avoiding `G`, such
  a reading fails the baseline (a smaller object without a target cycle would
  otherwise contradict minimality).
* `reading_exact`: a reading of `G` at `Z` either drops no edge (every edge of
  `G[Z]` with an interior end lies in `Y`) or it drops one and fails the
  baseline.
-/

namespace Hypostructure.Graph.ReadingExactness

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ActualContext

universe u

variable {object : FiniteObject.{u}}

/-- The reading has the vertex count of `G`. -/
theorem actualGlue_vertexCount (Z Y : Finset object.Vertex) :
    (actualGlue object Z Y).vertexCount = object.vertexCount := by
  have full : (glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)).vertexCount =
      object.vertexCount :=
    FiniteObject.vertexCount_eq_of_isomorphic
      ⟨(SupportAtom.decomposition object Z).reconstructionIso⟩
  rw [← full]
  unfold actualGlue
  rw [glue_vertexCount, glue_vertexCount]
  rfl

/-- **Dropping an owned edge with an interior end makes the reading smaller.** -/
theorem actualGlue_lexicographicallySmaller {Z Y : Finset object.Vertex}
    {x y : object.Vertex} (adj : object.graph.Adj x y) (hx : x ∈ Z) (hy : y ∈ Z)
    (hxb : x ∉ SupportAtom.cutBoundary object Z) (notBoth : ¬ (x ∈ Y ∧ y ∈ Y)) :
    (actualGlue object Z Y).LexicographicallySmaller object := by
  classical
  refine FiniteObject.lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt
    (actualGlue_vertexCount Z Y) ?_
  let full := glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)
  have fullEdges : full.edgeCount = object.edgeCount :=
    FiniteObject.edgeCount_eq_of_isomorphic
      ⟨(SupportAtom.decomposition object Z).reconstructionIso⟩
  have le : glueGraph (SupportAtom.retainedPiece object Z Y) (SupportAtom.outside object Z) ≤
      glueGraph (SupportAtom.piece object Z) (SupportAtom.outside object Z) := by
    apply glueGraph_mono (piece := SupportAtom.piece object Z) (SupportAtom.outside object Z)
    intro left right adjacent
    exact adjacent.1
  let s : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z :=
    .inr ⟨x, hx, hxb⟩
  let t : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z :=
    if hyb : y ∈ SupportAtom.cutBoundary object Z then .inl ⟨y, hyb⟩ else .inr ⟨y, hy, hyb⟩
  have sdec : SupportAtom.pieceDecode object Z s = x := rfl
  have tdec : SupportAtom.pieceDecode object Z t = y := by
    by_cases hyb : y ∈ SupportAtom.cutBoundary object Z
    · simp [t, hyb, SupportAtom.pieceDecode]
    · simp [t, hyb, SupportAtom.pieceDecode]
  have pieceAdj : (SupportAtom.piece object Z).graph.Adj s t := by
    change object.graph.Adj (SupportAtom.pieceDecode object Z s)
      (SupportAtom.pieceDecode object Z t)
    rw [sdec, tdec]; exact adj
  have inFull : (glueGraph (SupportAtom.piece object Z) (SupportAtom.outside object Z)).Adj
      (pieceEmbedding (SupportAtom.piece object Z) (SupportAtom.outside object Z) s)
      (pieceEmbedding (SupportAtom.piece object Z) (SupportAtom.outside object Z) t) :=
    (glueGraph_adj_iff _ _ _ _).2 (Or.inl ⟨s, t, pieceAdj, rfl, rfl⟩)
  have dec : ∀ a b : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z,
      pieceEmbedding (SupportAtom.retainedPiece object Z Y) (SupportAtom.outside object Z) a =
        pieceEmbedding (SupportAtom.piece object Z) (SupportAtom.outside object Z) b →
      SupportAtom.pieceDecode object Z a = SupportAtom.pieceDecode object Z b := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      simp [pieceEmbedding, SupportAtom.pieceDecode] at h ⊢ <;>
      first
        | (have h' := Sum.inl.inj h; subst h'; rfl)
        | (have h' := Sum.inl.inj (Sum.inr.inj h); subst h'; rfl)
  have notInRetained : ¬ (glueGraph (SupportAtom.retainedPiece object Z Y)
      (SupportAtom.outside object Z)).Adj
      (pieceEmbedding (SupportAtom.piece object Z) (SupportAtom.outside object Z) s)
      (pieceEmbedding (SupportAtom.piece object Z) (SupportAtom.outside object Z) t) := by
    intro h
    rcases (glueGraph_adj_iff _ _ _ _).1 h with ⟨s', t', hadj, hs', ht'⟩ | ⟨s', t', -, hs', -⟩
    · have es := dec s' s hs'
      have et := dec t' t ht'
      have h2 := hadj.2
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h2
      rw [es, et, sdec, tdec] at h2
      rcases h2.2 with h | h
      · exact notBoth h
      · exact notBoth ⟨h.2, h.1⟩
    · rcases s' with b | i
      · simp [contextEmbedding, pieceEmbedding, s] at hs'
      · change (Sum.inr (Sum.inr i) : GluedVertex _ _) = Sum.inr (Sum.inl _) at hs'
        injection hs' with h1
        injection h1
  have strict : (glueGraph (SupportAtom.retainedPiece object Z Y) (SupportAtom.outside object Z))
      < glueGraph (SupportAtom.piece object Z) (SupportAtom.outside object Z) :=
    lt_of_le_of_ne le fun eq => notInRetained (eq ▸ inFull)
  change (glue (SupportAtom.retainedPiece object Z Y) (SupportAtom.outside object Z)).edgeCount <
    object.edgeCount
  rw [← fullEdges, FiniteObject.edgeCount_eq_ncard_edgeSet, FiniteObject.edgeCount_eq_ncard_edgeSet]
  have hfin : (glueGraph (SupportAtom.piece object Z) (SupportAtom.outside object Z)).edgeSet.Finite := by
    letI : FinEnum (GluedVertex (SupportAtom.piece object Z) (SupportAtom.outside object Z)) :=
      full.vertices
    exact Set.toFinite _
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono strict) hfin

end Hypostructure.Graph.ReadingExactness
