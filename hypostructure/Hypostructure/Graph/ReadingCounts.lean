import Hypostructure.Graph.ReadingProfiles

/-!
# Active labels and private edges of a reading

Let `Z` be a vertex support of a finite object, `∂Z` its cut boundary and
`ret_R` the piece of `Z` that keeps the edges with both ends in `R`, with the
reading counts `c_R(b)` of `Graph/ReadingProfiles.lean`.

Results (all vocabulary-free):
* every accepted cycle of a reading glued to a cycle-free context crosses `∂Z`
  at two distinct active labels (positive reading count);
* if `glue ret_P O` has an accepted cycle and `glue ret_N O` has none, the cycle
  uses a private edge of `P` (both ends in `P`, not both in `N`).
-/

namespace Hypostructure.Graph.ReadingCounts

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ReadingProfiles

universe u

section Active

variable {G : FiniteObject.{u}}

/-- The active part of a support: vertices with a neighbour in `Z ∩ X`. -/
noncomputable def activePart (Z X : Finset G.Vertex) : Finset G.Vertex := by
  classical
  exact X.filter fun v => ∃ x, x ∈ Z ∧ x ∈ X ∧ G.graph.Adj v x

theorem retained_le_active (Z X : Finset G.Vertex) :
    (SupportAtom.retainedPiece G Z X).graph ≤
      (SupportAtom.retainedPiece G Z (activePart Z X)).graph := by
  classical
  intro p q h
  have mem := GluedReadings.retained_adj_mem h
  have gadj : G.graph.Adj (SupportAtom.pieceDecode G Z p) (SupportAtom.pieceDecode G Z q) := h.1
  refine ⟨h.1, ?_⟩
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
  refine ⟨h.2.1, Or.inl ⟨?_, ?_⟩⟩
  · simp only [activePart, Finset.mem_filter]
    exact ⟨mem.1, _, pieceDecode_mem Z q, mem.2, gadj⟩
  · simp only [activePart, Finset.mem_filter]
    exact ⟨mem.2, _, pieceDecode_mem Z p, mem.1, gadj.symm⟩

theorem readingCount_pos_of_active {Z X : Finset G.Vertex}
    {l : (SupportAtom.boundary G Z).Vertex} (h : l.1 ∈ activePart Z X) :
    0 < readingCount Z X l := by
  classical
  simp only [activePart, Finset.mem_filter] at h
  obtain ⟨lX, x, xZ, xX, adj⟩ := h
  unfold readingCount
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨x, xZ, adj, lX, xX⟩

/-- **Two active labels** (vocabulary-free).  On an avoiding object, every
accepted cycle of a reading glued to a cycle-free context crosses `∂Z` at two
distinct labels, each with a positive reading count. -/
theorem two_active_labels {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L G)
    {Z X : Finset G.Vertex} {O : OutsideContext (SupportAtom.boundary G Z)}
    (ctxFree : ¬ HasCycleWithLength L O.pack)
    (pos : HasCycleWithLength L (glue (SupportAtom.retainedPiece G Z X) O)) :
    ∃ l₁ l₂ : (SupportAtom.boundary G Z).Vertex, l₁ ≠ l₂ ∧
      0 < readingCount Z X l₁ ∧ 0 < readingCount Z X l₂ := by
  have pos' := GluedReadings.glue_mono_of_le (retained_le_active Z X) O pos
  obtain ⟨c⟩ := pos'
  have hp := DefectGeometry.pieceExclusive c ctxFree
  have ho : DefectGeometry.ContextExclusive c := by
    rcases DefectGeometry.local_or_mixed c with loc | mix
    · exact absurd (DefectGeometry.local_target c loc)
        (GluedReadings.retainedPiece_avoids avoids Z _)
    · exact mix
  obtain ⟨l₁, l₂, ne, h1, h2⟩ := GluedReadings.two_retained_labels c hp ho
  exact ⟨l₁, l₂, ne, readingCount_pos_of_active h1, readingCount_pos_of_active h2⟩

/-- **Every accepted cycle of the positive reading uses a private edge**
(vocabulary-free): if `glue ret_P O` has an accepted cycle `c` and
`glue ret_N O` has none, then `c` traverses the glued copy of a `G`-edge
`xy` with `x, y ∈ Z ∩ P` and not both in `N`. -/
theorem cycle_uses_private {L : Nat → Prop} {Z P N : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)}
    (c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) L)
    (neg : ¬ HasCycleWithLength L (glue (SupportAtom.retainedPiece G Z N) O)) :
    ∃ pl pr : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z,
      s(pieceEmbedding (SupportAtom.retainedPiece G Z P) O pl,
        pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr) ∈ c.walk.edges ∧
      G.graph.Adj (SupportAtom.pieceDecode G Z pl) (SupportAtom.pieceDecode G Z pr) ∧
      SupportAtom.pieceDecode G Z pl ∈ P ∧ SupportAtom.pieceDecode G Z pr ∈ P ∧
      ¬ (SupportAtom.pieceDecode G Z pl ∈ N ∧ SupportAtom.pieceDecode G Z pr ∈ N) := by
  classical
  by_contra none
  push Not at none
  apply neg
  have edgesIn : ∀ e ∈ c.walk.edges,
      e ∈ (glue (SupportAtom.retainedPiece G Z N) O).graph.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have adj := c.walk.adj_of_mem_edges he
      rcases (glueGraph_adj_iff _ O a b).1 adj with owns | owns
      · obtain ⟨pl, pr, padj, rfl, rfl⟩ := owns
        have mem := GluedReadings.retained_adj_mem padj
        have both := none pl pr he padj.1 mem.1 mem.2
        refine (glueGraph_adj_iff (SupportAtom.retainedPiece G Z N) O _ _).2
          (Or.inl ⟨pl, pr, ⟨padj.1, ?_⟩, ?_, ?_⟩)
        · simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
          exact ⟨padj.2.1, Or.inl both⟩
        · cases pl <;> rfl
        · cases pr <;> rfl
      · obtain ⟨cl, cr, cadj, h1, h2⟩ := owns
        exact (glueGraph_adj_iff (SupportAtom.retainedPiece G Z N) O a b).2
          (Or.inr ⟨cl, cr, cadj, h1, h2⟩)
  exact ⟨⟨c.vertex, c.walk.transfer _ edgesIn, c.isCycle.transfer edgesIn,
    by convert c.length_ok using 1; apply SimpleGraph.Walk.length_transfer⟩⟩

end Active

end Hypostructure.Graph.ReadingCounts
