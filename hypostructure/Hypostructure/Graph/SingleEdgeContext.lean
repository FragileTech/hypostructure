import Hypostructure.Graph.ReadingSpectrum

/-!
# The single-edge context between two boundary vertices: positivity and path length

For a support `Z` and two boundary vertices `a ≠ b` of `∂Z`, the single-edge
context `a — b` (`Graph/ReadingSpectrum.lean`, `EdgeContext.edgeContext`) has no
internal vertex and the one edge `ab`.  On a target-avoiding object a reading
glued to it is positive iff the reading has an `a → b` path avoiding `ab` of
accepted-minus-one length; every path between two labels of the context has
length one.  Vocabulary-free.
-/

namespace Hypostructure.Graph.SingleEdgeContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ReadingSpectrum.EdgeContext

universe u

/-- The single-edge context `a — b` is positive for a reading iff the reading
has an `a → b` path avoiding `ab` of accepted-minus-one length. -/
theorem edgeContext_positive_iff {G : FiniteObject.{u}} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L G) {Z R : Finset G.Vertex}
    {a b : (SupportAtom.boundary G Z).Vertex} (ne : a ≠ b) :
    HasCycleWithLength L
        (glue (SupportAtom.retainedPiece G Z R) (edgeContext Z a b)) ↔
      ∃ p : (SupportAtom.retainedPiece G Z R).graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ s(.inl a, .inl b) ∉ p.edges ∧ L (p.length + 1) :=
  ⟨path_of_edgeContext_cycle avoids,
    fun ⟨p, hp, hf, hl⟩ => edgeContext_cycle_of_path ne p hp hf hl⟩

/-- A path between two labels in a single-edge context has length exactly `1`. -/
theorem edgeContext_path_length {G : FiniteObject.{u}} {Z : Finset G.Vertex}
    {a b : (SupportAtom.boundary G Z).Vertex} {x y : (SupportAtom.boundary G Z).Vertex}
    (xy : x ≠ y)
    (σ : (edgeContext Z a b).graph.Walk (.inl x) (.inl y)) (hσ : σ.IsPath) :
    σ.length = 1 := by
  classical
  have pos : 1 ≤ σ.length := by
    rcases σ with _ | ⟨_, _⟩
    · exact absurd rfl xy
    · simp
  have sub : σ.edges.toFinset ⊆ {s(Sum.inl a, Sum.inl b)} := by
    intro e he
    have := σ.edges_subset_edgeSet (List.mem_toFinset.1 he)
    change e ∈ (SimpleGraph.fromEdgeSet _).edgeSet at this
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    exact Finset.mem_singleton.2 (Set.mem_singleton_iff.1 this.1)
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hσ.edges_nodup, SimpleGraph.Walk.length_edges,
    Finset.card_singleton] at card
  omega

end Hypostructure.Graph.SingleEdgeContext
