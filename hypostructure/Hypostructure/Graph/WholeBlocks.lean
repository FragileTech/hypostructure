import Hypostructure.Graph.CycleCounting.Object
import Hypostructure.Graph.SupportComponents

/-!
# Cut vertices of G have even degree at least four (`[144a]`, G audit S144a)

Vocabulary-free.  In the boundary-free whole-graph configuration of `[144a]`
every vertex outside a pair seed is a cut vertex of `G`.  With the
vertex-deletion shape of `G` (`CycleCounting.VertexDeletionShape`) a cut vertex
`h` has even degree, hence degree at least `4` on a graph of minimum degree
`3`.  So every degree-`3` vertex lies in both pair seeds, and if `G` has no
cut vertex then the pair seeds cover `V(G)`.
-/

namespace Hypostructure.Graph.WholeBlocks

open Hypostructure
open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

/-- **A cut vertex has even degree at least `4`.**  `Z` is every vertex of `G`;
`Z.erase v` is disconnected. -/
theorem cut_even_degree [DecidableEq object.Vertex]
    (shape : CycleCounting.VertexDeletionShape object)
    (base : ∀ v, 3 ≤ object.degree v) {Z : Finset object.Vertex} (hZ : ∀ v, v ∈ Z)
    {v : object.Vertex}
    (cut : ¬ SupportComponents.Connected.ConnectedOn object (Z.erase v)) :
    Even (object.degree v) ∧ 4 ≤ object.degree v := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rcases shape v with dc | ⟨ev, -, -⟩
  · exfalso
    apply cut
    have hdeg : 0 < object.graph.degree v := by
      have := base v
      unfold FiniteObject.degree at this
      omega
    obtain ⟨x, hx⟩ := (SimpleGraph.degree_pos_iff_exists_adj object.graph v).1 hdeg
    have full := dc x hx
    have inComp : ∀ u, u ≠ v → ∃ p : object.graph.Walk x u, v ∉ p.support := by
      intro u hu
      have h := (Finset.ext_iff.1 full u).2 (Finset.mem_univ u)
      simp only [Finset.mem_insert] at h
      rcases h with h | h
      · exact absurd h hu
      · simpa [CycleCounting.comp] using h
    refine ⟨⟨x, Finset.mem_erase.2 ⟨hx.ne.symm, hZ x⟩⟩, ?_⟩
    intro l r hl hr
    have hl' := Finset.mem_erase.1 hl
    have hr' := Finset.mem_erase.1 hr
    obtain ⟨pl, hpl⟩ := inComp l hl'.1
    obtain ⟨pr, hpr⟩ := inComp r hr'.1
    let w : object.graph.Walk l r := pl.reverse.append pr
    refine ⟨w.bypass, w.bypass_isPath, fun u hu => ?_⟩
    have hu' := w.support_bypass_subset_support hu
    refine Finset.mem_erase.2 ⟨?_, hZ u⟩
    rintro rfl
    simp only [w, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse,
      List.mem_append, List.mem_reverse] at hu'
    rcases hu' with h | h
    · exact hpl h
    · exact hpr (List.mem_of_mem_tail h)
  · refine ⟨ev, ?_⟩
    obtain ⟨k, hk⟩ := ev
    have := base v
    omega

end Hypostructure.Graph.WholeBlocks
