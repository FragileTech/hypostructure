import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.BoundaryDemand

/-!
# The route-8 supply is the boundary incidence

`prop:typeA-route8-carrier-reduction` counts private essential carriers against
the boundary-incidence supply `def⁺(R) ≤ e(R,W)`.  The carrier lemmas of
`Graph/Route8CarrierCore` are stated over the cut `∂R` as a set of edges
(`Route8.cutEdges`), while nodes `[28]`--`[29]` bound the *count*
`e(R,W)` (`boundaryIncidence`).  This module identifies the two: every cut edge
has exactly one endpoint inside the support, so the cut has exactly as many
edges as there are incidences leaving the support.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq vertexFintype edgeFintype

/-- The ordered crossing pairs `(inside, outside)` of a support. -/
noncomputable def crossingPairs (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset (object.Vertex × object.Vertex) := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact (support ×ˢ (Finset.univ \ support)).filter fun pair =>
    object.graph.Adj pair.1 pair.2

theorem mem_crossingPairs {support : Finset object.Vertex}
    {pair : object.Vertex × object.Vertex} :
    pair ∈ crossingPairs object support ↔
      pair.1 ∈ support ∧ pair.2 ∉ support ∧ object.graph.Adj pair.1 pair.2 := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp [crossingPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The cut is the image of the crossing pairs under `Sym2.mk`. -/
theorem cutEdges_eq_image (support : Finset object.Vertex) :
    cutEdges object support =
      (crossingPairs object support).image fun pair => s(pair.1, pair.2) := by
  classical
  ext edge
  rw [mem_cutEdges, Finset.mem_image]
  constructor
  · rintro ⟨edgeMem, inside, insideMem, outside, outsideMem, insideSupport, outsideSupport⟩
    have edgeAdj : edge ∈ object.graph.edgeSet := by simpa using edgeMem
    have distinct : inside ≠ outside := by
      intro same; exact outsideSupport (same ▸ insideSupport)
    refine ⟨(inside, outside), ?_, ?_⟩
    · rw [mem_crossingPairs]
      refine ⟨insideSupport, outsideSupport, ?_⟩
      induction edge using Sym2.inductionOn with
      | hf left right =>
        simp only [Sym2.mem_iff] at insideMem outsideMem
        rcases insideMem with rfl | rfl <;> rcases outsideMem with rfl | rfl
        · exact absurd rfl distinct
        · exact edgeAdj
        · exact edgeAdj.symm
        · exact absurd rfl distinct
    · induction edge using Sym2.inductionOn with
      | hf left right =>
        simp only [Sym2.mem_iff] at insideMem outsideMem
        rcases insideMem with rfl | rfl <;> rcases outsideMem with rfl | rfl
        · exact absurd rfl distinct
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl distinct
  · rintro ⟨pair, pairMem, rfl⟩
    rw [mem_crossingPairs] at pairMem
    obtain ⟨insideSupport, outsideSupport, adjacent⟩ := pairMem
    refine ⟨?_, pair.1, ?_, pair.2, ?_, insideSupport, outsideSupport⟩
    · simpa using adjacent
    · exact Sym2.mem_mk_left _ _
    · exact Sym2.mem_mk_right _ _

/-- `Sym2.mk` is injective on the crossing pairs: the inside endpoint is
determined by the support. -/
theorem crossingPairs_injOn (support : Finset object.Vertex) :
    Set.InjOn (fun pair : object.Vertex × object.Vertex => s(pair.1, pair.2))
      ↑(crossingPairs object support) := by
  intro left leftMem right rightMem equal
  rw [Finset.mem_coe, mem_crossingPairs] at leftMem rightMem
  have cases := Sym2.eq_iff.mp equal
  rcases cases with same | swapped
  · exact Prod.ext same.1 same.2
  · exact absurd (swapped.1 ▸ leftMem.1) rightMem.2.1

/-- **The cut has exactly `e(R,W)` edges.** -/
theorem card_cutEdges_eq_boundaryIncidence (support : Finset object.Vertex) :
    (cutEdges object support).card = object.boundaryIncidence support := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  rw [cutEdges_eq_image, Finset.card_image_of_injOn (crossingPairs_injOn support)]
  have pairsCard : (crossingPairs object support).card =
      ∑ vertex ∈ support,
        object.internalDegree (Finset.univ \ support) vertex := by
    rw [crossingPairs, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    rw [FiniteObject.internalDegree, Finset.inter_comm, ← Finset.filter_mem_eq_inter,
      Finset.card_filter]
    refine Finset.sum_congr rfl fun other _ => ?_
    simp [SimpleGraph.mem_neighborFinset]
  rw [pairsCard, FiniteObject.boundaryIncidence]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  have split := object.internalDegree_add_internalDegree_compl support vertex
  have complEq : (Finset.univ \ support : Finset object.Vertex) =
      (by letI : FinEnum object.Vertex := object.vertices
          classical
          exact Finset.univ \ support) := by
    congr
  rw [complEq, ← split, Nat.add_sub_cancel_left]
  congr

end Hypostructure.Graph.Route8
