import Hypostructure.Graph.WindowPacking

/-!
# The stub structure of an ambient-cubic induced window

`lem:cold-window-stub-excess` counts the external stubs of an ambient-cubic
induced `P_order` window: `δ·order − 2(order−1)` in all.  This module records
*where* those stubs sit, which is what the symmetric-pair analysis of the dense
residual (nodes `[167]`--`[168]`) charges: an interior window vertex has exactly
two window neighbours and therefore exactly `δ − 2` external stubs, and only
the two path endpoints have `δ − 1`.  At the manuscript's baseline `δ = 3` an
interior vertex carries a single stub, so two internally disjoint strands
leaving the same interior attachment vertex do not exist: a genuine symmetric
strand pair can attach only at the two endpoints, and a window carries at most
one such pair, on its four endpoint stubs.

Everything is stated for a general order and baseline; no numeral of the
strategy appears.
-/

namespace Hypostructure.Graph.FiniteObject

universe u

variable {object : FiniteObject.{u}}

/-- The external neighbours of a window vertex: its neighbours outside the
window (the stubs at that vertex, read as their outside endpoints). -/
noncomputable def externalNeighbours (object : FiniteObject.{u})
    (window : Finset object.Vertex) (vertex : object.Vertex) :
    Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (object.graph.neighborFinset vertex).filter (· ∉ window)

/-- The window neighbours of a window vertex. -/
noncomputable def windowNeighbours (object : FiniteObject.{u})
    (window : Finset object.Vertex) (vertex : object.Vertex) :
    Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (object.graph.neighborFinset vertex).filter (· ∈ window)

theorem card_windowNeighbours_add_card_externalNeighbours (window : Finset object.Vertex)
    (vertex : object.Vertex) :
    (object.windowNeighbours window vertex).card +
        (object.externalNeighbours window vertex).card = object.degree vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold windowNeighbours externalNeighbours
  rw [Finset.card_filter_add_card_filter_not]
  simp [FiniteObject.degree, SimpleGraph.card_neighborFinset_eq_degree]

/-- **The endpoint/interior stub structure of an ambient-cubic induced window.**

There is a set `ends` of exactly two window vertices (the two path endpoints)
such that every window vertex outside `ends` has exactly `threshold − 2`
external stubs, and every vertex of `ends` has exactly `threshold − 1`. -/
theorem exists_ends_externalNeighbours {order threshold : Nat}
    (window : Finset object.Vertex) (three : 3 ≤ order)
    (induces : object.InducesWindow order window)
    (cubic : ∀ vertex ∈ window, object.degree vertex = threshold) :
    ∃ ends : Finset object.Vertex, ends ⊆ window ∧ ends.card = 2 ∧
      (∀ vertex ∈ window, vertex ∉ ends →
        (object.externalNeighbours window vertex).card = threshold - 2) ∧
      (∀ vertex ∈ ends,
        (object.externalNeighbours window vertex).card = threshold - 1) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  obtain ⟨⟨embedding⟩, cardinality⟩ := induces
  let toVertex : Fin order → object.Vertex := fun index => (embedding index).1
  have toVertexInj : Function.Injective toVertex := by
    intro a b same
    exact embedding.injective (Subtype.ext same)
  have toVertexMem : ∀ index, toVertex index ∈ window := fun index => (embedding index).2
  have toVertexRange : ∀ vertex ∈ window, ∃ index, toVertex index = vertex := by
    intro vertex member
    have imageCard : (Finset.univ.image toVertex).card = order := by
      rw [Finset.card_image_of_injective _ toVertexInj]; simp
    have imageSubset : Finset.univ.image toVertex ⊆ window := by
      intro v hv
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.1 hv
      exact toVertexMem index
    have imageEq : Finset.univ.image toVertex = window :=
      Finset.eq_of_subset_of_card_le imageSubset (by rw [imageCard, cardinality])
    rw [← imageEq] at member
    obtain ⟨index, _, eq⟩ := Finset.mem_image.1 member
    exact ⟨index, eq⟩
  -- adjacency inside the window is path adjacency
  have adjIff : ∀ i j : Fin order,
      object.graph.Adj (toVertex i) (toVertex j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
    intro i j
    rw [← SimpleGraph.pathGraph_adj, ← embedding.map_adj_iff]
    rfl
  -- the window neighbours of `toVertex i` are the images of the path neighbours
  have windowNeighboursEq : ∀ i : Fin order,
      object.windowNeighbours window (toVertex i) =
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).image
          toVertex := by
    intro i
    ext w
    simp only [windowNeighbours, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨adjacent, wMem⟩
      obtain ⟨j, rfl⟩ := toVertexRange w wMem
      exact ⟨j, (adjIff i j).1 adjacent, rfl⟩
    · rintro ⟨j, pathAdj, rfl⟩
      exact ⟨(adjIff i j).2 pathAdj, toVertexMem j⟩
  have windowNeighboursCard : ∀ i : Fin order,
      (object.windowNeighbours window (toVertex i)).card =
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card := by
    intro i
    rw [windowNeighboursEq i, Finset.card_image_of_injective _ toVertexInj]
  -- the ends
  let first : Fin order := ⟨0, by omega⟩
  let last : Fin order := ⟨order - 1, by omega⟩
  refine ⟨{toVertex first, toVertex last}, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact toVertexMem _
  · rw [Finset.card_pair]
    intro same
    have indexSame : first = last := toVertexInj same
    rw [Fin.ext_iff] at indexSame
    simp only [first, last] at indexSame
    omega
  · intro vertex vertexMem notEnd
    obtain ⟨i, rfl⟩ := toVertexRange vertex vertexMem
    have iNotFirst : i ≠ first := fun h => notEnd (by simp [h])
    have iNotLast : i ≠ last := fun h => notEnd (by simp [h])
    have iPos : 0 < i.1 := by
      rcases Nat.eq_zero_or_pos i.1 with h | h
      · exact absurd (Fin.ext (by simp [first, h])) iNotFirst
      · exact h
    have iLt : i.1 < order - 1 := by
      have := i.2
      rcases Nat.lt_or_ge i.1 (order - 1) with h | h
      · exact h
      · exact absurd (Fin.ext (by simp [last]; omega)) iNotLast
    -- two path neighbours
    have twoNeighbours :
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) =
          {⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, by omega⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    have degreeEq := card_windowNeighbours_add_card_externalNeighbours
      (object := object) window (toVertex i)
    rw [windowNeighboursCard i, twoNeighbours, cubic _ vertexMem] at degreeEq
    have twoCard : ({⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, by omega⟩} :
        Finset (Fin order)).card = 2 := by
      rw [Finset.card_pair]
      intro h
      rw [Fin.ext_iff] at h
      simp only at h
      omega
    rw [twoCard] at degreeEq
    omega
  · intro vertex vertexMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
    have oneNeighbour : ∀ i : Fin order, i = first ∨ i = last →
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card = 1 := by
      intro i hi
      rcases hi with rfl | rfl
      · have : (Finset.univ.filter fun j : Fin order =>
            first.1 + 1 = j.1 ∨ j.1 + 1 = first.1) = {⟨1, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff, first]
          omega
        rw [this, Finset.card_singleton]
      · have : (Finset.univ.filter fun j : Fin order =>
            last.1 + 1 = j.1 ∨ j.1 + 1 = last.1) = {⟨order - 2, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff, last]
          have := j.2
          omega
        rw [this, Finset.card_singleton]
    rcases vertexMem with rfl | rfl
    · have degreeEq := card_windowNeighbours_add_card_externalNeighbours
        (object := object) window (toVertex first)
      rw [windowNeighboursCard first, oneNeighbour first (Or.inl rfl),
        cubic _ (toVertexMem first)] at degreeEq
      omega
    · have degreeEq := card_windowNeighbours_add_card_externalNeighbours
        (object := object) window (toVertex last)
      rw [windowNeighboursCard last, oneNeighbour last (Or.inr rfl),
        cubic _ (toVertexMem last)] at degreeEq
      omega

/-- **At most one genuine symmetric strand pair per window.**  Two internally
disjoint strands leaving one attachment vertex need two distinct stubs there;
at the baseline `threshold = 3` an interior vertex has one, so both attachment
vertices of a genuine pair are endpoints.  Consequently at least
`(order − 2)·(threshold − 2)` external stubs sit at single-stub interior
vertices, i.e. the asymmetric stub count. -/
theorem interior_stubs_le_asymmetric {order threshold : Nat}
    (window : Finset object.Vertex) (three : 3 ≤ order)
    (induces : object.InducesWindow order window)
    (cubic : ∀ vertex ∈ window, object.degree vertex = threshold) :
    (order - 2) * (threshold - 2) ≤
      ∑ vertex ∈ window.filter (fun vertex =>
        (object.externalNeighbours window vertex).card = threshold - 2),
        (object.externalNeighbours window vertex).card := by
  classical
  obtain ⟨ends, endsSubset, endsCard, interior, _⟩ :=
    exists_ends_externalNeighbours window three induces cubic
  have subset : window \ ends ⊆ window.filter (fun vertex =>
      (object.externalNeighbours window vertex).card = threshold - 2) := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    exact Finset.mem_filter.2 ⟨hv.1, interior v hv.1 hv.2⟩
  have cardSdiff : order - 2 ≤ (window \ ends).card := by
    rw [Finset.card_sdiff_of_subset endsSubset]
    have := induces.2
    omega
  calc (order - 2) * (threshold - 2)
      ≤ (window \ ends).card * (threshold - 2) := Nat.mul_le_mul_right _ cardSdiff
    _ = ∑ vertex ∈ window \ ends, (object.externalNeighbours window vertex).card := by
        rw [Finset.sum_congr rfl (fun v hv => interior v (Finset.mem_sdiff.1 hv).1
          (Finset.mem_sdiff.1 hv).2), Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ vertex ∈ window.filter (fun vertex =>
          (object.externalNeighbours window vertex).card = threshold - 2),
          (object.externalNeighbours window vertex).card :=
        Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)

end Hypostructure.Graph.FiniteObject
