import Hypostructure.Graph.PathGraphCount
import Hypostructure.Graph.BoundaryDemand

/-!
# The internal degree mass of a packed window

A packed window is an induced copy of the path on `order` vertices, so
`order − 1` of its incidences are internal and the degree mass they carry --
`2(order − 1)` -- never leaves the window.  That is the `2·12 = 24` the
manuscript subtracts from the cubic degree sum `13·3 = 39` to reach the
`15` cubic exits of `lem:surplus-aware-window-stub`.

The chain is: the embedding of the path into the window's induced subgraph is
injective and the two vertex sets have the same size, so it is surjective;
degree transfers along a surjective embedding; and `sum_degree_pathGraph`
evaluates the result.

No numeral is written.  `order` is the registered window order throughout.
-/

namespace Hypostructure.Graph

open Hypostructure
open SimpleGraph
open scoped BigOperators

universe u

/-- Degree transfers along a surjective graph embedding: the neighbours of an
image are exactly the images of the neighbours. -/
theorem degree_eq_of_embedding_surjective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (embedding : G ↪g H) (surjective : Function.Surjective embedding)
    (vertex : α) :
    H.degree (embedding vertex) = G.degree vertex := by
  classical
  have image :
      H.neighborFinset (embedding vertex) =
        (G.neighborFinset vertex).image embedding := by
    ext other
    obtain ⟨source, rfl⟩ := surjective other
    simp only [mem_neighborFinset, Finset.mem_image]
    constructor
    · intro adjacent
      exact ⟨source, embedding.map_adj_iff.mp adjacent, rfl⟩
    · rintro ⟨candidate, member, equal⟩
      have same : candidate = source := embedding.injective equal
      subst same
      exact embedding.map_adj_iff.mpr member
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, image,
    Finset.card_image_of_injective _ embedding.injective]

namespace FiniteObject

/-- The internal degree of a vertex is its degree in the induced restriction. -/
theorem internalDegree_eq_degree_induce (object : FiniteObject.{u})
    (support : Finset object.Vertex) {vertex : object.Vertex}
    (member : vertex ∈ support) :
    object.internalDegree support vertex =
      (object.induce support).degree ⟨vertex, member⟩ := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : FinEnum (object.induce support).Vertex := (object.induce support).vertices
  letI : DecidableRel (object.induce support).graph.Adj :=
    (object.induce support).decideAdj
  classical
  rw [internalDegree, FiniteObject.degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (fun other _ => (⟨other, ?_⟩ : (object.induce support).Vertex)) ?_ ?_ ?_
  · rename_i inside
    exact (Finset.mem_inter.mp inside).2
  · intro other inside
    rw [mem_neighborFinset]
    have adjacent := (Finset.mem_inter.mp inside).1
    rwa [mem_neighborFinset] at adjacent
  · intro left leftMem right rightMem same
    exact congrArg Subtype.val same
  · intro other member'
    rw [mem_neighborFinset] at member'
    refine ⟨other.1, Finset.mem_inter.mpr ⟨?_, other.2⟩, rfl⟩
    rw [mem_neighborFinset]
    exact member'

/-- **The internal degree mass of a packed window is `2(order − 1)`.**

The window has exactly `order` vertices and its induced subgraph is a path on
that many, so the path embedding is a bijection and the degree sums agree. -/
theorem sum_internalDegree_window (object : FiniteObject.{u}) {order : Nat}
    {support : Finset object.Vertex}
    (window : object.InducesWindow order support) :
    ∑ vertex ∈ support, object.internalDegree support vertex =
      2 * (order - 1) := by
  classical
  obtain ⟨⟨embedding⟩, cardinality⟩ := window
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : FinEnum (object.induce support).Vertex := (object.induce support).vertices
  letI : DecidableRel (object.induce support).graph.Adj :=
    (object.induce support).decideAdj
  -- The embedding is a bijection: equal finite cardinalities.
  have cardSupport :
      Fintype.card (object.induce support).Vertex = support.card := by
    rw [← Fintype.card_coe support]
    exact Fintype.card_congr (Equiv.refl _)
  have cardEq : Fintype.card (Fin order) =
      Fintype.card (object.induce support).Vertex := by
    rw [Fintype.card_fin, cardSupport, cardinality]
  have bijective : Function.Bijective embedding :=
    (Fintype.bijective_iff_injective_and_card embedding).mpr
      ⟨embedding.injective, cardEq⟩
  -- Degree sums agree under it, and the path's sum is known.
  have transfer :
      ∑ index : Fin order, (pathGraph order).degree index =
        ∑ vertex : (object.induce support).Vertex,
          (object.induce support).degree vertex :=
    Fintype.sum_bijective embedding bijective _ _
      (fun index =>
        (degree_eq_of_embedding_surjective embedding bijective.2 index).symm)
  -- Rewrite the support sum as a sum over the induced vertex type.
  have attached :
      ∑ vertex ∈ support, object.internalDegree support vertex =
        ∑ vertex : (object.induce support).Vertex,
          (object.induce support).degree vertex := by
    have toAttach :
        (∑ vertex : (object.induce support).Vertex,
          (object.induce support).degree vertex) =
          ∑ vertex ∈ support.attach, (object.induce support).degree vertex := by
      exact Finset.sum_congr (Finset.ext fun candidate =>
        iff_of_true (Finset.mem_univ candidate)
          (Finset.mem_attach support candidate)) (fun _ _ => rfl)
    rw [toAttach, ← Finset.sum_attach support
      (fun vertex => object.internalDegree support vertex)]
    exact Finset.sum_congr rfl fun vertex _ =>
      object.internalDegree_eq_degree_induce support vertex.2
  rw [attached, ← transfer, sum_degree_pathGraph]

/-- **The internal degree mass of the whole packing.**

The packed windows are pairwise disjoint, so the mass on `W` is at least the
sum of the masses each window already carries inside itself. -/
theorem internal_mass_windowSupport (object : FiniteObject.{u}) {order : Nat}
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    2 * (order - 1) * packing.card ≤
      ∑ vertex ∈ windowSupport packing,
        object.internalDegree (windowSupport packing) vertex := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  have split :
      ∑ vertex ∈ windowSupport packing,
          object.internalDegree (windowSupport packing) vertex =
        ∑ member ∈ packing, ∑ vertex ∈ member,
          object.internalDegree (windowSupport packing) vertex := by
    have pairwise :
        (packing : Set (Finset object.Vertex)).PairwiseDisjoint id := by
      intro left leftMember right rightMember distinct
      exact valid.2 left leftMember right rightMember distinct
    rw [windowSupport, Finset.sum_biUnion pairwise]
    simp only [id_eq]
  rw [split]
  have each : ∀ member ∈ packing,
      2 * (order - 1) ≤ ∑ vertex ∈ member,
        object.internalDegree (windowSupport packing) vertex := by
    intro member present
    calc 2 * (order - 1)
        = ∑ vertex ∈ member, object.internalDegree member vertex :=
          (object.sum_internalDegree_window (valid.1 member present)).symm
      _ ≤ ∑ vertex ∈ member,
            object.internalDegree (windowSupport packing) vertex :=
          Finset.sum_le_sum fun vertex inside =>
            object.internalDegree_mono
              (fun other otherInside =>
                mem_windowSupport present otherInside) vertex
  calc 2 * (order - 1) * packing.card
      = ∑ _member ∈ packing, 2 * (order - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum each

/-! ## `lem:surplus-aware-window-stub`, assembled -/

/-- The incidences across the window/remainder cut are the same number counted
from either side. -/
theorem boundaryIncidence_remainderSupport_eq (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    object.boundaryIncidence (object.remainderSupport packing) =
      object.boundaryIncidence (windowSupport packing) := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  have complement :
      (Finset.univ \ object.remainderSupport packing) = windowSupport packing := by
    rw [remainderSupport]
    ext vertex
    simp
  have fromRemainder :
      object.boundaryIncidence (object.remainderSupport packing) =
        ∑ vertex ∈ object.remainderSupport packing,
          object.internalDegree (windowSupport packing) vertex := by
    rw [boundaryIncidence]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have split := object.internalDegree_add_internalDegree_compl
      (object.remainderSupport packing) vertex
    rw [complement] at split
    omega
  have fromWindow :
      object.boundaryIncidence (windowSupport packing) =
        ∑ vertex ∈ windowSupport packing,
          object.internalDegree (object.remainderSupport packing) vertex := by
    rw [boundaryIncidence]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have split := object.internalDegree_add_internalDegree_compl
      (windowSupport packing) vertex
    have same : (Finset.univ \ windowSupport packing) =
        object.remainderSupport packing := by
      rw [remainderSupport]
    rw [same] at split
    omega
  rw [fromRemainder, fromWindow]
  exact object.sum_internalDegree_comm _ _

/-- **`lem:surplus-aware-window-stub`.**

`def⁺(R) + 2(order − 1)·p ≤ δ·order·p + σ_W`, the subtraction-free form of

  `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order − 1))·p + σ_W`,

which at the manuscript's presentation is `def⁺(R) ≤ 15p₁₃ + σ_W`: `δ·order`
is its `39` and `2(order − 1)` its `24`.  Neither numeral appears.

No near-cubic hypothesis is used, exactly as the manuscript states. -/
theorem positiveDeficiency_add_internal_mass_le (object : FiniteObject.{u})
    {order threshold : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.positiveDeficiency (object.remainderSupport packing) threshold +
        2 * (order - 1) * packing.card ≤
      threshold * (order * packing.card) +
        object.ambientSurplus (windowSupport packing) threshold := by
  classical
  have demand :
      object.positiveDeficiency (object.remainderSupport packing) threshold ≤
        object.boundaryIncidence (windowSupport packing) := by
    rw [← object.boundaryIncidence_remainderSupport_eq packing]
    exact object.positiveDeficiency_le_boundaryIncidence _ threshold baseline
  have supply :
      object.boundaryIncidence (windowSupport packing) +
          ∑ vertex ∈ windowSupport packing,
            object.internalDegree (windowSupport packing) vertex =
        threshold * (windowSupport packing).card +
          object.ambientSurplus (windowSupport packing) threshold := by
    rw [object.boundaryIncidence_eq_sub,
      ← object.sum_degree_eq_threshold_mul_card_add_ambientSurplus _ threshold
        baseline]
    have bounded :
        (∑ vertex ∈ windowSupport packing,
          object.internalDegree (windowSupport packing) vertex) ≤
          ∑ vertex ∈ windowSupport packing, object.degree vertex :=
      Finset.sum_le_sum fun vertex _ =>
        object.internalDegree_le_degree _ vertex
    omega
  have mass := object.internal_mass_windowSupport valid
  rw [object.windowSupport_card_eq valid] at supply
  omega

end FiniteObject

end Hypostructure.Graph
