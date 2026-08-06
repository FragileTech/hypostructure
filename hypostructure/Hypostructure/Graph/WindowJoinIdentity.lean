import Hypostructure.Graph.WindowInternalMass

/-!
# `lem:exact-window-join-identity`, and the two incidence families it counts

`def:window-remainder-surplus-split` names three quantities on a packing `𝒫` of
induced windows: the window and remainder surpluses

  `σ_W = Σ_{w ∈ W} (d_G(w) − δ)`,  `σ_R = Σ_{v ∈ R} (d_G(v) − δ)`,

which are `BoundaryDemand`'s `ambientSurplus` read at the two sides of the cut,
and `e_×(W)`, the number of edges whose two ends lie in *distinct* packed
windows.  `lem:exact-window-join-identity` is then

  `e(R,W) + 2e_×(W) = 15p₁₃ + σ_W`.

Both sides of that display are incidence counts, and this module builds them as
the two finite families the manuscript names:

* `windowRemainderIncidences` — the ordered adjacent pairs `(v, w)` with `v ∈ R`
  and `w ∈ W`.  Every `R`–`W` edge occurs exactly once, so the count is `e(R,W)`.
* `crossWindowIncidences` — the ordered adjacent pairs `(v, w)` whose two ends
  lie in distinct packed windows.  Every cross-window edge occurs once at each of
  its two window ends, so the count is `2e_×(W)`; this is exactly the manuscript's
  "each cross-window edge contributes one token at each of its two window ends",
  and it is why the two families are the window token supply of
  `def:capacity-token-ledger`.

The identity itself is the manuscript's degree sum over `W`, with the internal
mass evaluated exactly rather than bounded: the incidences of `W` that stay
inside `W` are the `2(order − 1)` path incidences each packed window already
carries plus the cross-window incidences, and the rest leave.  `WindowInternalMass`
supplies the per-window mass; what is added here is that the two contributions
exhaust the internal mass.

The window order and the baseline are parameters: `15 = δ·order − 2(order − 1)`
at `δ = 3`, `order = 13`, and neither numeral is written.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u

namespace FiniteObject

variable {object : FiniteObject.{u}}

/-! ## The two incidence families of the cut -/

/-- **`e(R,W)` as a family.**  The ordered adjacent pairs leaving the remainder:
`(v, w)` with `v ∈ R`, `w ∈ W` and `vw ∈ E(G)`.  An `R`–`W` edge has one end on
each side, so it contributes exactly one such pair. -/
noncomputable def windowRemainderIncidences (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Finset (object.Vertex × object.Vertex) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact (object.remainderSupport packing).biUnion fun vertex =>
    (object.graph.neighborFinset vertex ∩ windowSupport packing).image
      fun other => (vertex, other)

/-- `W ∖ P`: the covered support outside one packed window. -/
noncomputable def windowSupportOutside (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) (member : Finset object.Vertex) :
    Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact windowSupport packing \ member

/-- **`2e_×(W)` as a family.**  The ordered adjacent pairs whose two ends lie in
*distinct* packed windows: `(v, w)` with `v` in a packed window and `w` in a
different one.  A cross-window edge contributes one pair at each of its two
window ends. -/
noncomputable def crossWindowIncidences (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Finset (object.Vertex × object.Vertex) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact packing.biUnion fun member =>
    member.biUnion fun vertex =>
      (object.graph.neighborFinset vertex ∩
          object.windowSupportOutside packing member).image
        fun other => (vertex, other)

/-- A pair of the remainder family is an `R`–`W` edge, and every `R`–`W` edge is
one: the family is the manuscript's `E(R,W)` read as ordered pairs from the
remainder side. -/
theorem mem_windowRemainderIncidences_iff
    (packing : Finset (Finset object.Vertex))
    (pair : object.Vertex × object.Vertex) :
    pair ∈ object.windowRemainderIncidences packing ↔
      object.graph.Adj pair.1 pair.2 ∧
        pair.1 ∈ object.remainderSupport packing ∧
        pair.2 ∈ windowSupport packing := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  obtain ⟨left, right⟩ := pair
  simp only [windowRemainderIncidences, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_inter, SimpleGraph.mem_neighborFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨vertex, inside, other, ⟨adjacent, window⟩, rfl, rfl⟩
    exact ⟨adjacent, inside, window⟩
  · rintro ⟨adjacent, inside, window⟩
    exact ⟨left, inside, right, ⟨adjacent, window⟩, rfl, rfl⟩

/-- A pair of the cross-window family is an edge with its two ends in distinct
packed windows, and every such ordered pair is one. -/
theorem mem_crossWindowIncidences_iff
    (packing : Finset (Finset object.Vertex))
    (pair : object.Vertex × object.Vertex) :
    pair ∈ object.crossWindowIncidences packing ↔
      object.graph.Adj pair.1 pair.2 ∧
        ∃ member ∈ packing, pair.1 ∈ member ∧
          pair.2 ∈ windowSupport packing ∧ pair.2 ∉ member := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  obtain ⟨left, right⟩ := pair
  simp only [crossWindowIncidences, windowSupportOutside, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_inter, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨member, present, vertex, inside, other, ⟨adjacent, window, outside⟩,
      rfl, rfl⟩
    exact ⟨adjacent, member, present, inside, window, outside⟩
  · rintro ⟨adjacent, member, present, inside, window, outside⟩
    exact ⟨member, present, left, inside, right, ⟨adjacent, window, outside⟩,
      rfl, rfl⟩

/-! ## The two counts -/

/-- The blocks of a vertex-indexed incidence family are disjoint, so the family
counts blockwise: each block is the vertex's own neighbour selection tagged with
that vertex. -/
theorem card_biUnion_incidenceBlocks (object : FiniteObject.{u})
    (source : Finset object.Vertex)
    (target : object.Vertex → Finset object.Vertex) :
    letI : FinEnum object.Vertex := object.vertices
    (source.biUnion fun vertex =>
        (target vertex).image fun other => (vertex, other)).card =
      ∑ vertex ∈ source, (target vertex).card := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun vertex _ =>
      Finset.card_image_of_injective _ fun _ _ equality => congrArg Prod.snd equality
  · intro left _ right _ distinct
    refine Finset.disjoint_left.2 fun pair leftMember rightMember => ?_
    obtain ⟨_, _, leftEq⟩ := Finset.mem_image.1 leftMember
    obtain ⟨_, _, rightEq⟩ := Finset.mem_image.1 rightMember
    exact distinct ((congrArg Prod.fst leftEq).trans (congrArg Prod.fst rightEq).symm)

/-- **`|E(R,W)| = e(R,W)`.**  The remainder family counts the incidences leaving
the remainder, which is `BoundaryDemand`'s `boundaryIncidence` on that side. -/
theorem card_windowRemainderIncidences (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    (object.windowRemainderIncidences packing).card =
      object.boundaryIncidence (object.remainderSupport packing) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  rw [windowRemainderIncidences,
    card_biUnion_incidenceBlocks object (object.remainderSupport packing)
      fun vertex => object.graph.neighborFinset vertex ∩ windowSupport packing,
    boundaryIncidence]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  have complement :
      (Finset.univ \ object.remainderSupport packing) = windowSupport packing := by
    rw [remainderSupport]
    ext other
    simp
  have split := object.internalDegree_add_internalDegree_compl
    (object.remainderSupport packing) vertex
  rw [complement] at split
  have inner : object.internalDegree (windowSupport packing) vertex =
      (object.graph.neighborFinset vertex ∩ windowSupport packing).card := rfl
  omega

/-- **`|I_×(W)| = Σ_{P ∈ 𝒫} Σ_{v ∈ P} d_{W∖P}(v)`.**  The cross-window family
counts, window by window, the incidences that leave the window but stay inside
the covered support. -/
theorem card_crossWindowIncidences (object : FiniteObject.{u})
    {order : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    (object.crossWindowIncidences packing).card =
      ∑ member ∈ packing, ∑ vertex ∈ member,
        object.internalDegree (object.windowSupportOutside packing member) vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have first : ∀ (member : Finset object.Vertex)
      (pair : object.Vertex × object.Vertex),
      pair ∈ member.biUnion (fun vertex =>
          (object.graph.neighborFinset vertex ∩
            object.windowSupportOutside packing member).image
            fun other => (vertex, other)) →
      pair.1 ∈ member := by
    intro member pair inside
    obtain ⟨vertex, present, image⟩ := Finset.mem_biUnion.1 inside
    obtain ⟨_, _, equality⟩ := Finset.mem_image.1 image
    exact (congrArg Prod.fst equality) ▸ present
  rw [crossWindowIncidences, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun member _ => ?_
    exact card_biUnion_incidenceBlocks object member
      fun vertex =>
        object.graph.neighborFinset vertex ∩
          object.windowSupportOutside packing member
  · intro left leftMember right rightMember distinct
    refine Finset.disjoint_left.2 fun pair leftInside rightInside => ?_
    exact Finset.disjoint_left.1 (valid.2 left leftMember right rightMember distinct)
      (first left pair leftInside) (first right pair rightInside)

/-! ## The internal mass of the covered support, evaluated exactly -/

/-- **Inside one window, or across to another.**  A packed window's vertex has
its `W`-internal neighbours split between the window itself and the rest of the
covered support; there is no third possibility. -/
theorem internalDegree_add_internalDegree_windowSupportOutside
    (object : FiniteObject.{u}) {packing : Finset (Finset object.Vertex)}
    {member : Finset object.Vertex} (present : member ∈ packing)
    (vertex : object.Vertex) :
    object.internalDegree member vertex +
        object.internalDegree (object.windowSupportOutside packing member) vertex =
      object.internalDegree (windowSupport packing) vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have contained : member ⊆ windowSupport packing :=
    fun other inside => mem_windowSupport present inside
  have inner :
      object.graph.neighborFinset vertex ∩ member =
        (object.graph.neighborFinset vertex ∩ windowSupport packing) ∩ member := by
    ext other
    simp only [Finset.mem_inter]
    exact ⟨fun ⟨adjacent, inside⟩ => ⟨⟨adjacent, contained inside⟩, inside⟩,
      fun ⟨⟨adjacent, _⟩, inside⟩ => ⟨adjacent, inside⟩⟩
  have outer :
      object.graph.neighborFinset vertex ∩
          object.windowSupportOutside packing member =
        (object.graph.neighborFinset vertex ∩ windowSupport packing) \ member := by
    ext other
    simp only [windowSupportOutside, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  show (object.graph.neighborFinset vertex ∩ member).card +
      (object.graph.neighborFinset vertex ∩
        object.windowSupportOutside packing member).card =
    (object.graph.neighborFinset vertex ∩ windowSupport packing).card
  rw [inner, outer, Finset.card_inter_add_card_sdiff]

/-- **The internal mass of `W`, exactly.**
`Σ_{w ∈ W} d_W(w) = 2(order − 1)p + |I_×(W)|`: an incidence that stays inside the
covered support either stays inside its own packed window -- and each window
carries exactly `2(order − 1)` of those, being an induced copy of the window --
or it crosses to another packed window. -/
theorem sum_internalDegree_windowSupport (object : FiniteObject.{u})
    {order : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    ∑ vertex ∈ windowSupport packing,
        object.internalDegree (windowSupport packing) vertex =
      2 * (order - 1) * packing.card +
        (object.crossWindowIncidences packing).card := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  have pairwise : (packing : Set (Finset object.Vertex)).PairwiseDisjoint id := by
    intro left leftMember right rightMember distinct
    exact valid.2 left leftMember right rightMember distinct
  have split :
      ∑ vertex ∈ windowSupport packing,
          object.internalDegree (windowSupport packing) vertex =
        ∑ member ∈ packing, ∑ vertex ∈ member,
          object.internalDegree (windowSupport packing) vertex := by
    rw [windowSupport, Finset.sum_biUnion pairwise]
    simp only [id_eq]
  have blockwise : ∀ member ∈ packing,
      (∑ vertex ∈ member, object.internalDegree (windowSupport packing) vertex) =
        2 * (order - 1) +
          ∑ vertex ∈ member,
            object.internalDegree (object.windowSupportOutside packing member)
              vertex := by
    intro member present
    have pointwise :
        (∑ vertex ∈ member, object.internalDegree (windowSupport packing) vertex) =
          (∑ vertex ∈ member, object.internalDegree member vertex) +
            ∑ vertex ∈ member,
              object.internalDegree (object.windowSupportOutside packing member)
                vertex := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun vertex _ =>
        (object.internalDegree_add_internalDegree_windowSupportOutside present
          vertex).symm
    rw [pointwise, object.sum_internalDegree_window (valid.1 member present)]
  rw [split, Finset.sum_congr rfl blockwise, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm,
    object.card_crossWindowIncidences valid]

/-! ## `lem:exact-window-join-identity` -/

/-- **`lem:exact-window-join-identity`**, in subtraction-free form:

  `e(R,W) + 2(order − 1)p + 2e_×(W) = δ·order·p + σ_W`,

which at the registered presentation `δ = 3`, `order = 13` is the manuscript's

  `e(R,W) + 2e_×(W) = 15p₁₃ + σ_W`,

`15` being `δ·order − 2(order − 1) = 39 − 24`.  The proof is the manuscript's:
sum degrees over the covered support, which is `δ|W| + σ_W` because every vertex
is at the baseline; the same sum counts each internal incidence once from its own
end and each leaving incidence once, and the internal ones are exactly the path
incidences of the packed windows together with the cross-window incidences. -/
theorem exact_window_join_identity (object : FiniteObject.{u})
    {order threshold : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.windowRemainderIncidences packing).card +
        (2 * (order - 1) * packing.card +
          (object.crossWindowIncidences packing).card) =
      threshold * (order * packing.card) +
        object.ambientSurplus (windowSupport packing) threshold := by
  classical
  have cut : (object.windowRemainderIncidences packing).card =
      object.boundaryIncidence (windowSupport packing) := by
    rw [object.card_windowRemainderIncidences packing,
      object.boundaryIncidence_remainderSupport_eq packing]
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
  have mass := object.sum_internalDegree_windowSupport valid
  rw [object.windowSupport_card_eq valid] at supply
  omega

/-! ## `def:window-remainder-surplus-split`: `σ(G) = σ_W + σ_R` -/

/-- **`σ(G) = σ_W + σ_R`.**  The covered support and the remainder partition the
vertex set, and surplus is a sum of vertex-local terms. -/
theorem ambientSurplus_windowSupport_add_remainderSupport (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.ambientSurplus (windowSupport packing) threshold +
        object.ambientSurplus (object.remainderSupport packing) threshold =
      object.degreeSurplus threshold := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [← object.ambientSurplus_univ_eq_degreeSurplus threshold baseline,
    ambientSurplus, ambientSurplus, ambientSurplus, remainderSupport,
    Nat.add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ _)

end FiniteObject

end Hypostructure.Graph
