import Hypostructure.Graph.WindowRemainder

/-!
# Positive deficiency and the boundary-incidence supply

`def:deficiency-surplus` measures external degree demand by *positive
deficiency* rather than signed charge: a vertex of internal degree below the
baseline needs that many incidences leaving its region, and a high-degree
neighbour cannot cancel the need.

Everything here is a sum of vertex-local counts, which is how the manuscript
argues.  `internalDegree` is the number of neighbours a vertex has inside a
support; the ambient degree minus it is the number that leave.  No edge set is
ever manipulated, so nothing has to be transported through an induced-subgraph
isomorphism.

The baseline is a parameter.  Nothing here knows the manuscript's value for it,
and the `3` of `def:deficiency-surplus` never appears.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u

namespace FiniteObject

/-- The number of neighbours a vertex has inside a support. -/
noncomputable def internalDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact ((object.graph.neighborFinset vertex) ∩ support).card

/-- A vertex has no more neighbours inside a support than it has overall. -/
theorem internalDegree_le_degree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    object.internalDegree support vertex ≤ object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simpa [internalDegree, FiniteObject.degree] using
    Finset.card_le_card
      (Finset.inter_subset_left (s₁ := object.graph.neighborFinset vertex)
        (s₂ := support))

/-- **The internal degree is the degree of the induced restriction.**

`internalDegree` counts a vertex's neighbours inside a support without ever
building the induced object; this identifies that count with the honest degree
of `induce`, which is what turns a pointwise internal-degree bound into a
`MinimumDegreeAtLeast` statement about a genuine subgraph. -/
theorem degree_induce_eq_internalDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (vertex : (object.induce support).Vertex) :
    (object.induce support).degree vertex =
      object.internalDegree support vertex.1 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  letI : DecidableRel induced.graph.Adj := induced.decideAdj
  classical
  rw [degree, internalDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_coe ((object.graph.neighborFinset vertex.1) ∩ support)]
  -- Neighbours of `vertex` in the restriction are exactly the neighbours of
  -- `vertex.1` that lie in the support.
  exact Fintype.card_congr
    { toFun := fun neighbour =>
        ⟨neighbour.1.1, Finset.mem_inter.mpr
          ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr neighbour.2,
            neighbour.1.2⟩⟩
      invFun := fun neighbour =>
        ⟨⟨neighbour.1, (Finset.mem_inter.mp neighbour.2).2⟩,
          (SimpleGraph.mem_neighborFinset _ _ _).mp
            (Finset.mem_inter.mp neighbour.2).1⟩
      left_inv := fun neighbour => by ext; rfl
      right_inv := fun neighbour => by ext; rfl }

/-- Enlarging the support cannot lose an internal neighbour. -/
theorem internalDegree_mono (object : FiniteObject.{u})
    {small large : Finset object.Vertex} (contained : small ⊆ large)
    (vertex : object.Vertex) :
    object.internalDegree small vertex ≤
      object.internalDegree large vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact Finset.card_le_card (Finset.inter_subset_inter_left contained)

/-- **`def:deficiency-surplus`.**  `def⁺(X) = Σ_{v∈X} max{0, δ − d_X(v)}`, with
truncated subtraction supplying the `max`. -/
noncomputable def positiveDeficiency (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  ∑ vertex ∈ support, (threshold - object.internalDegree support vertex)

/-- **`def:window-remainder-surplus-split`.**  The ambient surplus carried by
the vertices of a support, `Σ_{v} max{0, d_G(v) − δ}`. -/
noncomputable def ambientSurplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  ∑ vertex ∈ support, (object.degree vertex - threshold)

/-- `e(X, G − X)`: the incidences leaving a support, counted from inside it. -/
noncomputable def boundaryIncidence (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Nat :=
  ∑ vertex ∈ support,
    (object.degree vertex - object.internalDegree support vertex)

/-- **`lem:surplus-aware-window-stub`, first inequality.**
`def⁺(R) ≤ e(R, W)`.

The manuscript's argument verbatim: on the standing baseline every vertex of
the remainder already has ambient degree at least `δ`, so it is deficient
*inside* the remainder only because some of its incidences leave.  Writing
`d_G(v) = d_R(v) + e_v` gives `max{0, δ − d_R(v)} ≤ e_v` pointwise, and summing
over the remainder gives the claim.

No near-cubic hypothesis is used, exactly as the manuscript notes. -/
theorem positiveDeficiency_le_boundaryIncidence (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.positiveDeficiency support threshold ≤
      object.boundaryIncidence support :=
  Finset.sum_le_sum fun vertex _ =>
    Nat.sub_le_sub_right (baseline vertex) _

/-- The degree sum over a support splits into its baseline part and its
surplus: `Σ_{v∈X} d_G(v) = δ·|X| + σ(X)`.  This is the `39p₁₃ + σ_W` of
`lem:exact-window-join-identity` with the numerals left to the caller. -/
theorem sum_degree_eq_threshold_mul_card_add_ambientSurplus
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    ∑ vertex ∈ support, object.degree vertex =
      threshold * support.card + object.ambientSurplus support threshold := by
  classical
  have expand : ∑ vertex ∈ support, object.degree vertex =
      ∑ vertex ∈ support, ((object.degree vertex - threshold) + threshold) :=
    Finset.sum_congr rfl fun vertex _ =>
      (Nat.sub_add_cancel (baseline vertex)).symm
  rw [expand, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ambientSurplus, Nat.mul_comm]
  omega

/-- The boundary incidence of a support is its degree sum minus its internal
degree sum.  Truncated subtraction distributes because a vertex never has more
internal neighbours than neighbours. -/
theorem boundaryIncidence_eq_sub (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    object.boundaryIncidence support =
      (∑ vertex ∈ support, object.degree vertex) -
        ∑ vertex ∈ support, object.internalDegree support vertex := by
  classical
  rw [boundaryIncidence, Finset.sum_tsub_distrib]
  intro vertex _
  exact object.internalDegree_le_degree support vertex

/-- **`lem:surplus-aware-window-stub`, capacity half, in its reduced form.**

`e(W, R) ≤ δ·|W| + σ_W − (internal degree mass of the packing)`.

Read at the packed windows this is the manuscript's
`e(R,W) ≤ 15p₁₃ + σ_W`: the degree sum over `W` is `δ|W| + σ_W`, and every
incidence that stays inside a window is one that does not leave.  The
manuscript evaluates the internal mass as `2(order − 1)` per window -- twice
the path edges of an induced copy -- and `δ|W| = δ·order·p₁₃`, giving
`(δ·order − 2(order − 1))·p₁₃ + σ_W`, which at the registered presentation is
`15p₁₃ + σ_W`.  Neither numeral appears here. -/
theorem boundaryIncidence_le_of_internal_mass (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold internalMass : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (mass : internalMass ≤
      ∑ vertex ∈ support, object.internalDegree support vertex) :
    object.boundaryIncidence support ≤
      threshold * support.card + object.ambientSurplus support threshold -
        internalMass := by
  rw [object.boundaryIncidence_eq_sub support,
    object.sum_degree_eq_threshold_mul_card_add_ambientSurplus support threshold
      baseline]
  exact Nat.sub_le_sub_left mass _

/-! ## The two sides of one incidence count -/

/-- A vertex's neighbours split between a support and its complement. -/
theorem internalDegree_add_internalDegree_compl (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    object.internalDegree support vertex +
        object.internalDegree
          (by letI : FinEnum object.Vertex := object.vertices
              classical
              exact Finset.univ \ support) vertex =
      object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have rewrite :
      object.graph.neighborFinset vertex ∩ (Finset.univ \ support) =
        object.graph.neighborFinset vertex \ support := by
    ext other; simp
  have split :
      (object.graph.neighborFinset vertex ∩ support).card +
          (object.graph.neighborFinset vertex ∩ (Finset.univ \ support)).card =
        (object.graph.neighborFinset vertex).card := by
    rw [rewrite, Nat.add_comm, Finset.card_sdiff_add_card_inter]
  simpa [internalDegree, FiniteObject.degree] using split

/-- A closed region reads the same internal degree as its closure: when every
neighbour landing in `mid` lands in `inner ⊆ mid`, the two internal degrees
agree. -/
theorem internalDegree_eq_of_closed (object : FiniteObject.{u})
    {inner mid : Finset object.Vertex} {vertex : object.Vertex}
    (innerMid : inner ⊆ mid)
    (closed : ∀ other, object.graph.Adj vertex other → other ∈ mid →
      other ∈ inner) :
    object.internalDegree mid vertex =
      object.internalDegree inner vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp only [internalDegree]
  refine congrArg Finset.card (Finset.ext fun other => ?_)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun pair => ⟨pair.1, closed other pair.1 pair.2⟩,
    fun pair => ⟨pair.1, innerMid pair.2⟩⟩

/-- **The boundary incidence is symmetric.**  Counting the incidences that
leave a support from inside it, and counting them from outside, give the same
number: both are the number of adjacent ordered pairs across the cut.

This is what lets `def⁺(R) ≤ e(R,W)`, proved on the remainder side, chain with
the capacity bound, proved on the window side. -/
theorem sum_internalDegree_comm (object : FiniteObject.{u})
    (left right : Finset object.Vertex) :
    ∑ vertex ∈ left, object.internalDegree right vertex =
      ∑ vertex ∈ right, object.internalDegree left vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have expand : ∀ (source target : Finset object.Vertex),
      ∑ vertex ∈ source, object.internalDegree target vertex =
        ∑ vertex ∈ source, ∑ other ∈ target,
          (if object.graph.Adj vertex other then 1 else 0) := by
    intro source target
    refine Finset.sum_congr rfl fun vertex _ => ?_
    rw [internalDegree, Finset.inter_comm,
      ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl fun other _ => by
      simp [SimpleGraph.mem_neighborFinset]
  rw [expand, expand, Finset.sum_comm]
  exact Finset.sum_congr rfl fun vertex _ =>
    Finset.sum_congr rfl fun other _ => by
      simp [SimpleGraph.adj_comm]

/-! ## `σ_W ≤ σ(G)`: paying a region's surplus out of the object's own -/

/-- **`σ_W ≤ σ(G)`.**  Surplus is a sum of nonnegative vertex-local terms, so a
larger region carries at least as much of it.  The manuscript's own reason for
`σ_W ≤ σ(G)`: "the windows are vertex-disjoint and surplus is nonnegative". -/

theorem ambientSurplus_le_of_subset (object : FiniteObject.{u})
    {small large : Finset object.Vertex} (contained : small ⊆ large)
    (threshold : Nat) :
    object.ambientSurplus small threshold ≤
      object.ambientSurplus large threshold :=
  Finset.sum_le_sum_of_subset contained

/-- **The surplus of any region is bounded by the object's own**, `σ_W ≤ σ(G)`.

The whole object's surplus, read as a region, *is* the `degreeSurplus`
observable that the node-`[19]` split compares: on the standing baseline the
handshake gives `Σ_v (d(v) − δ) = 2m − δn`.  So this is not a second surplus
notion, and a window-local surplus can be paid for out of a registered ceiling
on `σ(G)`. -/
theorem ambientSurplus_univ_eq_degreeSurplus (object : FiniteObject.{u})
    (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    letI : FinEnum object.Vertex := object.vertices
    object.ambientSurplus Finset.univ threshold =
      object.degreeSurplus threshold := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have split := object.sum_degree_eq_threshold_mul_card_add_ambientSurplus
    Finset.univ threshold baseline
  have handshake :
      (∑ vertex : object.Vertex, object.degree vertex) =
        2 * object.edgeCount := by
    simpa [FiniteObject.degree, FiniteObject.edgeCount] using
      object.graph.sum_degrees_eq_twice_card_edges
  have card :
      (Finset.univ : Finset object.Vertex).card = object.vertexCount := by
    simp [FiniteObject.vertexCount, Finset.card_univ,
      FinEnum.card_eq_fintypeCard]
  rw [handshake, card] at split
  unfold FiniteObject.degreeSurplus
  omega

theorem ambientSurplus_le_degreeSurplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.ambientSurplus support threshold ≤
      object.degreeSurplus threshold := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [← object.ambientSurplus_univ_eq_degreeSurplus threshold baseline]
  exact object.ambientSurplus_le_of_subset (Finset.subset_univ support) threshold

/-- A covered set reads at most the covering pair's internal degrees.  The
statement carries no set constructor, so it applies at any decidability
flavour. -/
theorem internalDegree_le_add_of_cover (object : FiniteObject.{u})
    {covering left right : Finset object.Vertex} (vertex : object.Vertex)
    (covered : ∀ other ∈ covering, other ∈ left ∨ other ∈ right) :
    object.internalDegree covering vertex ≤
      object.internalDegree left vertex +
        object.internalDegree right vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp only [internalDegree]
  have subsetUnion : object.graph.neighborFinset vertex ∩ covering ⊆
      (object.graph.neighborFinset vertex ∩ left) ∪
        (object.graph.neighborFinset vertex ∩ right) := by
    intro other omem
    rw [Finset.mem_inter] at omem
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
    rcases covered other omem.2 with inLeft | inRight
    · exact Or.inl ⟨omem.1, inLeft⟩
    · exact Or.inr ⟨omem.1, inRight⟩
  calc (object.graph.neighborFinset vertex ∩ covering).card
      ≤ ((object.graph.neighborFinset vertex ∩ left) ∪
          (object.graph.neighborFinset vertex ∩ right)).card :=
        Finset.card_le_card subsetUnion
    _ ≤ _ := Finset.card_union_le _ _

open scoped Classical in
/-- Deleting a vertex set transfers at most its support-internal degrees into
new positive deficiency: each deleted edge opens one deficiency slot at its
surviving endpoint. -/
theorem positiveDeficiency_sdiff_le (object : FiniteObject.{u})
    (support deleted : Finset object.Vertex) (threshold : Nat) :
    object.positiveDeficiency (support \ deleted) threshold ≤
      object.positiveDeficiency support threshold +
        ∑ vertex ∈ deleted, object.internalDegree support vertex := by
  classical
  have pointwise : ∀ vertex ∈ support \ deleted,
      threshold - object.internalDegree (support \ deleted) vertex ≤
        (threshold - object.internalDegree support vertex) +
          object.internalDegree deleted vertex := by
    intro vertex _
    have mono := object.internalDegree_mono
      (Finset.sdiff_subset : support \ deleted ⊆ support) vertex
    have cover := object.internalDegree_le_add_of_cover
      (covering := support) (left := support \ deleted) (right := deleted)
      vertex (fun other mem => by
        by_cases odel : other ∈ deleted
        · exact Or.inr odel
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨mem, odel⟩))
    omega
  have summed : object.positiveDeficiency (support \ deleted) threshold ≤
      (∑ vertex ∈ support \ deleted,
        (threshold - object.internalDegree support vertex)) +
        ∑ vertex ∈ support \ deleted,
          object.internalDegree deleted vertex := by
    unfold positiveDeficiency
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum pointwise
  have deficiencyPart : (∑ vertex ∈ support \ deleted,
      (threshold - object.internalDegree support vertex)) ≤
      object.positiveDeficiency support threshold := by
    unfold positiveDeficiency
    exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have crossPart : (∑ vertex ∈ support \ deleted,
      object.internalDegree deleted vertex) ≤
      ∑ vertex ∈ deleted, object.internalDegree support vertex := by
    rw [object.sum_internalDegree_comm (support \ deleted) deleted]
    exact Finset.sum_le_sum fun vertex _ =>
      object.internalDegree_mono Finset.sdiff_subset vertex
  omega

end FiniteObject

end Hypostructure.Graph
