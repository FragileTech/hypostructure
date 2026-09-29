import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.RemainderGlue

/-!
# The stub-deficit identity at a support

For a support `X` of a finite object with baseline degree `δ`, write
`e(X, G−X)` for the boundary incidences, `σ(X) = Σ_X (d_G − δ)` for the ambient
surplus, `def⁺(X) = Σ_X (δ − d_X)⁺` for the positive deficiency and
`exc(X) = Σ_X (d_X − δ)⁺` for the internal excess.  Pointwise
`(d_G − d_X) + (d_X − δ)⁺ = (d_G − δ) + (δ − d_X)⁺`, so

  `e(X, G−X) + exc(X) = σ(X) + def⁺(X)`.

The handshake `Σ_X d_X = 2·e(G[X])` then gives `2·e(G[X]) + e(X, G−X) = δ|X| + σ(X)`.
Nothing here knows a presentation: `δ` is a parameter.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u

namespace FiniteObject

/-- `exc(X) = Σ_{v∈X} max{0, d_X(v) − δ}`. -/
noncomputable def internalExcess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  ∑ vertex ∈ support, (object.internalDegree support vertex - threshold)

/-- **The stub-deficit identity**: `e(X, G−X) + exc(X) = σ(X) + def⁺(X)`. -/
theorem boundaryIncidence_add_internalExcess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.boundaryIncidence support + object.internalExcess support threshold =
      object.ambientSurplus support threshold +
        object.positiveDeficiency support threshold := by
  unfold boundaryIncidence internalExcess ambientSurplus positiveDeficiency
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  have le := object.internalDegree_le_degree support vertex
  have base := baseline vertex
  omega

/-- The handshake at a support: the internal degrees sum to twice the
inherited edge count. -/
theorem sum_internalDegree_eq_two_mul_internalEdgeCount (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    ∑ vertex ∈ support, object.internalDegree support vertex =
      2 * object.internalEdgeCount support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  -- ordered adjacent pairs inside the support
  have expand : ∑ vertex ∈ support, object.internalDegree support vertex =
      ((support ×ˢ support).filter fun p => object.graph.Adj p.1 p.2).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    rw [internalDegree, Finset.inter_comm, ← Finset.filter_mem_eq_inter,
      Finset.card_filter]
    exact Finset.sum_congr rfl fun other _ => by
      simp [SimpleGraph.mem_neighborFinset]
  rw [expand, internalEdgeCount]
  -- the map `(v, w) ↦ s(v, w)` is two-to-one onto the inherited edges
  let toEdge : object.Vertex × object.Vertex → Sym2 object.Vertex := fun p => s(p.1, p.2)
  have maps : ∀ p ∈ (support ×ˢ support).filter (fun p => object.graph.Adj p.1 p.2),
      toEdge p ∈ object.graph.edgeFinset.filter
        fun edge => ∀ vertex ∈ edge, vertex ∈ support := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, toEdge, SimpleGraph.mem_edgeSet]
    refine ⟨hp.2, ?_⟩
    intro vertex hv
    rcases Sym2.mem_iff.mp hv with h | h
    · rw [h]; exact hp.1.1
    · rw [h]; exact hp.1.2
  rw [Finset.card_eq_sum_card_fiberwise (f := toEdge) maps]
  have fibre : ∀ edge ∈ object.graph.edgeFinset.filter
      (fun edge => ∀ vertex ∈ edge, vertex ∈ support),
      (((support ×ˢ support).filter fun p => object.graph.Adj p.1 p.2).filter
        fun p => toEdge p = edge).card = 2 := by
    intro edge hedge
    induction edge using Sym2.ind with
    | h a b =>
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] at hedge
      obtain ⟨adj, inS⟩ := hedge
      have ha : a ∈ support := inS a (by simp)
      have hb : b ∈ support := inS b (by simp)
      have ne : a ≠ b := adj.ne
      have eq : (((support ×ˢ support).filter fun p => object.graph.Adj p.1 p.2).filter
          fun p => toEdge p = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq, toEdge]
        constructor
        · rintro ⟨_, h⟩
          rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · subst h1; subst h2
            exact ⟨⟨⟨ha, hb⟩, adj⟩, rfl⟩
          · subst h1; subst h2
            exact ⟨⟨⟨hb, ha⟩, adj.symm⟩, Sym2.eq_swap⟩
      rw [eq, Finset.card_pair (fun h => ne (Prod.mk.inj h).1)]
  rw [Finset.sum_congr rfl fibre]
  simp [mul_comm]

/-- **`2·e(G[X]) + e(X, G−X) = δ|X| + σ(X)`.** -/
theorem two_mul_internalEdgeCount_add_boundaryIncidence (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    2 * object.internalEdgeCount support + object.boundaryIncidence support =
      threshold * support.card + object.ambientSurplus support threshold := by
  have sumEq := object.sum_degree_eq_threshold_mul_card_add_ambientSurplus support
    threshold baseline
  have hand := object.sum_internalDegree_eq_two_mul_internalEdgeCount support
  have bd := object.boundaryIncidence_eq_sub support
  have le : ∑ vertex ∈ support, object.internalDegree support vertex ≤
      ∑ vertex ∈ support, object.degree vertex :=
    Finset.sum_le_sum fun vertex _ => object.internalDegree_le_degree support vertex
  omega

/-! ## The canonical assignment of deficit units to boundary stubs -/

/-- The outside neighbours of `vertex` for the support, in G's own vertex order
(the `FinEnum` index of the object). -/
noncomputable def outsideNeighbourList (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) : List object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact ((((object.graph.neighborFinset vertex) \ support).image
    (FinEnum.equiv (α := object.Vertex))).sort (· ≤ ·)).map
      (FinEnum.equiv (α := object.Vertex)).symm

theorem length_outsideNeighbourList (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    (object.outsideNeighbourList support vertex).length =
      object.degree vertex - object.internalDegree support vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold outsideNeighbourList
  rw [List.length_map, Finset.length_sort,
    Finset.card_image_of_injective _ (FinEnum.equiv (α := object.Vertex)).injective]
  have split := Finset.card_sdiff_add_card_inter (object.graph.neighborFinset vertex) support
  have deg : (object.graph.neighborFinset vertex).card = object.degree vertex := by
    unfold FiniteObject.degree
    exact SimpleGraph.card_neighborFinset_eq_degree _ _
  have inner : (object.graph.neighborFinset vertex ∩ support).card =
      object.internalDegree support vertex := by
    unfold internalDegree; rfl
  omega

theorem nodup_outsideNeighbourList (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    (object.outsideNeighbourList support vertex).Nodup := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold outsideNeighbourList
  exact (Finset.sort_nodup _ _).map (FinEnum.equiv (α := object.Vertex)).symm.injective

theorem mem_outsideNeighbourList (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex other : object.Vertex) :
    other ∈ object.outsideNeighbourList support vertex ↔
      object.graph.Adj vertex other ∧ other ∉ support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold outsideNeighbourList
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨x, ⟨y, ⟨hy, hys⟩, rfl⟩, rfl⟩
    simpa using ⟨hy, hys⟩
  · rintro ⟨hadj, hns⟩
    exact ⟨_, ⟨other, ⟨hadj, hns⟩, rfl⟩, by simp⟩

/-- The deficit units of a support: `i < (δ − d_X(v))⁺` at each vertex `v ∈ X`.
Their number is `def⁺(X)`. -/
noncomputable def deficitUnits (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    Finset (object.Vertex × Nat) := by
  classical
  exact (support.sigma
    (fun vertex => Finset.range (threshold - object.internalDegree support vertex))).image
      (fun p => (p.1, p.2))

theorem card_deficitUnits (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    (object.deficitUnits support threshold).card =
      object.positiveDeficiency support threshold := by
  classical
  unfold deficitUnits positiveDeficiency
  rw [Finset.card_image_of_injective _ (by
    intro p q h
    exact Sigma.ext (congrArg Prod.fst h) (heq_of_eq (congrArg Prod.snd h)))]
  rw [Finset.card_sigma]
  simp

/-- The boundary stubs of a support: the incidences leaving it, as ordered pairs. -/
noncomputable def boundaryStubs (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset (object.Vertex × object.Vertex) := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact (support ×ˢ (Finset.univ \ support)).filter fun p => object.graph.Adj p.1 p.2

theorem card_boundaryStubs (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    (object.boundaryStubs support).card = object.boundaryIncidence support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold boundaryStubs boundaryIncidence
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  have len := object.length_outsideNeighbourList support vertex
  rw [← len]
  simp only []
  have same : (Finset.univ \ support).filter (fun other => object.graph.Adj vertex other) =
      (object.outsideNeighbourList support vertex).toFinset := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      List.mem_toFinset, mem_outsideNeighbourList]
    tauto
  have key := List.toFinset_card_of_nodup (object.nodup_outsideNeighbourList support vertex)
  rw [← same, Finset.card_filter] at key
  convert key

/-- **The canonical assignment**: the `i`-th deficit unit of `v` goes to the
`i`-th outside neighbour of `v` in G's vertex order. -/
noncomputable def stubAssignment (object : FiniteObject.{u})
    (support : Finset object.Vertex) (unit : object.Vertex × Nat) :
    Option (object.Vertex × object.Vertex) :=
  ((object.outsideNeighbourList support unit.1)[unit.2]?).map fun other => (unit.1, other)

/-- Under the baseline every deficit unit is assigned a boundary stub. -/
theorem stubAssignment_isSome (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (unit) (mem : unit ∈ object.deficitUnits support threshold) :
    ∃ stub ∈ object.boundaryStubs support, object.stubAssignment support unit = some stub := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  obtain ⟨vertex, index⟩ := unit
  unfold deficitUnits at mem
  simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_range, Prod.mk.injEq] at mem
  obtain ⟨⟨v', i'⟩, ⟨vS, hi⟩, hv, hi'⟩ := mem
  subst hv; subst hi'
  dsimp only at hi vS
  have len := object.length_outsideNeighbourList support v'
  have base := baseline v'
  have lt : i' < (object.outsideNeighbourList support v').length := by omega
  refine ⟨(v', (object.outsideNeighbourList support v')[i']), ?_, ?_⟩
  · have memL := (object.mem_outsideNeighbourList support v'
      ((object.outsideNeighbourList support v')[i'])).mp (List.getElem_mem lt)
    unfold boundaryStubs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    exact ⟨⟨vS, memL.2⟩, memL.1⟩
  · unfold stubAssignment
    simp [List.getElem?_eq_getElem lt]

/-- The assignment is injective on deficit units: distinct units use distinct stubs. -/
theorem stubAssignment_injOn (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    ∀ u ∈ object.deficitUnits support threshold, ∀ v ∈ object.deficitUnits support threshold,
      ∀ stub, object.stubAssignment support u = some stub →
        object.stubAssignment support v = some stub → u = v := by
  intro u _ v _ stub hu hv
  obtain ⟨a, i⟩ := u
  obtain ⟨b, j⟩ := v
  unfold stubAssignment at hu hv
  simp only [Option.map_eq_some_iff] at hu hv
  obtain ⟨x, hx, hxs⟩ := hu
  obtain ⟨y, hy, hys⟩ := hv
  have ab : a = b := by
    have := congrArg Prod.fst (hxs.trans hys.symm)
    simpa using this
  subst ab
  have xy : x = y := by
    have := congrArg Prod.snd (hxs.trans hys.symm)
    simpa using this
  subst xy
  have nd := object.nodup_outsideNeighbourList support a
  obtain ⟨hi, hix⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, hjx⟩ := List.getElem?_eq_some_iff.mp hy
  have := (List.Nodup.getElem_inj_iff nd).mp (hix.trans hjx.symm)
  rw [this]

end FiniteObject

end Hypostructure.Graph
