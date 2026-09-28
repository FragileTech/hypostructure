import Hypostructure.Graph.SingleEdgeContext

/-!
# Edge switches at a minimal object and the paths they force

Let `G` be a finite object with minimum degree at least `k` that has no accepted
cycle, while every lexicographically smaller object with minimum degree at least
`k` has one.

* **Deletion deficits.**  Deleting an edge with an endpoint of degree exactly `k`
  breaks the baseline at that endpoint; the exact degree identity
  `deg_{G−S}(v) + d_S(v) = deg_G(v)`.
* **The private-edge deletion.**  For two vertex sets `X_p, X_q`, deleting the
  edges of `G[X_q]` that are not edges of `G[X_p]` either deletes nothing or
  breaks the baseline at a tight endpoint of a deleted edge.
* **Two-edge switch.**  For edges `u₁v₁`, `u₂v₂` on four distinct vertices with
  `u₁ ≁ u₂` and `deg v₁, deg v₂ ≥ k + 1`, the object
  `G − {u₁v₁, u₂v₂} + u₁u₂` is smaller with minimum degree at least `k`; so
  `G − {u₁v₁, u₂v₂}` has a simple `u₁`–`u₂` path of length `ℓ` with `ℓ + 1`
  accepted.
* **Same-vertex switch.**  For `deg h ≥ k + 2` and non-adjacent neighbours
  `u₁ ≠ u₂` of `h`, `G − {hu₁, hu₂}` has a simple `u₁`–`u₂` path of length `ℓ`
  with `ℓ + 1` accepted; with return avoidance the path either avoids `h` (and
  `ℓ + 2` is not accepted) or splits at `h` into two returns neither of whose
  lengths plus one is accepted.

All results are vocabulary-free.
-/

namespace Hypostructure.Graph.EdgeSwitchPaths

open Hypostructure
open Hypostructure.Graph
open Classical

universe u

variable {object : FiniteObject.{u}}

/-- **Exact δ-failure of a spanning subgraph** (vocabulary-free).  If `H ≤ G`
drops the edge `uv`, the degree of `u` drops by at least one. -/
theorem ncard_neighborSet_lt {V : Type*} [Finite V] {G H : SimpleGraph V}
    (le : H ≤ G) {u v : V} (adj : G.Adj u v) (drop : ¬ H.Adj u v) :
    (H.neighborSet u).ncard + 1 ≤ (G.neighborSet u).ncard := by
  have sub : H.neighborSet u ⊆ G.neighborSet u \ {v} := by
    intro w hw
    refine ⟨le hw, ?_⟩
    rintro rfl
    exact drop hw
  have vmem : v ∈ G.neighborSet u := adj
  calc (H.neighborSet u).ncard + 1 ≤ (G.neighborSet u \ {v}).ncard + 1 :=
        Nat.add_le_add_right (Set.ncard_le_ncard sub (Set.toFinite _)) 1
    _ = (G.neighborSet u).ncard := Set.ncard_sdiff_singleton_add_one vmem (Set.toFinite _)

/-- The spanning subgraph of a finite object keeping only the edges of `H`. -/
noncomputable def spanning (object : FiniteObject.{u}) (H : SimpleGraph object.Vertex) :
    FiniteObject.{u} where
  Vertex := object.Vertex
  graph := H
  vertices := object.vertices
  decideAdj := Classical.decRel _

/-- **A spanning subgraph dropping an edge with a tight endpoint fails the
baseline at that endpoint** (vocabulary-free): the endpoint `w` with
`deg_G w = k` has degree `≤ k - 1` after the deletion. -/
theorem spanning_degree_le_of_tight {k : Nat} {H : SimpleGraph object.Vertex}
    (le : H ≤ object.graph) {u v : object.Vertex} (adj : object.graph.Adj u v)
    (drop : ¬ H.Adj u v) (tight : object.degree u = k) :
    (spanning object H).degree u + 1 ≤ k := by
  letI : Finite object.Vertex := by
    letI := object.vertices; infer_instance
  rw [FiniteObject.degree_eq_ncard_neighborSet, ← tight,
    FiniteObject.degree_eq_ncard_neighborSet]
  exact ncard_neighborSet_lt le adj drop

theorem spanning_not_baseline_of_tight {k : Nat} {H : SimpleGraph object.Vertex}
    (le : H ≤ object.graph) (tightEndpoint : ∀ d : object.graph.Dart,
      object.degree d.fst = k ∨ object.degree d.snd = k)
    {u v : object.Vertex} (adj : object.graph.Adj u v) (drop : ¬ H.Adj u v) :
    ∃ w, (w = u ∨ w = v) ∧ (spanning object H).degree w + 1 ≤ k ∧
      ¬ MinimumDegreeAtLeast k (spanning object H) := by
  have notBase : ∀ w, (spanning object H).degree w + 1 ≤ k →
      ¬ MinimumDegreeAtLeast k (spanning object H) := by
    intro w hw base
    have := (spanning object H).minDegree_le_degree w
    unfold MinimumDegreeAtLeast at base
    omega
  rcases tightEndpoint ⟨(u, v), adj⟩ with t | t
  · have := spanning_degree_le_of_tight le adj drop t
    exact ⟨u, Or.inl rfl, this, notBase u this⟩
  · have := spanning_degree_le_of_tight le adj.symm (fun h => drop h.symm) t
    exact ⟨v, Or.inr rfl, this, notBase v this⟩

/-- The swap object `G − (E(G[X_q]) \ E(G[X_p]))`: `G` with `ret_q`'s private
edges removed, i.e. `ret_q` glued back as `ret_p`. -/
def swapGraph (Xp Xq : Finset object.Vertex) : SimpleGraph object.Vertex :=
  object.graph.deleteEdges
    {e | ∃ x y, e = s(x, y) ∧ x ∈ Xq ∧ y ∈ Xq ∧ ¬ (x ∈ Xp ∧ y ∈ Xp)}

/-- **The private-edge deletion, exactly**: either `ret_q` has no private edge
(every edge of `G[X_q]` lies in `G[X_p]`, so the swap object is `G` itself and
is not smaller), or the swap object fails `δ ≥ k` at a tight endpoint
`w` of a private edge, with `deg(w) ≤ k − 1`. -/
theorem swap_exact {k : Nat}
    (tight : ∀ d : object.graph.Dart, object.degree d.fst = k ∨ object.degree d.snd = k)
    (Xp Xq : Finset object.Vertex) :
    (∀ x y, object.graph.Adj x y → x ∈ Xq → y ∈ Xq → x ∈ Xp ∧ y ∈ Xp) ∨
      ∃ x y, object.graph.Adj x y ∧ x ∈ Xq ∧ y ∈ Xq ∧ ¬ (x ∈ Xp ∧ y ∈ Xp) ∧
        ∃ w, (w = x ∨ w = y) ∧
          (spanning object (swapGraph Xp Xq)).degree w + 1 ≤ k ∧
          ¬ MinimumDegreeAtLeast k (spanning object (swapGraph Xp Xq)) := by
  by_cases none : ∀ x y, object.graph.Adj x y → x ∈ Xq → y ∈ Xq → x ∈ Xp ∧ y ∈ Xp
  · exact Or.inl none
  · right
    push Not at none
    obtain ⟨x, y, adj, hx, hy, priv⟩ := none
    have notP : ¬ (x ∈ Xp ∧ y ∈ Xp) := fun h => by
      by_cases hxp : x ∈ Xp
      · exact absurd (priv hxp) (not_not.2 h.2)
      · exact hxp h.1
    refine ⟨x, y, adj, hx, hy, notP, ?_⟩
    have le : swapGraph Xp Xq ≤ object.graph := object.graph.deleteEdges_le _
    have drop : ¬ (swapGraph Xp Xq).Adj x y := by
      intro h
      rw [swapGraph, SimpleGraph.deleteEdges_adj] at h
      exact h.2 ⟨x, y, rfl, hx, hy, notP⟩
    exact spanning_not_baseline_of_tight le tight adj drop


/-- The vertex type of a finite object is finite. -/
theorem finite_vertex : Finite object.Vertex := by letI := object.vertices; infer_instance

attribute [local instance] finite_vertex

theorem spanning_degree (H : SimpleGraph object.Vertex) (v : object.Vertex) :
    (spanning object H).degree v = (H.neighborSet v).ncard :=
  FiniteObject.degree_eq_ncard_neighborSet (spanning object H) v

theorem spanning_vertexCount (H : SimpleGraph object.Vertex) :
    (spanning object H).vertexCount = object.vertexCount := rfl

theorem edgeCount_eq_ncard (K : FiniteObject.{u}) :
    K.edgeCount = K.graph.edgeSet.ncard := by
  letI : FinEnum K.Vertex := K.vertices
  letI : DecidableRel K.graph.Adj := K.decideAdj
  unfold FiniteObject.edgeCount
  rw [Set.ncard_eq_toFinset_card']
  simp [SimpleGraph.edgeFinset]

/-- `d_S(v)`: the number of deleted edges at `v`. -/
noncomputable def deletedDegree (S : Set (Sym2 object.Vertex)) (v : object.Vertex) : Nat :=
  {w | object.graph.Adj v w ∧ s(v, w) ∈ S}.ncard

/-- **Exact degree identity** (vocabulary-free):
`deg_{G−S}(v) + d_S(v) = deg_G(v)`. -/
theorem deleteEdges_degree (S : Set (Sym2 object.Vertex)) (v : object.Vertex) :
    (spanning object (object.graph.deleteEdges S)).degree v + deletedDegree S v =
      object.degree v := by
  rw [spanning_degree, FiniteObject.degree_eq_ncard_neighborSet, deletedDegree]
  rw [← Set.ncard_union_eq]
  · congr 1
    ext w
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj, Set.mem_union,
      Set.mem_setOf_eq]
    tauto
  · rw [Set.disjoint_left]
    rintro w h1 ⟨-, h2⟩
    exact ((SimpleGraph.deleteEdges_adj ..).1 h1).2 h2

/-- **Exact deficit profile** at threshold `k`: `k − deg_{G−S}(v)` (truncated)
equals `d_S(v) − (deg_G(v) − k)` (truncated), for `deg_G v ≥ k`. -/
theorem deficit_formula {k : Nat} (S : Set (Sym2 object.Vertex)) (v : object.Vertex)
    (base : k ≤ object.degree v) :
    k - (spanning object (object.graph.deleteEdges S)).degree v =
      deletedDegree S v - (object.degree v - k) := by
  have := deleteEdges_degree S v
  omega

/-- At a tight vertex the deficit is exactly the number of deleted edges there. -/
theorem deficit_tight {k : Nat} (S : Set (Sym2 object.Vertex)) (v : object.Vertex)
    (tight : object.degree v = k) :
    k - (spanning object (object.graph.deleteEdges S)).degree v = deletedDegree S v := by
  have := deleteEdges_degree S v
  omega

/-- A vertex with no deleted edge loses nothing. -/
theorem deficit_zero_of_untouched {k : Nat} (S : Set (Sym2 object.Vertex)) (v : object.Vertex)
    (base : k ≤ object.degree v) (untouched : deletedDegree S v = 0) :
    k ≤ (spanning object (object.graph.deleteEdges S)).degree v := by
  have := deleteEdges_degree S v
  omega

/-! ## Minimality forces an accepted cycle through every smaller repair -/

/-- **Forced cycle of a smaller repair** (vocabulary-free): if G has no accepted
cycle and every smaller baseline object has one, then a smaller baseline repair
`(G − S) ⊔ F` has an accepted cycle using an edge of `F` absent from `G − S`. -/
theorem repair_forced_cycle {k : Nat} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (S : Set (Sym2 object.Vertex)) (F : SimpleGraph object.Vertex)
    (base : MinimumDegreeAtLeast k (spanning object (object.graph.deleteEdges S ⊔ F)))
    (smaller : (spanning object (object.graph.deleteEdges S ⊔ F)).LexicographicallySmaller object) :
    ∃ c : CycleCertificate (spanning object (object.graph.deleteEdges S ⊔ F)) L,
      ∃ e ∈ c.walk.edges, e ∈ F.edgeSet ∧ e ∉ (object.graph.deleteEdges S).edgeSet := by
  obtain ⟨c⟩ := minimal _ smaller base
  refine ⟨c, ?_⟩
  by_contra none
  push Not at none
  have hK : ∀ e ∈ c.walk.edges, e ∈ object.graph.edgeSet := by
    intro e he
    have h := c.walk.edges_subset_edgeSet he
    change e ∈ (object.graph.deleteEdges S ⊔ F).edgeSet at h
    rw [SimpleGraph.edgeSet_sup] at h
    rcases h with h | h
    · exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le S) h
    · exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le S) (none e he h)
  exact avoids ⟨⟨c.vertex, c.walk.transfer object.graph hK, c.isCycle.transfer hK, by
    convert c.length_ok using 1; exact SimpleGraph.Walk.length_transfer _ _⟩⟩


/-- **Two-edge switch at a minimal object** (vocabulary-free).  Let `u₁v₁`,
`u₂v₂` be edges with `u₁,v₁,u₂,v₂` distinct, `u₁ ≁ u₂`, and `v₁, v₂` of degree
`≥ k+1`.  Then `G − {u₁v₁,u₂v₂} + u₁u₂` keeps `δ ≥ k` and has one edge fewer,
so minimality forces a simple `u₁`–`u₂` path in `G − {u₁v₁,u₂v₂}` of length
`ℓ` with `ℓ + 1` accepted. -/
theorem twoSwitch_forced_path {k : Nat} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (baseline : MinimumDegreeAtLeast k object)
    {u₁ v₁ u₂ v₂ : object.Vertex}
    (a₁ : object.graph.Adj u₁ v₁) (a₂ : object.graph.Adj u₂ v₂)
    (h12 : u₁ ≠ u₂) (h1v2 : u₁ ≠ v₂) (hv1u2 : v₁ ≠ u₂) (hvv : v₁ ≠ v₂)
    (nonadj : ¬ object.graph.Adj u₁ u₂)
    (slack₁ : k + 1 ≤ object.degree v₁) (slack₂ : k + 1 ≤ object.degree v₂) :
    ∃ p : (object.graph.deleteEdges {s(u₁, v₁), s(u₂, v₂)}).Walk u₁ u₂,
      p.IsPath ∧ L (p.length + 1) := by
  set S : Set (Sym2 object.Vertex) := {s(u₁, v₁), s(u₂, v₂)} with hS
  set F := SimpleGraph.edge u₁ u₂ with hF
  have hu1v1 : u₁ ≠ v₁ := a₁.ne
  have hu2v2 : u₂ ≠ v₂ := a₂.ne
  have memS : ∀ {w x}, s(w, x) ∈ S →
      (w = u₁ ∧ x = v₁) ∨ (w = v₁ ∧ x = u₁) ∨ (w = u₂ ∧ x = v₂) ∨ (w = v₂ ∧ x = u₂) := by
    intro w x h
    rcases h with h | h
    · rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
    · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 h) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  have baseDeg : ∀ w, k ≤ object.degree w := fun w =>
    baseline.trans (object.minDegree_le_degree w)
  -- degree of every vertex after the switch
  have degH : ∀ w, k ≤ ((object.graph.deleteEdges S ⊔ F).neighborSet w).ncard := by
    intro w
    have split := deleteEdges_degree (object := object) S w
    rw [spanning_degree] at split
    have mono : ((object.graph.deleteEdges S).neighborSet w).ncard ≤
        ((object.graph.deleteEdges S ⊔ F).neighborSet w).ncard :=
      Set.ncard_le_ncard (fun x hx => Or.inl hx) (Set.toFinite _)
    by_cases wu1 : w = u₁
    · subst wu1
      have dle : deletedDegree S w ≤ 1 := by
        unfold deletedDegree
        calc _ ≤ ({v₁} : Set object.Vertex).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro x ⟨-, hx⟩
              rcases memS hx with h | h | h | h
              · exact h.2
              · exact absurd h.1 hu1v1
              · exact absurd h.1 h12
              · exact absurd h.1 h1v2
          _ = 1 := Set.ncard_singleton _
      have sub : (object.graph.deleteEdges S).neighborSet w ∪ {u₂} ⊆
          (object.graph.deleteEdges S ⊔ F).neighborSet w := by
        rintro x (hx | hx)
        · exact Or.inl hx
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          right
          rw [hF, SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨rfl, rfl⟩, h12⟩
      have disj : u₂ ∉ (object.graph.deleteEdges S).neighborSet w := fun h => nonadj h.1
      have card := Set.ncard_le_ncard sub (Set.toFinite _)
      rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 disj) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton] at card
      have := baseDeg w
      omega
    by_cases wu2 : w = u₂
    · subst wu2
      have dle : deletedDegree S w ≤ 1 := by
        unfold deletedDegree
        calc _ ≤ ({v₂} : Set object.Vertex).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro x ⟨-, hx⟩
              rcases memS hx with h | h | h | h
              · exact absurd h.1.symm h12
              · exact absurd h.1.symm hv1u2
              · exact h.2
              · exact absurd h.1 hu2v2
          _ = 1 := Set.ncard_singleton _
      have sub : (object.graph.deleteEdges S).neighborSet w ∪ {u₁} ⊆
          (object.graph.deleteEdges S ⊔ F).neighborSet w := by
        rintro x (hx | hx)
        · exact Or.inl hx
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          right
          rw [hF, SimpleGraph.edge_adj]
          exact ⟨Or.inr ⟨rfl, rfl⟩, h12.symm⟩
      have disj : u₁ ∉ (object.graph.deleteEdges S).neighborSet w :=
        fun h => nonadj h.1.symm
      have card := Set.ncard_le_ncard sub (Set.toFinite _)
      rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 disj) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton] at card
      have := baseDeg w
      omega
    by_cases wv1 : w = v₁
    · subst wv1
      have dle : deletedDegree S w ≤ 1 := by
        unfold deletedDegree
        calc _ ≤ ({u₁} : Set object.Vertex).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro x ⟨-, hx⟩
              rcases memS hx with h | h | h | h
              · exact absurd h.1 wu1
              · exact h.2
              · exact absurd h.1 wu2
              · exact absurd h.1 hvv
          _ = 1 := Set.ncard_singleton _
      omega
    by_cases wv2 : w = v₂
    · subst wv2
      have dle : deletedDegree S w ≤ 1 := by
        unfold deletedDegree
        calc _ ≤ ({u₂} : Set object.Vertex).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro x ⟨-, hx⟩
              rcases memS hx with h | h | h | h
              · exact absurd h.1 wu1
              · exact absurd h.1 wv1
              · exact absurd h.1 wu2
              · exact h.2
          _ = 1 := Set.ncard_singleton _
      omega
    · have dz : deletedDegree S w = 0 := by
        unfold deletedDegree
        rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hx
        rcases memS hx with h | h | h | h
        · exact wu1 h.1
        · exact wv1 h.1
        · exact wu2 h.1
        · exact wv2 h.1
      have := baseDeg w
      omega
  have base : MinimumDegreeAtLeast k (spanning object (object.graph.deleteEdges S ⊔ F)) := by
    unfold MinimumDegreeAtLeast
    haveI : Nonempty (spanning object (object.graph.deleteEdges S ⊔ F)).Vertex := ⟨u₁⟩
    apply FiniteObject.le_minDegree_of_forall_le_degree
    intro w
    rw [spanning_degree]
    exact degH w
  have smaller : (spanning object (object.graph.deleteEdges S ⊔ F)).LexicographicallySmaller
      object := by
    rw [FiniteObject.lexicographicallySmaller_iff]
    right
    refine ⟨rfl, ?_⟩
    rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
    change ((object.graph.deleteEdges S ⊔ F).edgeSet).ncard < _
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, hF,
      SimpleGraph.edgeSet_edge]
    have Ssub : S ⊆ object.graph.edgeSet := by
      rintro e (h | h)
      · rw [h]; exact a₁
      · rw [Set.mem_singleton_iff.1 h]; exact a₂
    have Scard : S.ncard = 2 := by
      rw [hS, Set.ncard_pair]
      intro h
      rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h12 h1
      · exact h1v2 h1
    have d := Set.ncard_sdiff Ssub (Set.toFinite _)
    have u := Set.ncard_union_le (object.graph.edgeSet \ S) ({s(u₁, u₂)} \ Sym2.diagSet)
    have one : ({s(u₁, u₂)} \ Sym2.diagSet : Set (Sym2 object.Vertex)).ncard ≤ 1 :=
      (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)).trans (Set.ncard_singleton _).le
    have le := Set.ncard_le_ncard Ssub (Set.toFinite _)
    omega
  obtain ⟨c, e, he, eF, eNot⟩ := repair_forced_cycle avoids minimal S F base smaller
  have eEq : e = s(u₁, u₂) := by
    rw [hF, SimpleGraph.edgeSet_edge] at eF
    exact Set.mem_singleton_iff.1 eF.1
  subst eEq
  obtain ⟨w, wPath, wFresh, wLen⟩ := SingleEdgeContext.cycle_through_edge c.walk c.isCycle he
  have hw : ∀ e ∈ w.edges, e ∈ (object.graph.deleteEdges S).edgeSet := by
    intro e' he'
    have h := w.edges_subset_edgeSet he'
    change e' ∈ (object.graph.deleteEdges S ⊔ F).edgeSet at h
    rw [SimpleGraph.edgeSet_sup] at h
    rcases h with h | h
    · exact h
    · rw [hF, SimpleGraph.edgeSet_edge] at h
      exact absurd (Set.mem_singleton_iff.1 h.1 ▸ he') wFresh
  refine ⟨w.transfer _ hw, wPath.transfer hw, ?_⟩
  convert c.length_ok using 1
  rw [← wLen]
  congr 1
  exact SimpleGraph.Walk.length_transfer _ _

/-- **Same-vertex switch at a minimal object** (vocabulary-free).  If
`deg h ≥ k + 2` and `u₁ ≠ u₂` are non-adjacent neighbours of `h`, then
`G − {hu₁, hu₂} + u₁u₂` keeps `δ ≥ k` with one edge fewer, so minimality forces
a simple `u₁`–`u₂` path in `G − {hu₁, hu₂}` of length `ℓ` with `ℓ + 1`
accepted. -/
theorem sameVertexSwitch_forced_path {k : Nat} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (baseline : MinimumDegreeAtLeast k object)
    {h u₁ u₂ : object.Vertex}
    (a₁ : object.graph.Adj h u₁) (a₂ : object.graph.Adj h u₂)
    (h12 : u₁ ≠ u₂) (nonadj : ¬ object.graph.Adj u₁ u₂)
    (heavy : k + 2 ≤ object.degree h) :
    ∃ p : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ u₂,
      p.IsPath ∧ L (p.length + 1) := by
  set S : Set (Sym2 object.Vertex) := {s(h, u₁), s(h, u₂)} with hS
  set F := SimpleGraph.edge u₁ u₂ with hF
  have hu1 : h ≠ u₁ := a₁.ne
  have hu2 : h ≠ u₂ := a₂.ne
  have memS : ∀ {w x}, s(w, x) ∈ S →
      (w = h ∧ x = u₁) ∨ (w = u₁ ∧ x = h) ∨ (w = h ∧ x = u₂) ∨ (w = u₂ ∧ x = h) := by
    intro w x hm
    rcases hm with hm | hm
    · rcases Sym2.eq_iff.1 hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
    · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hm) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  have baseDeg : ∀ w, k ≤ object.degree w := fun w =>
    baseline.trans (object.minDegree_le_degree w)
  have gain : ∀ w x : object.Vertex, (w = u₁ ∧ x = u₂ ∨ w = u₂ ∧ x = u₁) →
      k ≤ ((object.graph.deleteEdges S ⊔ F).neighborSet w).ncard := by
    intro w x hwx
    have split := deleteEdges_degree (object := object) S w
    rw [spanning_degree] at split
    have sub1 : {y | object.graph.Adj w y ∧ s(w, y) ∈ S} ⊆ ({h} : Set object.Vertex) := by
      rintro y ⟨-, hy⟩
      rw [Set.mem_singleton_iff]
      rcases hwx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases memS hy with e | e | e | e
        · exact absurd e.1.symm hu1
        · exact e.2
        · exact absurd e.1.symm hu1
        · exact absurd e.1 h12
      · rcases memS hy with e | e | e | e
        · exact absurd e.1.symm hu2
        · exact absurd e.1 h12.symm
        · exact absurd e.1.symm hu2
        · exact e.2
    have dle : deletedDegree S w ≤ 1 :=
      (Set.ncard_le_ncard sub1 (Set.toFinite _)).trans (Set.ncard_singleton _).le
    have sub : (object.graph.deleteEdges S).neighborSet w ∪ {x} ⊆
        (object.graph.deleteEdges S ⊔ F).neighborSet w := by
      rintro y (hy | hy)
      · exact Or.inl hy
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        right
        rw [hF, SimpleGraph.edge_adj]
        rcases hwx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl ⟨rfl, rfl⟩, h12⟩
        · exact ⟨Or.inr ⟨rfl, rfl⟩, h12.symm⟩
    have disj : x ∉ (object.graph.deleteEdges S).neighborSet w := by
      intro hx
      rcases hwx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact nonadj hx.1
      · exact nonadj hx.1.symm
    have card := Set.ncard_le_ncard sub (Set.toFinite _)
    rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 disj) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_singleton] at card
    have := baseDeg w
    omega
  have degH : ∀ w, k ≤ ((object.graph.deleteEdges S ⊔ F).neighborSet w).ncard := by
    intro w
    have split := deleteEdges_degree (object := object) S w
    rw [spanning_degree] at split
    have mono : ((object.graph.deleteEdges S).neighborSet w).ncard ≤
        ((object.graph.deleteEdges S ⊔ F).neighborSet w).ncard :=
      Set.ncard_le_ncard (fun x hx => Or.inl hx) (Set.toFinite _)
    by_cases w1 : w = u₁
    · exact gain w u₂ (Or.inl ⟨w1, rfl⟩)
    by_cases w2 : w = u₂
    · exact gain w u₁ (Or.inr ⟨w2, rfl⟩)
    by_cases wh : w = h
    · subst wh
      have dle : deletedDegree S w ≤ 2 := by
        unfold deletedDegree
        calc _ ≤ ({u₁, u₂} : Set object.Vertex).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro y ⟨-, hy⟩
              rcases memS hy with e | e | e | e
              · exact Or.inl e.2
              · exact absurd e.1 w1
              · exact Or.inr e.2
              · exact absurd e.1 w2
          _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
      omega
    · have dz : deletedDegree S w = 0 := by
        unfold deletedDegree
        rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hx
        rcases memS hx with e | e | e | e
        · exact wh e.1
        · exact w1 e.1
        · exact wh e.1
        · exact w2 e.1
      have := baseDeg w
      omega
  have base : MinimumDegreeAtLeast k (spanning object (object.graph.deleteEdges S ⊔ F)) := by
    unfold MinimumDegreeAtLeast
    haveI : Nonempty (spanning object (object.graph.deleteEdges S ⊔ F)).Vertex := ⟨h⟩
    apply FiniteObject.le_minDegree_of_forall_le_degree
    intro w
    rw [spanning_degree]
    exact degH w
  have smaller : (spanning object (object.graph.deleteEdges S ⊔ F)).LexicographicallySmaller
      object := by
    rw [FiniteObject.lexicographicallySmaller_iff]
    right
    refine ⟨rfl, ?_⟩
    rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
    change ((object.graph.deleteEdges S ⊔ F).edgeSet).ncard < _
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, hF,
      SimpleGraph.edgeSet_edge]
    have Ssub : S ⊆ object.graph.edgeSet := by
      rintro e (he | he)
      · rw [he]; exact a₁
      · rw [Set.mem_singleton_iff.1 he]; exact a₂
    have Scard : S.ncard = 2 := by
      rw [hS, Set.ncard_pair]
      intro he
      rcases Sym2.eq_iff.1 he with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h12 h1
      · exact hu2 h1
    have d := Set.ncard_sdiff Ssub (Set.toFinite _)
    have uu := Set.ncard_union_le (object.graph.edgeSet \ S) ({s(u₁, u₂)} \ Sym2.diagSet)
    have one : ({s(u₁, u₂)} \ Sym2.diagSet : Set (Sym2 object.Vertex)).ncard ≤ 1 :=
      (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)).trans (Set.ncard_singleton _).le
    have le := Set.ncard_le_ncard Ssub (Set.toFinite _)
    omega
  obtain ⟨c, e, he, eF, eNot⟩ := repair_forced_cycle avoids minimal S F base smaller
  have eEq : e = s(u₁, u₂) := by
    rw [hF, SimpleGraph.edgeSet_edge] at eF
    exact Set.mem_singleton_iff.1 eF.1
  subst eEq
  obtain ⟨w, wPath, wFresh, wLen⟩ := SingleEdgeContext.cycle_through_edge c.walk c.isCycle he
  have hw : ∀ e ∈ w.edges, e ∈ (object.graph.deleteEdges S).edgeSet := by
    intro e' he'
    have hh := w.edges_subset_edgeSet he'
    change e' ∈ (object.graph.deleteEdges S ⊔ F).edgeSet at hh
    rw [SimpleGraph.edgeSet_sup] at hh
    rcases hh with hh | hh
    · exact hh
    · rw [hF, SimpleGraph.edgeSet_edge] at hh
      exact absurd (Set.mem_singleton_iff.1 hh.1 ▸ he') wFresh
  refine ⟨w.transfer _ hw, wPath.transfer hw, ?_⟩
  convert c.length_ok using 1
  rw [← wLen]
  congr 1
  exact SimpleGraph.Walk.length_transfer _ _


/-- A path in `G − {hu₁,hu₂}` from `u₁` to `h` is a return of `hu₁`. -/
theorem return_of_deleted {L : Nat → Prop}
    (returnAvoidance : ∀ dart : object.graph.Dart,
      Disjoint (returnLengthSet object dart) (shiftedAcceptedSet L))
    {h u₁ u₂ : object.Vertex} (a₁ : object.graph.Adj h u₁)
    (q : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ h) (qp : q.IsPath) :
    ¬ L (q.length + 1) := by
  intro ok
  let d : object.graph.Dart := ⟨(h, u₁), a₁⟩
  have le : object.graph.deleteEdges {s(h, u₁), s(h, u₂)} ≤
      object.graph.deleteEdges {d.edge} :=
    SimpleGraph.deleteEdges_anti (by
      intro e he
      rw [Set.mem_singleton_iff] at he
      exact Or.inl he)
  have mem : q.length ∈ returnLengthSet object d :=
    ⟨q.mapLe le, qp.mapLe le, SimpleGraph.Walk.length_map _ _⟩
  exact Set.disjoint_left.1 (returnAvoidance d) mem ok

/-- **Dichotomy for the same-vertex forced path** (vocabulary-free).  Let `p` be
a simple `u₁`–`u₂` path in `G − {hu₁,hu₂}` on a target-avoiding object with
return avoidance.  Either `p` avoids `h`, and then `p + u₂h + hu₁` is a cycle
of `G` of length `|p| + 2`, which is not accepted; or `p` passes through `h`,
and splits into two returns of `hu₁` and `hu₂` with lengths `ℓ₁ + ℓ₂ = |p|`,
neither `ℓᵢ + 1` accepted. -/
theorem sameVertex_path_dichotomy {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (returnAvoidance : ∀ dart : object.graph.Dart,
      Disjoint (returnLengthSet object dart) (shiftedAcceptedSet L))
    {h u₁ u₂ : object.Vertex}
    (a₁ : object.graph.Adj h u₁) (a₂ : object.graph.Adj h u₂) (h12 : u₁ ≠ u₂)
    (p : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ u₂) (pp : p.IsPath) :
    (h ∉ p.support ∧ ¬ L (p.length + 2)) ∨
      (∃ ℓ₁ ℓ₂, ℓ₁ + ℓ₂ = p.length ∧ ¬ L (ℓ₁ + 1) ∧ ¬ L (ℓ₂ + 1)) := by
  by_cases hin : h ∈ p.support
  · right
    have spec := SimpleGraph.Walk.take_spec p hin
    refine ⟨(p.takeUntil h hin).length, (p.dropUntil h hin).length, ?_, ?_, ?_⟩
    · have := congrArg SimpleGraph.Walk.length spec
      rw [SimpleGraph.Walk.length_append] at this
      exact this
    · exact return_of_deleted returnAvoidance a₁ _ (pp.takeUntil hin)
    · have r := return_of_deleted (u₂ := u₁) returnAvoidance a₂
        ((p.dropUntil h hin).reverse.mapLe (SimpleGraph.deleteEdges_anti (by
          intro e he
          rcases he with he | he
          · exact Or.inr he
          · exact Or.inl (Set.mem_singleton_iff.1 he))))
        ((pp.dropUntil hin).reverse.mapLe _)
      have hl : ((p.dropUntil h hin).reverse.mapLe (SimpleGraph.deleteEdges_anti (G := object.graph)
          (s₁ := {s(h, u₂), s(h, u₁)}) (s₂ := {s(h, u₁), s(h, u₂)}) (by
            intro e he
            rcases he with he | he
            · exact Or.inr he
            · exact Or.inl (Set.mem_singleton_iff.1 he)))).length =
          (p.dropUntil h hin).length :=
        (SimpleGraph.Walk.length_map _ _).trans (SimpleGraph.Walk.length_reverse _)
      rwa [hl] at r
  · left
    refine ⟨hin, ?_⟩
    intro ok
    have le : object.graph.deleteEdges {s(h, u₁), s(h, u₂)} ≤ object.graph :=
      SimpleGraph.deleteEdges_le _
    let q := p.mapLe le
    have qp : q.IsPath := pp.mapLe le
    have qsupp : h ∉ q.support := by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hin
    have fresh : s(h, u₁) ∉ q.edges := by
      intro m
      have : s(h, u₁) ∈ (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).edgeSet := by
        have m' : s(h, u₁) ∈ p.edges := by
          rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at m
        exact p.edges_subset_edgeSet m'
      rw [SimpleGraph.edgeSet_deleteEdges] at this
      exact this.2 (Or.inl rfl)
    let body := q.concat a₂.symm
    have bodyPath : body.IsPath := (SimpleGraph.Walk.concat_isPath_iff _).2 ⟨qp, qsupp⟩
    have bodyFresh : s(h, u₁) ∉ body.edges := by
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, not_or]
      refine ⟨fresh, ?_⟩
      rw [List.mem_singleton]
      intro e
      rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact a₂.ne h1
      · exact h12 h2
    apply avoids
    refine ⟨⟨h, .cons a₁ body,
      (SimpleGraph.Walk.cons_isCycle_iff body a₁).2 ⟨bodyPath, bodyFresh⟩, ?_⟩⟩
    convert ok using 1
    simp only [body, q, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
    rw [show (SimpleGraph.Walk.mapLe le p).length = p.length from
      SimpleGraph.Walk.length_map _ _]

/-- A vertex `c` of degree `k` and a vertex `h` of degree `≥ k + 1`: some
neighbour `u` of `h` is neither `c` nor adjacent to `c`. -/
theorem exists_nonadj_nbr {k : Nat} {c h : object.Vertex}
    (dc : object.degree c = k) (dh : k + 1 ≤ object.degree h) :
    ∃ u, object.graph.Adj h u ∧ u ≠ c ∧ ¬ object.graph.Adj c u := by
  by_contra none
  push Not at none
  rw [FiniteObject.degree_eq_ncard_neighborSet] at dc dh
  by_cases ch : object.graph.Adj h c
  · have sub : object.graph.neighborSet h ⊆ insert c (object.graph.neighborSet c \ {h}) := by
      intro u hu
      by_cases uc : u = c
      · exact Or.inl uc
      · exact Or.inr ⟨none u hu uc, fun e => object.graph.irrefl
          (show object.graph.Adj h h from (Set.mem_singleton_iff.1 e) ▸ hu)⟩
    have c1 := (Set.ncard_le_ncard sub (Set.toFinite _)).trans (Set.ncard_insert_le _ _)
    have c2 := Set.ncard_sdiff_singleton_add_one
      (show h ∈ object.graph.neighborSet c from ch.symm) (Set.toFinite _)
    omega
  · have sub : object.graph.neighborSet h ⊆ object.graph.neighborSet c := by
      intro u hu
      have uc : u ≠ c := fun e => ch (e ▸ hu)
      exact none u hu uc
    have := Set.ncard_le_ncard sub (Set.toFinite _)
    omega

end Hypostructure.Graph.EdgeSwitchPaths
