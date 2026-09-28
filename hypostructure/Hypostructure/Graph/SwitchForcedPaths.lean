import Hypostructure.Graph.ReadingSpectrum

/-!
# Forced paths and cycles of edge switches, deletions and vertex splits

On a target-avoiding object `G` all of whose lexicographically smaller
baseline objects carry a target cycle:

* deleting an edge set `S` and repairing with `F` so that the baseline holds
  again forces an accepted cycle through the repair edges
  (`deleteEdges_degree`, `deficit_*`, `repair_cover`, `repair_forced_cycle`),
  and the deficit accounting of a whole swap (`SwapAccounting`:
  `allTight_repair_not_fewer`, ...);
* the two-edge switch `G − {u₁v₁, u₂v₂} + u₁u₂` (`twoSwitch_forced_path`) and
  the same-vertex switch `G − {hu₁, hu₂} + u₁u₂` (`sameVertexSwitch_forced_path`,
  with the return dichotomy `sameVertex_path_dichotomy`) force simple paths
  with accepted closing lengths;
* the vertex split `(G − h) ⊔ M` (`splitObj`, `split_forced_cycle`) at a
  high centre with a matching neighbourhood (`highCentre_cover`,
  `highCentre_split_forced`) forces an accepted cycle through a new pair;
* at the dyadic target two equal-length `2^j − 1` paths into two neighbours of
  a vertex form a forbidden star (`star_forbidden`), which constrains the
  cross-vertex switch family (`cross_switch_family`).

Every statement is about an arbitrary finite object; nothing here knows a
presentation, a ledger, or a manuscript.
-/

universe u v


/-! ## Edge deletion, deficits and repairs -/

namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Classical


variable {object : FiniteObject.{u}}

/-- The spanning object carrying a graph on the object's vertices. -/
noncomputable def spanning (object : FiniteObject.{u}) (H : SimpleGraph object.Vertex) :
    FiniteObject.{u} where
  Vertex := object.Vertex
  graph := H
  vertices := object.vertices
  decideAdj := Classical.decRel _

scoped instance : Finite object.Vertex := by letI := object.vertices; infer_instance

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

/-! ## E1: equal readings force equal supports -/

/-- **Equal readings ⇒ equal supports** (vocabulary-free).  If `G[X]` and `G[Y]`
have the same edges and every vertex of each set has a neighbour in it, then
`X = Y`. -/
theorem supports_eq_of_same_edges {X Y : Finset object.Vertex}
    (same : ∀ x y, object.graph.Adj x y → (x ∈ X ∧ y ∈ X ↔ x ∈ Y ∧ y ∈ Y))
    (nbrX : ∀ v ∈ X, ∃ w ∈ X, object.graph.Adj v w)
    (nbrY : ∀ v ∈ Y, ∃ w ∈ Y, object.graph.Adj v w) : X = Y := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, adj⟩ := nbrX v hv
    exact ((same v w adj).1 ⟨hv, hw⟩).1
  · intro hv
    obtain ⟨w, hw, adj⟩ := nbrY v hv
    exact ((same v w adj).2 ⟨hv, hw⟩).1

/-- With equal supports the canonical carrier is the support itself. -/
theorem select_self {X Z : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object X)
    (selected : CanonicalSupport.select? object X = some Z) : Z = X := by
  have cand := CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates selected)
  have le := CanonicalSupport.select?_card_le selected
    (CanonicalSupport.mem_candidates_iff.2 ⟨subset_refl X, connected⟩)
  exact (Finset.eq_of_subset_of_card_le cand.1 le).symm

/-! ## E2: exact deficit of an edge deletion -/

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

/-! ## E3: every repair covers the deficient vertices -/

/-- **Repair cover** (vocabulary-free): if `(G − S) ⊔ F` has minimum degree at
least `k`, every vertex deficient in `G − S` gains at least
`k − deg_{G−S}(v)` neighbours from `F`. -/
theorem repair_cover {k : Nat} (S : Set (Sym2 object.Vertex)) (F : SimpleGraph object.Vertex)
    (base : MinimumDegreeAtLeast k (spanning object (object.graph.deleteEdges S ⊔ F)))
    (v : object.Vertex) :
    k ≤ (spanning object (object.graph.deleteEdges S)).degree v + (F.neighborSet v).ncard := by
  have hv := (spanning object (object.graph.deleteEdges S ⊔ F)).minDegree_le_degree v
  unfold MinimumDegreeAtLeast at base
  rw [spanning_degree] at hv ⊢
  have sub : (object.graph.deleteEdges S ⊔ F).neighborSet v ⊆
      (object.graph.deleteEdges S).neighborSet v ∪ F.neighborSet v := by
    intro w hw
    rcases hw with h | h
    · exact Or.inl h
    · exact Or.inr h
  have := (Set.ncard_le_ncard sub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  omega

/-! ## E4: minimality forces an accepted cycle through every smaller repair -/

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

end Hypostructure.Graph.SwitchForcedPaths


namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Classical

variable {object : FiniteObject.{u}}

/-! ## The canonical two-edge switch and the path it forces -/

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
    have d := Set.ncard_diff Ssub (Set.toFinite _)
    have u := Set.ncard_union_le (object.graph.edgeSet \ S) ({s(u₁, u₂)} \ Sym2.diagSet)
    have one : ({s(u₁, u₂)} \ Sym2.diagSet : Set (Sym2 object.Vertex)).ncard ≤ 1 :=
      (Set.ncard_le_ncard Set.diff_subset (Set.toFinite _)).trans (Set.ncard_singleton _).le
    have le := Set.ncard_le_ncard Ssub (Set.toFinite _)
    omega
  obtain ⟨c, e, he, eF, eNot⟩ := repair_forced_cycle avoids minimal S F base smaller
  have eEq : e = s(u₁, u₂) := by
    rw [hF, SimpleGraph.edgeSet_edge] at eF
    exact Set.mem_singleton_iff.1 eF.1
  subst eEq
  obtain ⟨w, wPath, wFresh, wLen⟩ := Hypostructure.Graph.ReadingSpectrum.EdgeContext.cycle_through_edge c.walk c.isCycle he
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

end Hypostructure.Graph.SwitchForcedPaths


namespace Hypostructure.Graph.SwitchForcedPaths.SwapAccounting
open Hypostructure Hypostructure.Graph Classical

variable {V : Type u} [Fintype V]

/-- `ncard` degree. -/
noncomputable def dg (H : SimpleGraph V) (v : V) : Nat := (H.neighborSet v).ncard

theorem dg_eq_degree (H : SimpleGraph V) (v : V) : dg H v = H.degree v := by
  unfold dg
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Set.ncard_eq_toFinset_card']
  simp [SimpleGraph.neighborFinset]

/-- Handshake in `ncard` form. -/
theorem sum_dg (H : SimpleGraph V) : ∑ v, dg H v = 2 * H.edgeSet.ncard := by
  simp_rw [dg_eq_degree]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, Set.ncard_eq_toFinset_card']
  simp [SimpleGraph.edgeFinset]


variable {G P F : SimpleGraph V} {k : Nat}

/-- Degree split: `deg_G = deg_{G∖P} + deg_P` for `P ≤ G`. -/
theorem dg_split (le : P ≤ G) (v : V) : dg G v = dg (G \ P) v + dg P v := by
  unfold dg
  rw [← Set.ncard_union_eq]
  · congr 1
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_union, SimpleGraph.sdiff_adj]
    constructor
    · intro h; by_cases hp : P.Adj v w
      · exact Or.inr hp
      · exact Or.inl ⟨h, hp⟩
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact le h
  · rw [Set.disjoint_left]
    rintro w ⟨-, h1⟩ h2
    exact h1 h2

/-- The deficit of `v` after deleting `P`, at threshold `k`. -/
noncomputable def deficit (k : Nat) (G P : SimpleGraph V) (v : V) : Nat := k - dg (G \ P) v

/-- The total deficit `D`. -/
noncomputable def totalDeficit (k : Nat) (G P : SimpleGraph V) : Nat := ∑ v, deficit k G P v

theorem deficit_le (le : P ≤ G) (base : ∀ v, k ≤ dg G v) (v : V) :
    deficit k G P v ≤ dg P v := by
  unfold deficit; have := dg_split le v; have := base v; omega

/-- **Upper bound** `D ≤ 2|P|`. -/
theorem totalDeficit_le (le : P ≤ G) (base : ∀ v, k ≤ dg G v) :
    totalDeficit k G P ≤ 2 * P.edgeSet.ncard := by
  rw [← sum_dg]
  exact Finset.sum_le_sum fun v _ => deficit_le le base v

/-- Darts of `P` leaving a vertex set count its degree sum. -/
theorem edges_le_sum_dg (T : Finset V) (cover : ∀ x y, P.Adj x y → x ∈ T ∨ y ∈ T) :
    P.edgeSet.ncard ≤ ∑ v ∈ T, dg P v := by
  classical
  have fib : ∑ v ∈ T, dg P v =
      (Finset.univ.filter fun d : P.Dart => d.fst ∈ T).card := by
    have H := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun d : P.Dart => d.fst ∈ T) (t := T)
      (f := fun d : P.Dart => d.fst) (fun d hd => (Finset.mem_filter.1 hd).2)
    rw [H]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [dg_eq_degree, ← SimpleGraph.dart_fst_fiber_card_eq_degree]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> simp_all
  rw [fib, Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card_of_surjOn (fun d : P.Dart => d.edge)
  intro e he
  have he' : e ∈ P.edgeSet := by simpa using he
  induction e using Sym2.ind with
  | h x y =>
    have adj : P.Adj x y := he'
    rcases cover x y adj with hx | hy
    · exact ⟨⟨(x, y), adj⟩, by simpa using hx, rfl⟩
    · exact ⟨⟨(y, x), adj.symm⟩, by simpa using hy, Sym2.eq_swap⟩

/-- **Lower bound** `|P| ≤ D` when every edge of `P` has an endpoint at which
`G` is tight. -/
theorem le_totalDeficit (le : P ≤ G) (base : ∀ v, k ≤ dg G v)
    (tight : ∀ x y, P.Adj x y → dg G x = k ∨ dg G y = k) :
    P.edgeSet.ncard ≤ totalDeficit k G P := by
  classical
  let T := Finset.univ.filter fun v => dg G v = k
  have h1 := edges_le_sum_dg (P := P) T (fun x y h => by
    rcases tight x y h with hx | hy
    · exact Or.inl (by simp [T, hx])
    · exact Or.inr (by simp [T, hy]))
  refine h1.trans ?_
  unfold totalDeficit
  calc ∑ v ∈ T, dg P v = ∑ v ∈ T, deficit k G P v := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have := dg_split le v
        have hv' : dg G v = k := (Finset.mem_filter.1 hv).2
        unfold deficit; omega
    _ ≤ ∑ v, deficit k G P v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **Repair bound** `D ≤ 2|F|` for every repair `(G∖P) ⊔ F` with `δ ≥ k`. -/
theorem totalDeficit_le_repair (base' : ∀ v, k ≤ dg ((G \ P) ⊔ F) v) :
    totalDeficit k G P ≤ 2 * F.edgeSet.ncard := by
  rw [← sum_dg]
  refine Finset.sum_le_sum fun v _ => ?_
  have sub : ((G \ P) ⊔ F).neighborSet v ⊆ (G \ P).neighborSet v ∪ F.neighborSet v :=
    fun w hw => hw
  have := (Set.ncard_le_ncard sub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have := base' v
  unfold deficit dg at *
  omega

/-- **All-tight case**: if both endpoints of every edge of `P` are tight,
then `D = 2|P|`. -/
theorem totalDeficit_allTight (le : P ≤ G) (base : ∀ v, k ≤ dg G v)
    (tight : ∀ x y, P.Adj x y → dg G x = k ∧ dg G y = k) :
    totalDeficit k G P = 2 * P.edgeSet.ncard := by
  rw [← sum_dg]
  refine Finset.sum_congr rfl fun v _ => ?_
  have split := dg_split le v
  have := base v
  by_cases h : dg P v = 0
  · unfold deficit; omega
  · obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).1 (Nat.pos_of_ne_zero h)
    have := (tight v w hw).1
    unfold deficit; omega

/-- **Closed obstruction, all-tight case** (vocabulary-free): no repair with new
edges `F` (disjoint from `G ∖ P`) restores `δ ≥ k` with fewer edges than `G`. -/
theorem allTight_repair_not_fewer (le : P ≤ G) (base : ∀ v, k ≤ dg G v)
    (tight : ∀ x y, P.Adj x y → dg G x = k ∧ dg G y = k)
    (base' : ∀ v, k ≤ dg ((G \ P) ⊔ F) v)
    (fresh : ∀ x y, F.Adj x y → ¬ (G \ P).Adj x y) :
    G.edgeSet.ncard ≤ ((G \ P) ⊔ F).edgeSet.ncard := by
  have hD := totalDeficit_le_repair base'
  rw [totalDeficit_allTight le base tight] at hD
  rw [SimpleGraph.edgeSet_sup, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
    SimpleGraph.edgeSet_sdiff, Set.ncard_sdiff (SimpleGraph.edgeSet_mono le) (Set.toFinite _)]
  · have := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono le) (Set.toFinite _)
    omega
  · rw [Set.disjoint_left]
    intro e h1 h2
    induction e using Sym2.ind with
    | h x y => exact fresh x y h2 h1

end Hypostructure.Graph.SwitchForcedPaths.SwapAccounting


namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Classical

variable {object : FiniteObject.{u}}

/-! ## The same-vertex switch at a centre of degree `≥ k+2` -/

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
  obtain ⟨w, wPath, wFresh, wLen⟩ := Hypostructure.Graph.ReadingSpectrum.EdgeContext.cycle_through_edge c.walk c.isCycle he
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

end Hypostructure.Graph.SwitchForcedPaths


namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Classical

variable {object : FiniteObject.{u}}

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

end Hypostructure.Graph.SwitchForcedPaths


namespace Hypostructure.Graph.SwitchForcedPaths

/-- **Exact arithmetic of the same-vertex dichotomy at the dyadic target**: the
closing cycle `|p| + 2 = 2^j + 1` (`j ≥ 2`) is never a power of two, so case (i)
of `sameVertex_path_dichotomy` carries no conflict with `K .selection`. -/
theorem closing_length_not_dyadic {j : Nat} (hj : 2 ≤ j) :
    ¬ Hypostructure.Core.DyadicLength.PowerOfTwoLength (2 ^ j + 1) := by
  rintro ⟨e, he, eq⟩
  have h1 : 2 ^ j % 2 = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    simp [Nat.pow_succ]
  have h2 : 2 ^ e.1 % 2 = 0 := by
    obtain ⟨t, ht⟩ : ∃ t, e.1 = t + 1 := ⟨e.1 - 1, by omega⟩
    rw [ht]; simp [Nat.pow_succ]
  omega

end Hypostructure.Graph.SwitchForcedPaths

namespace Hypostructure.Graph.SwitchForcedPaths
open Hypostructure Hypostructure.Graph Classical
variable {object : FiniteObject.{u}}

/-- The split object `(G − h) ⊔ M`, with `M` pulled back to `V ∖ {h}`. -/
noncomputable def splitObj (object : FiniteObject.{u}) (h : object.Vertex)
    (M : SimpleGraph object.Vertex) : FiniteObject.{u} :=
  let K := object.induce (object.vertexFinset.erase h)
  { Vertex := K.Vertex
    graph := K.graph ⊔ M.comap Subtype.val
    vertices := K.vertices
    decideAdj := Classical.decRel _ }

theorem splitObj_vertexCount (h : object.Vertex) (M : SimpleGraph object.Vertex) :
    (splitObj object h M).vertexCount + 1 = object.vertexCount := by
  have := FiniteObject.vertexCount_induce object (object.vertexFinset.erase h)
  change (object.induce (object.vertexFinset.erase h)).vertexCount + 1 = _
  rw [this, Finset.card_erase_of_mem (object.mem_vertexFinset h),
    FiniteObject.card_vertexFinset]
  have : 0 < object.vertexCount := by
    rw [← FiniteObject.card_vertexFinset]
    exact Finset.card_pos.2 ⟨h, object.mem_vertexFinset h⟩
  omega

/-- The split embeds in `G ⊔ M` avoiding `h`. -/
def splitHom (h : object.Vertex) (M : SimpleGraph object.Vertex) :
    (splitObj object h M).graph →g (object.graph ⊔ M) where
  toFun v := v.1
  map_rel' := by
    intro a b adj
    rcases adj with adj | adj
    · exact Or.inl adj
    · exact Or.inr adj

theorem splitHom_injective (h : object.Vertex) (M : SimpleGraph object.Vertex) :
    Function.Injective (splitHom (object := object) h M) :=
  fun a b e => Subtype.ext e

/-- **Vertex split at a minimal object** (vocabulary-free).  Let `M` pair up the
neighbours of `h`: every `M`-edge joins two neighbours of `h` that are
non-adjacent in `G`, and every neighbour of `h` has an `M`-partner.  Then
`(G − h) ⊔ M` keeps `δ ≥ k` with one vertex fewer, so minimality forces an
accepted cycle of `G ⊔ M` avoiding `h` and using an `M`-edge absent from `G`. -/
theorem split_forced_cycle {k : Nat} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (baseline : MinimumDegreeAtLeast k object)
    {h : object.Vertex} {M : SimpleGraph object.Vertex}
    (pairs : ∀ x y, M.Adj x y → object.graph.Adj h x ∧ object.graph.Adj h y ∧
      ¬ object.graph.Adj x y)
    (cover : ∀ x, object.graph.Adj h x → ∃ y, M.Adj x y) :
    ∃ (v : object.Vertex) (c : (object.graph ⊔ M).Walk v v),
      c.IsCycle ∧ L c.length ∧ h ∉ c.support ∧
        ∃ e ∈ c.edges, e ∈ M.edgeSet ∧ e ∉ object.graph.edgeSet := by
  haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
  haveI : Finite (splitObj object h M).Vertex := by
    letI := (splitObj object h M).vertices; infer_instance
  have baseDeg : ∀ w, k ≤ object.degree w := fun w =>
    baseline.trans (object.minDegree_le_degree w)
  have hne : ∀ x y, M.Adj x y → x ≠ h ∧ y ≠ h := by
    intro x y m
    obtain ⟨hx, hy, -⟩ := pairs x y m
    exact ⟨hx.ne.symm, hy.ne.symm⟩
  -- δ of the split
  have degSplit : ∀ v : (splitObj object h M).Vertex, k ≤ (splitObj object h M).degree v := by
    intro v
    rw [FiniteObject.degree_eq_ncard_neighborSet]
    have vne : v.1 ≠ h := (Finset.mem_erase.1 v.2).1
    let valS : (splitObj object h M).Vertex → object.Vertex := fun x => x.1
    have valInj : Function.Injective valS := fun a b e => Subtype.ext e
    rw [← Set.ncard_image_of_injective _ valInj]
    have base := baseDeg v.1
    rw [FiniteObject.degree_eq_ncard_neighborSet] at base
    have inG : object.graph.neighborSet v.1 \ {h} ⊆
        valS '' (splitObj object h M).graph.neighborSet v := by
      intro w ⟨hw, wh⟩
      have wT : w ∈ object.vertexFinset.erase h :=
        Finset.mem_erase.2 ⟨wh, object.mem_vertexFinset w⟩
      exact ⟨⟨w, wT⟩, Or.inl hw, rfl⟩
    by_cases hv : object.graph.Adj h v.1
    · obtain ⟨y, my⟩ := cover v.1 hv
      have yh := (hne _ _ my).2
      have yT : y ∈ object.vertexFinset.erase h :=
        Finset.mem_erase.2 ⟨yh, object.mem_vertexFinset y⟩
      have sub : (object.graph.neighborSet v.1 \ {h}) ∪ {y} ⊆
          valS '' (splitObj object h M).graph.neighborSet v := by
        rintro w (hw | hw)
        · exact inG hw
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact ⟨⟨_, yT⟩, Or.inr my, rfl⟩
      have disj : y ∉ object.graph.neighborSet v.1 \ {h} := fun hy => (pairs _ _ my).2.2 hy.1
      have card := Set.ncard_le_ncard sub (Set.toFinite _)
      rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 disj) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton] at card
      have hmem : h ∈ object.graph.neighborSet v.1 := hv.symm
      have := Set.ncard_sdiff_singleton_add_one hmem (Set.toFinite _)
      omega
    · have eq : object.graph.neighborSet v.1 \ {h} = object.graph.neighborSet v.1 := by
        ext w
        simp only [Set.mem_diff, Set.mem_singleton_iff, and_iff_left_iff_imp]
        rintro hw rfl
        exact hv hw.symm
      rw [eq] at inG
      exact base.trans (Set.ncard_le_ncard inG (Set.toFinite _))
  have base : MinimumDegreeAtLeast k (splitObj object h M) := by
    unfold MinimumDegreeAtLeast
    by_cases ne : Nonempty (splitObj object h M).Vertex
    · exact FiniteObject.le_minDegree_of_forall_le_degree _ k degSplit
    · -- empty split: then `h` is the only vertex, so `δ ≥ k` forces `k = 0`
      have : k = 0 := by
        by_contra kpos
        have b := baseDeg h
        rw [FiniteObject.degree_eq_ncard_neighborSet] at b
        obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).1
          (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero kpos) b)
        exact ne ⟨⟨w, Finset.mem_erase.2 ⟨(hw : object.graph.Adj h w).ne.symm,
          object.mem_vertexFinset w⟩⟩⟩
      omega
  have smaller : (splitObj object h M).LexicographicallySmaller object :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
      have := splitObj_vertexCount h M; omega)
  obtain ⟨c⟩ := minimal _ smaller base
  let f := splitHom (object := object) h M
  refine ⟨c.vertex.1, c.walk.map f, c.isCycle.map (splitHom_injective h M), ?_, ?_, ?_⟩
  · convert c.length_ok using 1; exact SimpleGraph.Walk.length_map _ _
  · intro hs
    have hs' : h ∈ (c.walk.support.map f) := by
      have := SimpleGraph.Walk.support_map f c.walk
      rw [← this]; exact hs
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hs'
    exact (Finset.mem_erase.1 x.2).1 hx
  · by_contra none
    push Not at none
    -- every edge of the image is a `G`-edge: then `c` is a cycle of `G − h ⊆ G`
    have hK : ∀ e ∈ c.walk.edges, e ∈ (object.induce (object.vertexFinset.erase h)).graph.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have adj := c.walk.adj_of_mem_edges he
        rcases adj with adj | adj
        · exact adj
        · have mem : s(a.1, b.1) ∈ (c.walk.map f).edges := by
            rw [SimpleGraph.Walk.edges_map, List.mem_map]
            exact ⟨s(a, b), he, rfl⟩
          exact none _ mem adj
    let e := SimpleGraph.Embedding.induce (G := object.graph)
      ((object.vertexFinset.erase h : Finset object.Vertex) : Set object.Vertex)
    let g : (object.induce (object.vertexFinset.erase h)).graph →g object.graph := e.toHom
    exact avoids ⟨⟨_, (c.walk.transfer _ hK).map g,
      ((c.isCycle.transfer hK).map e.injective), by
        convert c.length_ok using 1
        exact (SimpleGraph.Walk.length_map _ _).trans (SimpleGraph.Walk.length_transfer _ _)⟩⟩

end Hypostructure.Graph.SwitchForcedPaths

namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Classical

variable {object : FiniteObject.{u}}

/-- **Pairing at a high centre** (vocabulary-free): if `G[N(h)]` has no path of
length two (a matching) and `deg h ≥ 4`, the graph `M_h` of all non-adjacent
pairs of `N(h)` covers every neighbour of `h`. -/
theorem highCentre_cover (h : object.Vertex) (heavy : 4 ≤ object.degree h)
    (matching : ∀ ⦃x y z : object.Vertex⦄, object.graph.Adj h x → object.graph.Adj h y →
      object.graph.Adj h z → x ≠ z → object.graph.Adj x y → object.graph.Adj y z → False)
    (x : object.Vertex) (hx : object.graph.Adj h x) :
    ∃ y, object.graph.Adj h y ∧ x ≠ y ∧ ¬ object.graph.Adj x y := by
  haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
  rw [FiniteObject.degree_eq_ncard_neighborSet] at heavy
  by_contra none
  push Not at none
  -- every neighbour of `h` other than `x` is adjacent to `x`; take three of them
  have sub : object.graph.neighborSet h \ {x} ⊆ object.graph.neighborSet x := by
    rintro y ⟨hy, yx⟩
    exact none y hy (Ne.symm yx)
  have card : 3 ≤ (object.graph.neighborSet h \ {x}).ncard := by
    have := Set.ncard_sdiff_singleton_add_one (show x ∈ object.graph.neighborSet h from hx)
      (Set.toFinite _)
    omega
  have one : 1 < (object.graph.neighborSet h \ {x}).ncard := by omega
  obtain ⟨y, hy, z, hz, yz⟩ := Set.one_lt_ncard_iff_nontrivial.1 one
  exact matching hy.1 hx hz.1 yz (sub hy).symm (sub hz)

end Hypostructure.Graph.SwitchForcedPaths

namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure Hypostructure.Graph

variable {object : FiniteObject.{u}}

/-- The non-adjacent pairs of `N(h)`. -/
def antiPairs (object : FiniteObject.{u}) (h : object.Vertex) : SimpleGraph object.Vertex :=
  SimpleGraph.fromRel fun x y =>
    object.graph.Adj h x ∧ object.graph.Adj h y ∧ ¬ object.graph.Adj x y

/-- **Forced cycle of the vertex split at every high centre** (vocabulary-free,
at any minimal object whose high centres have a matching neighbourhood): if
`deg h ≥ 4` and `G[N(h)]` has no path of length two, minimality forces an
accepted cycle of `G ⊔ M_h` avoiding `h` that uses a new edge `xy` between two
non-adjacent neighbours of `h`. -/
theorem highCentre_split_forced {k : Nat} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (baseline : MinimumDegreeAtLeast k object)
    (h : object.Vertex) (heavy : 4 ≤ object.degree h)
    (matching : ∀ ⦃x y z : object.Vertex⦄, object.graph.Adj h x → object.graph.Adj h y →
      object.graph.Adj h z → x ≠ z → object.graph.Adj x y → object.graph.Adj y z → False) :
    ∃ (v : object.Vertex) (c : (object.graph ⊔ antiPairs object h).Walk v v),
      c.IsCycle ∧ L c.length ∧ h ∉ c.support ∧
        ∃ e ∈ c.edges, e ∈ (antiPairs object h).edgeSet ∧ e ∉ object.graph.edgeSet := by
  refine Hypostructure.Graph.SwitchForcedPaths.split_forced_cycle avoids minimal baseline ?_ ?_
  · intro x y m
    rw [antiPairs, SimpleGraph.fromRel_adj] at m
    rcases m.2 with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact ⟨a, b, c⟩
    · exact ⟨b, a, fun hxy => c hxy.symm⟩
  · intro x hx
    obtain ⟨y, hy, ne, na⟩ := highCentre_cover h heavy matching x hx
    exact ⟨y, by rw [antiPairs, SimpleGraph.fromRel_adj]; exact ⟨ne, Or.inl ⟨hx, hy, na⟩⟩⟩

end Hypostructure.Graph.SwitchForcedPaths

namespace Hypostructure.Graph.SwitchForcedPaths

open Hypostructure Hypostructure.Graph

variable {object : FiniteObject.{u}}

/-- **Star obstruction at a vertex** (vocabulary-free): on an object without
dyadic cycles, two simple paths from a common vertex `x` to two distinct
neighbours `y, z` of `h`, both of length `2^j − 1` (`j ≥ 1`), cannot both avoid
`h` while meeting only at `x`. -/
theorem star_forbidden
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    {h x y z : object.Vertex} {j : Nat} (hj : 1 ≤ j)
    (ay : object.graph.Adj y h) (az : object.graph.Adj z h) (yz : y ≠ z)
    (P : object.graph.Walk x y) (Q : object.graph.Walk x z) (pp : P.IsPath) (qp : Q.IsPath)
    (lp : P.length + 1 = 2 ^ j) (lq : Q.length + 1 = 2 ^ j) :
    ¬ (h ∉ P.support ∧ h ∉ Q.support ∧ ∀ w ∈ P.support, w ∈ Q.support → w = x) := by
  rintro ⟨hP, hQ, disj⟩
  let W1 := P.concat ay
  let W2 := (Q.concat az).reverse
  have w1 : W1.IsPath := (SimpleGraph.Walk.concat_isPath_iff _).2 ⟨pp, hP⟩
  have w2 : W2.IsPath := ((SimpleGraph.Walk.concat_isPath_iff _).2 ⟨qp, hQ⟩).reverse
  have tail1 : ∀ w ∈ W1.support.tail, w = h ∨ (w ∈ P.support ∧ w ≠ x) := by
    intro w hw
    simp only [W1, SimpleGraph.Walk.support_concat] at hw
    have nd := pp.support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support] at nd hw
    rw [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | hw
    · right
      refine ⟨List.mem_of_mem_tail (by rw [← SimpleGraph.Walk.cons_tail_support]; simp [hw]), ?_⟩
      rintro rfl
      exact (List.nodup_cons.1 nd).1 hw
    · exact Or.inl hw
  have tail2 : ∀ w ∈ W2.support.tail, w ∈ Q.support := by
    intro w hw
    simp only [W2, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_concat,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.tail_cons,
      List.mem_reverse] at hw
    exact hw
  have disjT : W1.support.tail.Disjoint W2.support.tail := by
    intro w h1 h2
    have q := tail2 w h2
    rcases tail1 w h1 with rfl | ⟨pw, wx⟩
    · exact hQ q
    · exact wx (disj w pw q)
  have len : (W1.append W2).length = 2 ^ (j + 1) := by
    simp only [W1, W2, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_concat, pow_succ]
    omega
  apply avoids
  refine ⟨⟨x, W1.append W2, w1.isCycle_append w2 disjT (Or.inl ?_), ?_⟩⟩
  · simp only [W1, SimpleGraph.Walk.length_concat]
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  · rw [len]
    have : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
    exact ⟨⟨j + 1, by omega⟩, by simp only; omega, rfl⟩

/-- **Cross-vertex switch family at a minimal object** (vocabulary-free).  Fix
an edge `u₁v` with `deg v ≥ 4`, and a vertex `h' ≠ v` with `deg h' ≥ 4`.  For
every neighbour `u` of `h'` with `u ≁ u₁` (four distinct endpoints), minimality
forces a `u₁→u` path of length `2^{j_u} − 1` in `G − {u₁v, uh'}`; and for any two
such `u ≠ u'` whose forced paths have the same length, those two paths are not
simultaneously `h'`-free and internally disjoint. -/
theorem cross_switch_family
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast 3 H → HasCycleWithLength Core.DyadicLength.PowerOfTwoLength H)
    (baseline : MinimumDegreeAtLeast 3 object)
    {u₁ v h' : object.Vertex} (a₁ : object.graph.Adj u₁ v) (vh : v ≠ h')
    (dv : 4 ≤ object.degree v) (dh : 4 ≤ object.degree h') :
    (∀ u, object.graph.Adj u h' → u ≠ u₁ → u ≠ v → u₁ ≠ h' → ¬ object.graph.Adj u₁ u →
      ∃ p : (object.graph.deleteEdges {s(u₁, v), s(u, h')}).Walk u₁ u,
        p.IsPath ∧ Core.DyadicLength.PowerOfTwoLength (p.length + 1)) ∧
    (∀ u u' j (P : object.graph.Walk u₁ u) (Q : object.graph.Walk u₁ u'),
      object.graph.Adj u h' → object.graph.Adj u' h' → u ≠ u' → 1 ≤ j →
      P.IsPath → Q.IsPath → P.length + 1 = 2 ^ j → Q.length + 1 = 2 ^ j →
      ¬ (h' ∉ P.support ∧ h' ∉ Q.support ∧ ∀ w ∈ P.support, w ∈ Q.support → w = u₁)) := by
  refine ⟨?_, ?_⟩
  · intro u au hu1 huv hu1h na
    exact Hypostructure.Graph.SwitchForcedPaths.twoSwitch_forced_path (k := 3) avoids minimal baseline a₁ au
      (Ne.symm hu1) hu1h (Ne.symm huv) vh na (by omega) (by omega)
  · intro u u' j P Q au au' uu hj pp qp lp lq
    exact star_forbidden avoids hj au au' uu P Q pp qp lp lq

end Hypostructure.Graph.SwitchForcedPaths
