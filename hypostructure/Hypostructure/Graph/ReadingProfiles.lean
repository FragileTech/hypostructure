import Hypostructure.Graph.GluedReadingMaps
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.SparsePairResponse
import Hypostructure.Graph.RootedReturn

/-!
# Reading profiles of a support

Let `Z` be a vertex support of a finite object `G`, `∂Z` its cut boundary and
`ret_R` the reading of `Z` retained on `R` (the piece of `Z` keeping only the
edges with both ends in `R`).

* The boundary degree of `ret_R` at `b ∈ ∂Z` is the reading count
  `c_R(b) = #{w ∈ Z : b ~ w, b ∈ R, w ∈ R}` (`retained_boundaryDegree`), so two
  readings have the same boundary-degree profile iff their counts agree
  (`profile_eq_iff_counts`), and equal profiles transfer retained boundary
  vertices (`mem_of_profile_eq`).
* The spanning object of a subgraph loses the baseline at a tight endpoint of a
  deleted edge (`spanning_*_tight`); a non-injective declared quotient is
  refuted by minimality and the replacement exclusion
  (`declaredQuotient_reducing_false`).
* Steiner minimality of `CanonicalSupport.select?` (`select_no_smaller`,
  `select_nonseed_cut`, `select_neighbourhood_needed`, `hanging_meets_seed`),
  reading-count bounds (`readingCount_*`, `U1_*`), boundary-free supports
  (`boundaryFree_*`), walks and cycles through the boundary
  (`walk_meets_boundary`, `cycle_two_boundary`,
  `no_reading_walk_from_unretained`) and one-sided transfer
  (`onesided_singleton`).

Every statement is about an arbitrary finite object; nothing here knows a
presentation, a ledger, or a manuscript.
-/

namespace Hypostructure.Graph.ReadingProfiles

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

section Generic

variable {object : FiniteObject.{u}}

/-- `pieceDecode` is injective (vocabulary-free). -/
theorem pieceDecode_injective (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.pieceDecode object Z) := by
  intro x y h
  rcases x with a | a <;> rcases y with b | b <;>
    simp [SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl h
  · exact absurd (h ▸ a.2) b.2.2
  · exact absurd (h ▸ b.2) a.2.2
  · exact congrArg Sum.inr (Subtype.ext h)

theorem pieceDecode_mem (Z : Finset object.Vertex)
    (x : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    SupportAtom.pieceDecode object Z x ∈ Z := by
  rcases x with a | a
  · exact ((SupportAtom.mem_cutBoundary_iff object Z a.1).1 a.2).1
  · exact a.2.1

theorem exists_pieceDecode_eq {Z : Finset object.Vertex} {w : object.Vertex}
    (hw : w ∈ Z) : ∃ x, SupportAtom.pieceDecode object Z x = w := by
  classical
  by_cases hb : w ∈ SupportAtom.cutBoundary object Z
  · exact ⟨.inl ⟨w, hb⟩, rfl⟩
  · exact ⟨.inr ⟨w, hw, hb⟩, rfl⟩

/-- **Exact boundary-degree formula of a reading** (vocabulary-free).
At a boundary vertex `b` of `∂Z`, the reading of `Z` retained on `R` has degree
`#{w ∈ Z : b ~ w, b ∈ R, w ∈ R}`. -/
theorem retained_boundaryDegree (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R}.ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  let N : Set ((SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :=
    {x | (SupportAtom.retainedPiece object Z R).graph.Adj (.inl b) x}
  change N.ncard = _
  rw [← Set.ncard_image_of_injective N (pieceDecode_injective (object := object) Z)]
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have adj : (SupportAtom.retainedPiece object Z R).graph.Adj (.inl b) x := hx
    change (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _ at adj
    rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      SimpleGraph.fromRel_adj] at adj
    obtain ⟨gAdj, -, rel⟩ := adj
    refine ⟨pieceDecode_mem Z x, gAdj, ?_⟩
    rcases rel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  · rintro ⟨wZ, adj, bR, wR⟩
    obtain ⟨x, rfl⟩ := exists_pieceDecode_eq wZ
    refine ⟨x, ?_, rfl⟩
    show (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _
    rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      SimpleGraph.fromRel_adj]
    exact ⟨adj, adj.ne, Or.inl ⟨bR, wR⟩⟩

/-- A reading vanishes at a boundary vertex it does not retain. -/
theorem retained_boundaryDegree_eq_zero (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∉ R) :
    (SupportAtom.retainedPiece object Z R).boundaryDegree b = 0 := by
  rw [retained_boundaryDegree]
  convert Set.ncard_empty object.Vertex
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, bR, -⟩
  exact hb bR

/-- A reading is positive at a retained boundary vertex with a retained
neighbour in `Z`. -/
theorem retained_boundaryDegree_pos (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∈ R)
    {w : object.Vertex} (wZ : w ∈ Z) (wR : w ∈ R) (adj : object.graph.Adj b.1 w) :
    0 < (SupportAtom.retainedPiece object Z R).boundaryDegree b := by
  rw [retained_boundaryDegree]
  apply Set.ncard_pos (Set.toFinite _) |>.2
  exact ⟨w, wZ, adj, hb, wR⟩

/-- **Profile transfer** (vocabulary-free).  If two readings of `Z` have the
same boundary-degree profile, then every boundary vertex retained by the first
reading with a retained `Z`-neighbour is retained by the second. -/
theorem mem_of_profile_eq {Z R R' : Finset object.Vertex}
    (profile : (SupportAtom.retainedPiece object Z R).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object Z R').boundaryDegreeProfile)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∈ R)
    {w : object.Vertex} (wZ : w ∈ Z) (wR : w ∈ R) (adj : object.graph.Adj b.1 w) :
    b.1 ∈ R' := by
  by_contra notIn
  have pos := retained_boundaryDegree_pos Z R b hb wZ wR adj
  have zero := retained_boundaryDegree_eq_zero Z R' b notIn
  have eq := congrFun profile b
  change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
    (SupportAtom.retainedPiece object Z R').boundaryDegree b at eq
  omega

/-- In a connected set with at least two vertices every vertex has a neighbour
inside the set. -/
theorem exists_adj_of_connectedOn {X : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object X)
    {b c : object.Vertex} (hb : b ∈ X) (hc : c ∈ X) (ne : b ≠ c) :
    ∃ w ∈ X, object.graph.Adj b w := by
  obtain ⟨path, -, inside⟩ := connected.2 hb hc
  cases path with
  | nil => exact absurd rfl ne
  | cons adj rest =>
    exact ⟨_, inside _ (by simp), adj⟩

/-! ### Boundary-free readings -/

/-- The closed case: when `Z` is everything, `∂Z = ∅`, so every reading is
boundary-free. -/
theorem cutBoundary_eq_empty_of_covers {Z : Finset object.Vertex}
    (covers : ∀ v, v ∈ Z) : ∀ w, w ∉ SupportAtom.cutBoundary object Z := by
  intro w hw
  obtain ⟨-, n, -, nZ⟩ := (SupportAtom.mem_cutBoundary_iff object Z w).1 hw
  exact nZ (covers n)

/-! ### Deleting edges of a tight graph breaks the baseline -/

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

/-! ### A non-injective declared quotient is self-refuting at a minimal object -/

/-- **Circularity of a non-injective declared quotient** (vocabulary-free): a
non-injective admissible quotient carries, as a field, the replacement or
smaller representative that the replacement exclusion and minimality forbid; so at a
minimal target-avoiding object no such quotient exists. -/
theorem declaredQuotient_reducing_false {Baseline Target : FiniteObject.{u} → Prop}
    {Coordinate : Type u} {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (exclusion : ∀ S, ¬ ReplacementSupport Baseline Target object S)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H)
    (avoids : ¬ Target object)
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (reducing : ¬ Set.InjOn quotient.label ↑family) : False := by
  rcases quotient.localize reducing with r | ⟨H, sm, bl, noTarget⟩
  · exact exclusion _ r
  · exact noTarget (minimal H sm bl)

/-- The exact reading count `c_R(b) = #{w ∈ Z : b ~ w, b ∈ R, w ∈ R}`. -/
noncomputable def readingCount (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) : Nat :=
  {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R}.ncard

/-- Profile equality of two readings is exactly equality of reading counts. -/
theorem profile_eq_iff_counts (Z R R' : Finset object.Vertex) :
    (SupportAtom.retainedPiece object Z R).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object Z R').boundaryDegreeProfile ↔
      ∀ b, readingCount Z R b = readingCount Z R' b := by
  constructor
  · intro h b
    have := congrFun h b
    change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      (SupportAtom.retainedPiece object Z R').boundaryDegree b at this
    rwa [retained_boundaryDegree, retained_boundaryDegree] at this
  · intro h
    funext b
    change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      (SupportAtom.retainedPiece object Z R').boundaryDegree b
    rw [retained_boundaryDegree, retained_boundaryDegree]
    exact h b

end Generic

section Swap

variable {object : FiniteObject.{u}}

/-- The swap object `G − (E(G[X_q]) \ E(G[X_p]))`: `G` with `ret_q`'s private
edges removed, i.e. `ret_q` glued back as `ret_p`. -/
def swapGraph (Xp Xq : Finset object.Vertex) : SimpleGraph object.Vertex :=
  object.graph.deleteEdges
    {e | ∃ x y, e = s(x, y) ∧ x ∈ Xq ∧ y ∈ Xq ∧ ¬ (x ∈ Xp ∧ y ∈ Xp)}

/-- **The swap construction, exactly** (vocabulary-free): either every edge of
`G[X_q]` lies in `G[X_p]` (the swap object is `G` itself), or the swap object
loses `δ ≥ k` at a tight endpoint `w` of a private edge of `G[X_q]`, with
`deg(w) ≤ k − 1`. -/
theorem swap_exact {k : Nat} (tightEndpoint : ∀ d : object.graph.Dart,
      object.degree d.fst = k ∨ object.degree d.snd = k)
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
    exact spanning_not_baseline_of_tight le tightEndpoint adj drop

/-- **Equal-count readings on disjoint supports collapse to the boundary-free configuration**
(vocabulary-free input): with the transfer clause of equal counts, a connected support
`X_p` with at least two vertices, disjoint from `X_q`, never meets `∂Z`. -/
theorem U2_disjoint_boundaryFree {Z Xp Xq : Finset object.Vertex}
    (transfer : ∀ b : (SupportAtom.boundary object Z).Vertex, b.1 ∈ Xp →
      ∀ w ∈ Xp, object.graph.Adj b.1 w → b.1 ∈ Xq)
    (connected : SupportComponents.Connected.ConnectedOn object Xp)
    (two : ∀ b ∈ Xp, ∃ c ∈ Xp, c ≠ b)
    (disjoint : Disjoint Xp Xq) :
    ∀ w ∈ Xp, w ∉ SupportAtom.cutBoundary object Z := by
  intro w hw hb
  obtain ⟨c, hc, ne⟩ := two w hw
  obtain ⟨n, hn, adj⟩ := exists_adj_of_connectedOn connected hw hc ne.symm
  exact Finset.disjoint_left.1 disjoint hw (transfer ⟨w, hb⟩ hw n hn adj)

end Swap

/-! ## D: the three next constructions -/

section D

open Classical

variable {object : FiniteObject.{u}}

/-- **Steiner minimality of `select?`** (vocabulary-free): no proper subset of
the selected support that still contains the seed is connected. -/
theorem select_no_smaller {seed X Y : Finset object.Vertex}
    (selected : CanonicalSupport.select? object seed = some X)
    (sub : Y ⊆ X) (ne : Y ≠ X) (seedY : seed ⊆ Y)
    (connected : SupportComponents.Connected.ConnectedOn object Y) : False := by
  have le := CanonicalSupport.select?_card_le selected
    (CanonicalSupport.mem_candidates_iff.2 ⟨seedY, connected⟩)
  have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨sub, ne⟩)
  omega

/-- Every non-seed vertex of a selected support is a cut vertex of it. -/
theorem select_nonseed_cut {seed X : Finset object.Vertex}
    (selected : CanonicalSupport.select? object seed = some X)
    {v : object.Vertex} (vX : v ∈ X) (vSeed : v ∉ seed) :
    ¬ SupportComponents.Connected.ConnectedOn object (X.erase v) := by
  classical
  intro conn
  refine select_no_smaller selected (Finset.erase_subset _ _) ?_ ?_ conn
  · intro h
    have : v ∈ X.erase v := by rw [h]; exact vX
    simp at this
  · intro w hw
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · rintro rfl; exact vSeed hw
    · have cand := (CanonicalSupport.mem_candidates_iff.1
        (CanonicalSupport.select?_mem_candidates selected))
      exact cand.1 hw

/-- **Neighbourhood cut of a selected support** (vocabulary-free): deleting `N(b)` from a selected support.
If `b` has a neighbour in `X` and no neighbour in the seed, then `X ∖ N(b)` is
disconnected: `b`'s neighbours in `X` are needed for connectivity. -/
theorem select_neighbourhood_needed {seed X : Finset object.Vertex}
    (selected : CanonicalSupport.select? object seed = some X)
    {b : object.Vertex} (hasNbr : ∃ w ∈ X, object.graph.Adj b w)
    (seedFree : ∀ w ∈ seed, ¬ object.graph.Adj b w) :
    ¬ SupportComponents.Connected.ConnectedOn object
      (X.filter fun w => ¬ object.graph.Adj b w) := by
  classical
  intro conn
  have cand := (CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates selected))
  obtain ⟨w, wX, adj⟩ := hasNbr
  refine select_no_smaller selected (Finset.filter_subset _ _) ?_ ?_ conn
  · intro h
    have : w ∈ X.filter fun w => ¬ object.graph.Adj b w := by rw [h]; exact wX
    exact (Finset.mem_filter.1 this).2 adj
  · intro v hv
    exact Finset.mem_filter.2 ⟨cand.1 hv, seedFree v hv⟩

/-- **Reading-count bound** (vocabulary-free): at a boundary vertex of `Z`, every
reading count is at most `deg_G(b) − 1` (the outside neighbour is never
counted). -/
theorem readingCount_add_one_le (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    readingCount Z R b + 1 ≤ object.degree b.1 := by
  letI : Finite object.Vertex := by letI := object.vertices; infer_instance
  obtain ⟨-, n, adj, nZ⟩ := (SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have sub : {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R} ⊆
      object.graph.neighborSet b.1 \ {n} := by
    rintro w ⟨wZ, wAdj, -, -⟩
    refine ⟨wAdj, ?_⟩
    rintro rfl
    exact nZ wZ
  calc readingCount Z R b + 1 ≤ (object.graph.neighborSet b.1 \ {n}).ncard + 1 :=
        Nat.add_le_add_right (Set.ncard_le_ncard sub (Set.toFinite _)) 1
    _ = _ := Set.ncard_sdiff_singleton_add_one adj (Set.toFinite _)

/-- **Reading counts at a tight boundary vertex**: counts are at most `threshold − 1`, so the
separating vertex has `c_p(b), c_q(b) ∈ {0, …, δ−1}` and `1 ≤ |c_p(b) − c_q(b)|`. -/
theorem U1_counts_tight {k : Nat} (Z Xp Xq : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) (tight : object.degree b.1 = k)
    (differ : readingCount Z Xp b ≠ readingCount Z Xq b) :
    readingCount Z Xp b + 1 ≤ k ∧ readingCount Z Xq b + 1 ≤ k ∧
      (readingCount Z Xp b < readingCount Z Xq b ∨
        readingCount Z Xq b < readingCount Z Xp b) := by
  have h1 := readingCount_add_one_le Z Xp b
  have h2 := readingCount_add_one_le Z Xq b
  omega

/-- A positive reading count means `b` is retained and has a retained
`Z`-neighbour. -/
theorem readingCount_pos {Z R : Finset object.Vertex}
    {b : (SupportAtom.boundary object Z).Vertex} (pos : 0 < readingCount Z R b) :
    b.1 ∈ R ∧ ∃ w ∈ R, object.graph.Adj b.1 w := by
  obtain ⟨w, wZ, adj, bR, wR⟩ := (Set.ncard_pos (Set.toFinite _)).1 pos
  exact ⟨bR, w, wR, adj⟩

/-- **Separating-count configuration** (vocabulary-free).  At a vertex `b` with different counts, one of
the two supports, say `R = select?(seed)`, has `c_R(b) > 0`; then either `b` is
adjacent to the seed of `R`, or `R ∖ N(b)` is disconnected (b's neighbours are a
cut structure of `R`). -/
theorem U1_exact {Z Xp Xq seedP seedQ : Finset object.Vertex}
    (selP : CanonicalSupport.select? object seedP = some Xp)
    (selQ : CanonicalSupport.select? object seedQ = some Xq)
    (b : (SupportAtom.boundary object Z).Vertex)
    (differ : readingCount Z Xp b ≠ readingCount Z Xq b) :
    (0 < readingCount Z Xp b ∧
        ((∃ w ∈ seedP, object.graph.Adj b.1 w) ∨
          ¬ SupportComponents.Connected.ConnectedOn object
            (Xp.filter fun w => ¬ object.graph.Adj b.1 w))) ∨
      (0 < readingCount Z Xq b ∧
        ((∃ w ∈ seedQ, object.graph.Adj b.1 w) ∨
          ¬ SupportComponents.Connected.ConnectedOn object
            (Xq.filter fun w => ¬ object.graph.Adj b.1 w))) := by
  have side : ∀ {seed X : Finset object.Vertex},
      CanonicalSupport.select? object seed = some X → 0 < readingCount Z X b →
      ((∃ w ∈ seed, object.graph.Adj b.1 w) ∨
        ¬ SupportComponents.Connected.ConnectedOn object
          (X.filter fun w => ¬ object.graph.Adj b.1 w)) := by
    intro seed X sel pos
    by_cases touch : ∃ w ∈ seed, object.graph.Adj b.1 w
    · exact Or.inl touch
    · push Not at touch
      obtain ⟨-, hasNbr⟩ := readingCount_pos pos
      exact Or.inr (select_neighbourhood_needed sel hasNbr touch)
  rcases Nat.eq_zero_or_pos (readingCount Z Xp b) with zero | pos
  · have : 0 < readingCount Z Xq b := by omega
    exact Or.inr ⟨this, side selQ this⟩
  · exact Or.inl ⟨pos, side selP pos⟩

/-- **Boundary of a boundary-free selection** (vocabulary-free): in the boundary-free configuration every
boundary vertex of `Z = select?(X_p ∪ X_q)` lies in the connector
`Z ∖ (X_p ∪ X_q)` and is a cut vertex of `Z`. -/
theorem boundaryFree_boundary_cut {Z Xp Xq : Finset object.Vertex}
    (selected : CanonicalSupport.select? object (Xp ∪ Xq) = some Z)
    (freeP : ∀ w ∈ Xp, w ∉ SupportAtom.cutBoundary object Z)
    (freeQ : ∀ w ∈ Xq, w ∉ SupportAtom.cutBoundary object Z)
    (b : (SupportAtom.boundary object Z).Vertex) :
    b.1 ∉ Xp ∧ b.1 ∉ Xq ∧
      ¬ SupportComponents.Connected.ConnectedOn object (Z.erase b.1) := by
  classical
  have bP : b.1 ∉ Xp := fun h => freeP _ h b.2
  have bQ : b.1 ∉ Xq := fun h => freeQ _ h b.2
  refine ⟨bP, bQ, select_nonseed_cut selected ?_ ?_⟩
  · exact ((SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2).1
  · simp [bP, bQ]

/-- **Exits of a boundary-free selection** (vocabulary-free): in the boundary-free
configuration every edge leaving `Z` starts at a connector vertex, never at
`X_p ∪ X_q`: each vertex of `X_p ∪ X_q` has all its `G`-neighbours in `Z`. -/
theorem boundaryFree_neighbours_inside {Z X : Finset object.Vertex}
    (XZ : X ⊆ Z) (free : ∀ w ∈ X, w ∉ SupportAtom.cutBoundary object Z)
    {w n : object.Vertex} (wX : w ∈ X) (adj : object.graph.Adj w n) : n ∈ Z := by
  by_contra nZ
  exact free w wX ((SupportAtom.mem_cutBoundary_iff object Z w).2 ⟨XZ wX, n, adj, nZ⟩)

/-- On G, every pair support is the canonical selection of its pair seed. -/
theorem pairSupport_selected {Coordinate Chord : Type u}
    (connected : object.graph.Connected)
    (activation : FiniteObject.DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) :
    ∃ X, CanonicalSupport.select? object (activation.pairSeed pair) = some X ∧
      (activation.pairSupport pair).getD ∅ = X := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1
    (FiniteObject.DemandActivation.pairSupport_isSome_of_connected activation pair
      (SupportComponents.Connected.connectedOn_vertexFinset object connected))
  exact ⟨X, hX, by rw [hX]; rfl⟩

end D

section Onesided

variable {object : FiniteObject.{u}}

/-- **A one-sided transfer region collapses to a singleton support**
(vocabulary-free): with the transfer clause of equal counts and a connected support `X`,
a boundary vertex of `Z` in `X` but not in `Y` forces `X = {b}`. -/
theorem onesided_singleton {Z X Y : Finset object.Vertex}
    (transfer : ∀ b : (SupportAtom.boundary object Z).Vertex, b.1 ∈ X →
      ∀ w ∈ X, object.graph.Adj b.1 w → b.1 ∈ Y)
    (connected : SupportComponents.Connected.ConnectedOn object X)
    (b : (SupportAtom.boundary object Z).Vertex) (bX : b.1 ∈ X) (bY : b.1 ∉ Y) :
    X = {b.1} := by
  ext c
  simp only [Finset.mem_singleton]
  constructor
  · intro cX
    by_contra ne
    obtain ⟨w, wX, adj⟩ := Hypostructure.Graph.ReadingProfiles.exists_adj_of_connectedOn connected bX cX (Ne.symm ne)
    exact bY (transfer b bX w wX adj)
  · rintro rfl; exact bX

end Onesided

end Hypostructure.Graph.ReadingProfiles

namespace Hypostructure.Graph.ReadingProfiles

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical

variable {object : FiniteObject.{u}}

/-- **Every hanging part of a selected support meets its seed**
(vocabulary-free): if removing a nonempty `Y ⊆ X` leaves `X ∖ Y` connected,
then `Y` contains a seed vertex. -/
theorem hanging_meets_seed {seed X Y : Finset object.Vertex}
    (selected : CanonicalSupport.select? object seed = some X)
    (sub : Y ⊆ X) (ne : Y.Nonempty)
    (connected : SupportComponents.Connected.ConnectedOn object (X \ Y)) :
    (Y ∩ seed).Nonempty := by
  by_contra none
  rw [Finset.not_nonempty_iff_eq_empty] at none
  apply Hypostructure.Graph.ReadingProfiles.select_no_smaller selected Finset.sdiff_subset ?_ ?_ connected
  · intro h
    obtain ⟨y, hy⟩ := ne
    have : y ∈ X \ Y := by rw [h]; exact sub hy
    exact (Finset.mem_sdiff.1 this).2 hy
  · intro v hv
    have cand := CanonicalSupport.mem_candidates_iff.1
      (CanonicalSupport.select?_mem_candidates selected)
    refine Finset.mem_sdiff.2 ⟨cand.1 hv, fun hy => ?_⟩
    have : v ∈ Y ∩ seed := Finset.mem_inter.2 ⟨hy, hv⟩
    rw [none] at this
    simp at this

/-- A walk from `Z` to its outside passes through `∂Z` (vocabulary-free). -/
theorem walk_meets_boundary {Z : Finset object.Vertex} :
    ∀ {u w : object.Vertex} (p : object.graph.Walk u w), u ∈ Z → w ∉ Z →
      ∃ b ∈ p.support, b ∈ SupportAtom.cutBoundary object Z
  | _, _, .nil, hu, hw => absurd hu hw
  | u, _, .cons (v := v) h p', hu, hw => by
      by_cases hv : v ∈ Z
      · obtain ⟨b, hb, hbZ⟩ := walk_meets_boundary p' hv hw
        exact ⟨b, by simp [hb], hbZ⟩
      · exact ⟨u, by simp, (SupportAtom.mem_cutBoundary_iff object Z u).2 ⟨hu, v, h, hv⟩⟩

/-- **A cycle through an interior vertex of `Z` and a vertex outside `Z` meets
`∂Z` in two distinct vertices** (vocabulary-free). -/
theorem cycle_two_boundary {Z : Finset object.Vertex} {v : object.Vertex}
    {c : object.graph.Walk v v} (hc : c.IsCycle)
    {x y : object.Vertex} (hx : x ∈ c.support) (xZ : x ∈ Z)
    (xint : x ∉ SupportAtom.cutBoundary object Z) (hy : y ∈ c.support) (yZ : y ∉ Z) :
    ∃ b₁ ∈ c.support, ∃ b₂ ∈ c.support, b₁ ≠ b₂ ∧
      b₁ ∈ SupportAtom.cutBoundary object Z ∧ b₂ ∈ SupportAtom.cutBoundary object Z := by
  let c' := c.rotate x hx
  have hc' : c'.IsCycle := hc.rotate hx
  have inTail : ∀ z, z ∈ c.support → z ∈ c.support.tail := by
    intro z hz
    rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact SimpleGraph.Walk.end_mem_tail_support hc.not_nil
    · exact hz
  have rot := SimpleGraph.Walk.support_rotate c x hx
  have hy' : y ∈ c'.support :=
    List.mem_of_mem_tail (rot.mem_iff.2 (inTail y hy))
  let q1 := c'.takeUntil y hy'
  let q2 := c'.dropUntil y hy'
  have spec : q1.append q2 = c' := SimpleGraph.Walk.take_spec c' hy'
  obtain ⟨b₁, h1, hb1⟩ := walk_meets_boundary q1 xZ yZ
  obtain ⟨b₂, h2, hb2⟩ := walk_meets_boundary q2.reverse xZ yZ
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h2
  have toC : ∀ z, z ∈ q1.support ∨ z ∈ q2.support → z ∈ c.support := by
    intro z hz
    have : z ∈ c'.support := by
      rw [← spec, SimpleGraph.Walk.mem_support_append_iff]; exact hz
    rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at this
    rcases this with rfl | this
    · exact hx
    · exact List.mem_of_mem_tail (rot.mem_iff.1 this)
  refine ⟨b₁, toC _ (Or.inl h1), b₂, toC _ (Or.inr h2), ?_, hb1, hb2⟩
  rintro rfl
  have bx : b₁ ≠ x := fun e => xint (e ▸ hb1)
  have by' : b₁ ≠ y := fun e => yZ (e ▸ ((SupportAtom.mem_cutBoundary_iff object Z _).1 hb1).1)
  have t1 : b₁ ∈ q1.support.tail := by
    rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at h1
    exact h1.resolve_left bx
  have t2 : b₁ ∈ q2.support.tail := by
    rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at h2
    exact h2.resolve_left by'
  have nd := hc'.support_nodup
  rw [← spec, SimpleGraph.Walk.support_append, ← SimpleGraph.Walk.cons_tail_support q1,
    List.cons_append, List.tail_cons] at nd
  exact List.disjoint_of_nodup_append nd t1 t2

end Hypostructure.Graph.ReadingProfiles

namespace Hypostructure.Graph.ReadingProfiles

open Hypostructure Hypostructure.Graph Hypostructure.Graph.Strategy.InterfaceReplacement

variable {object : FiniteObject.{u}}

/-- **A reading has no edge at a boundary vertex it does not retain**
(vocabulary-free): every walk of the reading starting at such a boundary vertex
is trivial.  When no retained vertex is on `∂Z`, this makes every reading-path statement between
boundary vertices (path spectra) vacuous. -/
theorem no_reading_walk_from_unretained {Z R : Finset object.Vertex}
    {a : (SupportAtom.boundary object Z).Vertex} (ha : a.1 ∉ R) :
    ∀ {w} (p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) w), p.length = 0 := by
  intro w p
  cases p with
  | nil => rfl
  | cons h q =>
    exfalso
    change (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _ at h
    rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      SimpleGraph.fromRel_adj] at h
    rcases h.2.2 with ⟨h1, -⟩ | ⟨-, h1⟩ <;> exact ha h1

end Hypostructure.Graph.ReadingProfiles
