import Hypostructure.Graph.BlobCycles
import Hypostructure.Graph.LadderRun

/-!
# Attachments to a path, chains between two paths, separation at a cut vertex (generic)

Vocabulary-free and application-free.  The statements speak about paths of one graph `G`.

* **Segments** (`seg_path`): the segment `w[i..j]` of a path `w` is a path of length
  `|i − j|` whose vertices are the `w.getVert k`, `k` between `i` and `j`.
* **(a) Attachment** (`walk_attach_cycle`, `attachCycles_of`): a path `r : x ⇝ y` avoiding the
  segment `w[i..j]`, with `w(i) ~ x` and `y ~ w(j)` (and `i ≠ j` or `x ≠ y`), closes a cycle of
  length `|r| + |i − j| + 2` (`BlobCycles.chain_cycle`, the chain with one block).
* **(b) Chain** (`walk_pair_cycle`, `chainCycles_of`): routes `r : x ⇝ y`, `r' : x' ⇝ y'` and
  two segments `w₁[i..i']`, `w₂[j..j']`, pairwise vertex-disjoint, with `w₁(i) ~ x`,
  `y ~ w₂(j)`, `w₂(j') ~ x'`, `y' ~ w₁(i')`, close a cycle of length
  `|r| + |r'| + |i − i'| + |j − j'| + 4`.  Trivial routes (`x = y`) are hubs.
* **(c) Separation** (`cut_separates`): in a connected graph, if `v` is a cut vertex, every
  neighbour of `v` lies in `A ∪ B`, and `A`, `B` are each connected avoiding `v`, then `v` has
  a neighbour in `A` and one in `B`, and no walk avoiding `v` joins `A` to `B`.
* **Counts** (`interior_nbr_off`, `interior_le`, `card_le_of_cubic_cover`): an interior
  vertex of degree `≥ 3` of a shortest path avoiding its end edge has a neighbour off the
  path; if every interior vertex has a neighbour in `Y`, then `|w| − 1 ≤ |Y| · D` with `D` a
  degree bound on `Y`; a set each of whose vertices has a cubic neighbour in `T` has at most
  `3|T|` elements.
-/

set_option linter.unusedSectionVars false

namespace Hypostructure.Graph.WalkAttachment

open SimpleGraph
open Hypostructure.Graph.WalkIndex
open Hypostructure.Graph.PathChords
open Hypostructure.Graph.LadderRun

universe u

section Segment

variable {V : Type u} {G : SimpleGraph V}

/-- **The segment `w[i..j]` of a path.** -/
theorem seg_path {a b : V} (w : G.Walk a b) (hw : w.IsPath) (i j : ℕ) (hi : i ≤ w.length)
    (hj : j ≤ w.length) :
    ∃ s : G.Walk (w.getVert i) (w.getVert j), s.IsPath ∧ s.length = Nat.dist i j ∧
      ∀ v ∈ s.support, ∃ k, min i j ≤ k ∧ k ≤ max i j ∧ v = w.getVert k := by
  rcases le_total i j with h | h
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw', hl1, hl2⟩ := exists_decomp_idx w i j h hj
    subst hu hv
    have hp : (p1.append (p2.append p3)).IsPath := hw' ▸ hw
    refine ⟨p2, hp.of_append_right.of_append_left, ?_, ?_⟩
    · unfold Nat.dist; omega
    · intro y hy
      obtain ⟨s, hs, hy'⟩ := mem_segment_support hw' hy
      exact ⟨p1.length + s, by omega, by omega, hy'⟩
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw', hl1, hl2⟩ := exists_decomp_idx w j i h hi
    subst hu hv
    have hp : (p1.append (p2.append p3)).IsPath := hw' ▸ hw
    refine ⟨p2.reverse, hp.of_append_right.of_append_left.reverse, ?_, ?_⟩
    · rw [Walk.length_reverse]; unfold Nat.dist; omega
    · intro y hy
      rw [Walk.support_reverse, List.mem_reverse] at hy
      obtain ⟨s, hs, hy'⟩ := mem_segment_support hw' hy
      exact ⟨p1.length + s, by omega, by omega, hy'⟩

/-- **A path of length at least two closes a cycle with an edge between its ends.** -/
theorem close_path_cycle {x z : V} (P : G.Walk x z) (hP : P.IsPath) (close : G.Adj z x)
    (long : 2 ≤ P.length) :
    ∃ (c : V) (cyc : G.Walk c c), cyc.IsCycle ∧ cyc.length = P.length + 1 := by
  obtain ⟨cyc, cc, cl⟩ := BlobCycles.chain_cycle 0 (fun _ => x) (fun _ => z) (fun _ => P)
    (fun _ => hP)
    (fun i j hij => absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij) (fun i => i.elim0)
    close (by simpa using long)
  exact ⟨x, cyc, cc, by simpa using cl⟩

end Segment

/-! ## (a) Attachment of a route to a path -/

section Attach

variable {V : Type u} {G : SimpleGraph V}

/-- **(a) The attachment cycle.** -/
theorem walk_attach_cycle {a b x y : V} (w : G.Walk a b) (hw : w.IsPath) {i j : ℕ}
    (hi : i ≤ w.length) (hj : j ≤ w.length) (r : G.Walk x y) (hr : r.IsPath)
    (disj : ∀ v ∈ r.support, ∀ k, min i j ≤ k → k ≤ max i j → v ≠ w.getVert k)
    (hx : G.Adj (w.getVert i) x) (hy : G.Adj y (w.getVert j)) (ne : i ≠ j ∨ x ≠ y) :
    ∃ (c : V) (cyc : G.Walk c c), cyc.IsCycle ∧ cyc.length = r.length + Nat.dist i j + 2 := by
  obtain ⟨s, hs, sl, smem⟩ := seg_path w hw j i hj hi
  have hP : (r.append (Walk.cons hy s)).IsPath := by
    refine BlobCycles.append_cons_isPath r hy s hr hs (fun v hv hv' => ?_)
    obtain ⟨k, k1, k2, rfl⟩ := smem v hv'
    exact disj _ hv k (by rw [min_comm]; exact k1) (by rw [max_comm]; exact k2) rfl
  have rl : i ≠ j → 1 ≤ Nat.dist j i := fun h => by unfold Nat.dist; omega
  have xl : x ≠ y → 1 ≤ r.length := fun h => by
    by_contra h0
    exact h (Walk.eq_of_length_eq_zero (p := r) (by omega))
  obtain ⟨c, cyc, cc, cl⟩ := close_path_cycle (r.append (Walk.cons hy s)) hP hx (by
    simp only [Walk.length_append, Walk.length_cons, sl]
    rcases ne with h | h
    · have := rl h; omega
    · have := xl h; omega)
  refine ⟨c, cyc, cc, ?_⟩
  rw [cl]
  simp only [Walk.length_append, Walk.length_cons, sl, Nat.dist_comm j i]
  omega

/-- **Every attachment of a route to `w` has an unaccepted cycle length.** -/
def AttachCycles (LengthOK : ℕ → Prop) {a b : V} (w : G.Walk a b) : Prop :=
  ∀ (i j : ℕ) {x y : V} (r : G.Walk x y), i ≤ w.length → j ≤ w.length → r.IsPath →
    (∀ v ∈ r.support, ∀ k, min i j ≤ k → k ≤ max i j → v ≠ w.getVert k) →
    G.Adj (w.getVert i) x → G.Adj y (w.getVert j) → (i ≠ j ∨ x ≠ y) →
    ¬ LengthOK (r.length + Nat.dist i j + 2)

theorem attachCycles_of {LengthOK : ℕ → Prop} {a b : V} {w : G.Walk a b} (hw : w.IsPath)
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    AttachCycles LengthOK w := by
  intro i j x y r hi hj hr disj hx hy ne ok
  obtain ⟨c, cyc, cc, cl⟩ := walk_attach_cycle w hw hi hj r hr disj hx hy ne
  exact avoids ⟨c, cyc, cc, cl ▸ ok⟩

end Attach

/-! ## (b) Chains between two paths -/

section Chain

variable {V : Type u} {G : SimpleGraph V}

/-- **(b) The chain cycle through two paths.** -/
theorem walk_pair_cycle {a1 b1 a2 b2 x y x' y' : V} (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2)
    (hw1 : w1.IsPath) (hw2 : w2.IsPath) {i i' j j' : ℕ} (hi : i ≤ w1.length)
    (hi' : i' ≤ w1.length) (hj : j ≤ w2.length) (hj' : j' ≤ w2.length)
    (r : G.Walk x y) (r' : G.Walk x' y') (hr : r.IsPath) (hr' : r'.IsPath)
    (seg : ∀ s t, min i i' ≤ s → s ≤ max i i' → min j j' ≤ t → t ≤ max j j' →
      w1.getVert s ≠ w2.getVert t)
    (rr : ∀ v ∈ r.support, v ∉ r'.support)
    (rw : ∀ v ∈ r.support, v ∉ w1.support ∧ v ∉ w2.support)
    (rw' : ∀ v ∈ r'.support, v ∉ w1.support ∧ v ∉ w2.support)
    (e1 : G.Adj (w1.getVert i) x) (e2 : G.Adj y (w2.getVert j))
    (e3 : G.Adj (w2.getVert j') x') (e4 : G.Adj y' (w1.getVert i')) :
    ∃ (c : V) (cyc : G.Walk c c), cyc.IsCycle ∧
      cyc.length = r.length + r'.length + Nat.dist i i' + Nat.dist j j' + 4 := by
  obtain ⟨s1, hs1, l1, m1⟩ := seg_path w1 hw1 i' i hi' hi
  obtain ⟨s2, hs2, l2, m2⟩ := seg_path w2 hw2 j j' hj hj'
  have Q1p : (r'.append (Walk.cons e4 s1)).IsPath :=
    BlobCycles.append_cons_isPath r' e4 s1 hr' hs1 (fun v hv hv' => by
      obtain ⟨k, -, -, rfl⟩ := m1 v hv'
      exact (rw' _ hv).1 (Walk.getVert_mem_support _ _))
  have Q2p : (s2.append (Walk.cons e3 (r'.append (Walk.cons e4 s1)))).IsPath :=
    BlobCycles.append_cons_isPath s2 e3 _ hs2 Q1p (fun v hv hv' => by
      obtain ⟨t, t1, t2, rfl⟩ := m2 v hv
      rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hv'
      rcases hv' with h | h | h
      · exact (rw' _ h).2 (Walk.getVert_mem_support _ _)
      · exact (rw' y' (Walk.end_mem_support r')).2 (h ▸ Walk.getVert_mem_support w2 t)
      · obtain ⟨k, k1, k2, hk⟩ := m1 _ h
        exact seg k t (by rw [min_comm]; exact k1) (by rw [max_comm]; exact k2) t1 t2 hk.symm)
  have Pp : (r.append (Walk.cons e2 (s2.append (Walk.cons e3
      (r'.append (Walk.cons e4 s1)))))).IsPath :=
    BlobCycles.append_cons_isPath r e2 _ hr Q2p (fun v hv hv' => by
      rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
        Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hv'
      rcases hv' with h | h | h | h | h
      · obtain ⟨t, -, -, rfl⟩ := m2 _ h
        exact (rw _ hv).2 (Walk.getVert_mem_support _ _)
      · rw [h] at hv
        exact (rw _ hv).2 (Walk.getVert_mem_support _ _)
      · exact rr v hv h
      · rw [h] at hv
        exact rr y' hv (Walk.end_mem_support r')
      · obtain ⟨k, -, -, rfl⟩ := m1 _ h
        exact (rw _ hv).1 (Walk.getVert_mem_support _ _))
  obtain ⟨c, cyc, cc, cl⟩ := close_path_cycle (r.append (Walk.cons e2 (s2.append
      (Walk.cons e3 (r'.append (Walk.cons e4 s1)))))) Pp e1 (by
    simp only [Walk.length_append, Walk.length_cons]; omega)
  refine ⟨c, cyc, cc, ?_⟩
  rw [cl]
  simp only [Walk.length_append, Walk.length_cons, l1, l2, Nat.dist_comm i' i]
  omega

/-- **Every chain through two paths has an unaccepted cycle length.** -/
def ChainCycles (LengthOK : ℕ → Prop) {a1 b1 a2 b2 : V} (w1 : G.Walk a1 b1)
    (w2 : G.Walk a2 b2) : Prop :=
  ∀ (i i' j j' : ℕ) {x y x' y' : V} (r : G.Walk x y) (r' : G.Walk x' y'),
    i ≤ w1.length → i' ≤ w1.length → j ≤ w2.length → j' ≤ w2.length →
    r.IsPath → r'.IsPath →
    (∀ s t, min i i' ≤ s → s ≤ max i i' → min j j' ≤ t → t ≤ max j j' →
      w1.getVert s ≠ w2.getVert t) →
    (∀ v ∈ r.support, v ∉ r'.support) →
    (∀ v ∈ r.support, v ∉ w1.support ∧ v ∉ w2.support) →
    (∀ v ∈ r'.support, v ∉ w1.support ∧ v ∉ w2.support) →
    G.Adj (w1.getVert i) x → G.Adj y (w2.getVert j) →
    G.Adj (w2.getVert j') x' → G.Adj y' (w1.getVert i') →
    ¬ LengthOK (r.length + r'.length + Nat.dist i i' + Nat.dist j j' + 4)

theorem chainCycles_of {LengthOK : ℕ → Prop} {a1 b1 a2 b2 : V} {w1 : G.Walk a1 b1}
    {w2 : G.Walk a2 b2} (hw1 : w1.IsPath) (hw2 : w2.IsPath)
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    ChainCycles LengthOK w1 w2 := by
  intro i i' j j' x y x' y' r r' hi hi' hj hj' hr hr' seg rr rw rw' e1 e2 e3 e4 ok
  obtain ⟨c, cyc, cc, cl⟩ :=
    walk_pair_cycle w1 w2 hw1 hw2 hi hi' hj hj' r r' hr hr' seg rr rw rw' e1 e2 e3 e4
  exact avoids ⟨c, cyc, cc, cl ▸ ok⟩

end Chain

/-! ## (c) Separation at a cut vertex -/

section Separation

variable {V : Type u} {G : SimpleGraph V}

/-- `u` and `w` are joined by a walk avoiding `v`. -/
def JoinedAvoiding (G : SimpleGraph V) (v u w : V) : Prop :=
  ∃ p : G.Walk u w, v ∉ p.support

theorem JoinedAvoiding.symm {v u w : V} (h : JoinedAvoiding G v u w) :
    JoinedAvoiding G v w u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by rw [Walk.support_reverse, List.mem_reverse]; exact hp⟩

theorem JoinedAvoiding.trans {v u w z : V} (h : JoinedAvoiding G v u w)
    (h' : JoinedAvoiding G v w z) : JoinedAvoiding G v u z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨p.append q, by rw [Walk.mem_support_append_iff]; tauto⟩

/-- **Every vertex other than `v` reaches a neighbour of `v` avoiding `v`.** -/
theorem reach_nbr {u v : V} (p : G.Walk u v) :
    u ≠ v → ∃ y, G.Adj v y ∧ JoinedAvoiding G v u y := by
  induction p with
  | nil => intro h; exact absurd rfl h
  | @cons u x v h p ih =>
    intro huv
    by_cases hx : x = v
    · subst hx
      exact ⟨u, h.symm, Walk.nil, by simpa [eq_comm] using huv⟩
    · obtain ⟨y, hy, q, hq⟩ := ih hx
      refine ⟨y, hy, Walk.cons h q, ?_⟩
      rw [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun e => huv e.symm, hq⟩

/-- **(c) Separation at a cut vertex.** -/
theorem cut_separates {v l r : V} (conn : ∀ a b : V, G.Reachable a b) (hl : l ≠ v) (hr : r ≠ v)
    (cut : ¬ JoinedAvoiding G v l r) (A B : Set V) (nbr : ∀ y, G.Adj v y → y ∈ A ∨ y ∈ B)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a ≠ v → a' ≠ v → JoinedAvoiding G v a a')
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b ≠ v → b' ≠ v → JoinedAvoiding G v b b') :
    (∀ a ∈ A, ∀ b ∈ B, a ≠ v → b ≠ v → ¬ JoinedAvoiding G v a b) ∧
      (∃ a ∈ A, G.Adj v a) ∧ (∃ b ∈ B, G.Adj v b) := by
  obtain ⟨pl⟩ := conn l v
  obtain ⟨pr⟩ := conn r v
  obtain ⟨yl, al, jl⟩ := reach_nbr pl hl
  obtain ⟨yr, ar, jr⟩ := reach_nbr pr hr
  have yl' : yl ≠ v := fun e => G.loopless.irrefl v (e ▸ al)
  have yr' : yr ≠ v := fun e => G.loopless.irrefl v (e ▸ ar)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb av bv jab
    apply cut
    rcases nbr yl al with hyl | hyl <;> rcases nbr yr ar with hyr | hyr
    · exact jl.trans ((hA yl hyl yr hyr yl' yr').trans jr.symm)
    · exact jl.trans ((hA yl hyl a ha yl' av).trans
        (jab.trans ((hB b hb yr hyr bv yr').trans jr.symm)))
    · exact jl.trans ((hB yl hyl b hb yl' bv).trans
        (jab.symm.trans ((hA a ha yr hyr av yr').trans jr.symm)))
    · exact jl.trans ((hB yl hyl yr hyr yl' yr').trans jr.symm)
  · by_contra none
    push Not at none
    have gl := (nbr yl al).resolve_left (fun m => none yl m al)
    have gr := (nbr yr ar).resolve_left (fun m => none yr m ar)
    exact cut (jl.trans ((hB yl gl yr gr yl' yr').trans jr.symm))
  · by_contra none
    push Not at none
    have gl := (nbr yl al).resolve_right (fun m => none yl m al)
    have gr := (nbr yr ar).resolve_right (fun m => none yr m ar)
    exact cut (jl.trans ((hA yl gl yr gr yl' yr').trans jr.symm))

end Separation

/-! ## Counts -/

section Counts

variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **An interior vertex of degree `≥ 3` of a shortest path avoiding its end edge has a
neighbour off the path**: its only neighbours on the path are its two path neighbours. -/
theorem interior_nbr_off {a b : V} {w : G.Walk a b} (hp : w.IsPath)
    (det : GeodesicDetours s(a, b) w) {k : ℕ} (h0 : 0 < k) (hk : k < w.length)
    (deg : 3 ≤ G.degree (w.getVert k)) : ∃ y, G.Adj (w.getVert k) y ∧ y ∉ w.support := by
  by_contra none
  push Not at none
  obtain ⟨na, nb⟩ := ends_ne hp h0 hk
  have sub : G.neighborFinset (w.getVert k) ⊆ {w.getVert (k - 1), w.getVert (k + 1)} := by
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 (none y hy)
    have hne : j ≠ k := by
      rintro rfl
      exact G.loopless.irrefl _ hy
    let r : G.Walk (w.getVert k) (w.getVert j) := Walk.cons hy .nil
    have hr : ∀ ε ∈ r.edges, ε ≠ s(a, b) := by
      intro ε hε
      simp only [r, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hε
      rw [hε]
      intro e
      rw [Sym2.eq_iff] at e
      rcases e with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact na h1
      · exact nb h1
    have := idx_dist_le det (le_of_lt hk) hj r hr
    simp only [r, Walk.length_cons, Walk.length_nil] at this
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left; congr 1; omega
    · right; congr 1; omega
  have := Finset.card_le_card sub
  rw [card_neighborFinset_eq_degree] at this
  have := Finset.card_le_two (a := w.getVert (k - 1)) (b := w.getVert (k + 1))
  omega

/-- **The interior of a path is at most `|Y| · D`** when every interior vertex has a neighbour
in `Y` and every vertex of `Y` has degree at most `D`. -/
theorem interior_le {a b : V} {w : G.Walk a b} (hp : w.IsPath) (Y : Finset V) (D : ℕ)
    (hY : ∀ k, 0 < k → k < w.length → ∃ y ∈ Y, G.Adj (w.getVert k) y)
    (deg : ∀ y ∈ Y, G.degree y ≤ D) : w.length - 1 ≤ Y.card * D := by
  have sub : (Finset.Ioo 0 w.length).image w.getVert ⊆ Y.biUnion (fun y => G.neighborFinset y) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨h0, hl⟩ := Finset.mem_Ioo.1 hk
    obtain ⟨y, hy, adj⟩ := hY k h0 hl
    exact Finset.mem_biUnion.2 ⟨y, hy, (mem_neighborFinset _ _ _).2 adj.symm⟩
  have inj : Set.InjOn w.getVert (Finset.Ioo 0 w.length : Set ℕ) := by
    intro s hs t ht e
    have hs' := Finset.mem_Ioo.1 hs
    have ht' := Finset.mem_Ioo.1 ht
    exact getVert_inj hp (by omega) (by omega) e
  have c1 := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj, Nat.card_Ioo] at c1
  have c2 := Finset.card_biUnion_le (s := Y) (t := fun y => G.neighborFinset y)
  have c3 : ∑ y ∈ Y, (G.neighborFinset y).card ≤ Y.card * D := by
    have := Finset.sum_le_card_nsmul Y (fun y => (G.neighborFinset y).card) D
      (fun y hy => by rw [card_neighborFinset_eq_degree]; exact deg y hy)
    simpa using this
  omega

/-- **A set each of whose vertices has a cubic neighbour in `T` has at most `3|T|`
elements.** -/
theorem card_le_of_cubic_cover (S T : Finset V)
    (hS : ∀ v ∈ S, ∃ t ∈ T, G.Adj v t ∧ G.degree t = 3) : S.card ≤ 3 * T.card := by
  have sub : S ⊆ (T.filter fun t => G.degree t = 3).biUnion (fun y => G.neighborFinset y) := by
    intro v hv
    obtain ⟨t, ht, adj, d⟩ := hS v hv
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨ht, d⟩,
      (mem_neighborFinset _ _ _).2 adj.symm⟩
  have c1 := Finset.card_le_card sub
  have c2 := Finset.card_biUnion_le (s := T.filter fun t => G.degree t = 3)
    (t := fun y => G.neighborFinset y)
  have c3 : ∑ t ∈ T.filter (fun t => G.degree t = 3), (G.neighborFinset t).card ≤
      (T.filter fun t => G.degree t = 3).card * 3 := by
    have := Finset.sum_le_card_nsmul (T.filter fun t => G.degree t = 3)
      (fun t => (G.neighborFinset t).card) 3
      (fun t ht => by
        rw [card_neighborFinset_eq_degree]; exact le_of_eq (Finset.mem_filter.1 ht).2)
    simpa using this
  have c4 := Finset.card_filter_le T (fun t => G.degree t = 3)
  omega

end Counts

end Hypostructure.Graph.WalkAttachment
