import Hypostructure.Graph.ThetaCycles

/-!
# Cycles through the pieces of a remainder (generic)

Vocabulary-free and application-free.  The statements speak about paths and cycles of one
graph `G`; the application instantiates them at the pieces of the remainder of a window
packing and at the placed windows (`Contracts/RouteEight/BlobStructure.lean`).  The module
reuses `PathChords.ear_cycle` (the closing step of a chain) and `Core.DyadicLength`; the
two-path/theta/fan relations of `ThetaCycles`, the route numbers of `DisjointRoutes` and the
two-geodesic geometry of `TwoGeodesics` are not restated.

* **(a) Triangles** (`triangles_disjoint`): two distinct triangles sharing a vertex force a
  `4`-cycle (they share an edge) or a vertex of degree `≥ 4` (they share exactly one vertex).
  In a `4`-cycle-free graph whose shared vertices have degree `≤ 3`, distinct triangles are
  vertex-disjoint.
* **(b) Triangle toggle** (`toggle_one`, `toggle_interval`): a path through an edge `xy`
  whose ends have a common neighbour `z` off the path can replace `xy` by `x z y`.  With
  `t` such toggles on distinct edges (distinct third vertices) every length in
  `[L₀, L₀ + t]` is the length of an `a`–`b` path.
* **(c) Dyadic intervals** (`exists_pow_two_mem`, `powerOfTwo_of_interval`,
  `interval_bound_of_no_pow_two`): for `a ≥ 1` some power of two lies in `[a, 2a)`; an integer
  interval `[a, b]` with `b ≥ 4` and `b + 1 ≥ 2a` contains a power of two `≥ 4` (the small
  cases `a ≤ 2` are covered by `4` itself).  Contrapositive: an interval free of such powers
  has `b < 4` or `b + 1 < 2a`.
* **(d) Chain cycles** (`open_chain`, `chain_cycle`, `blob_chain_cycle`): `k` blocks
  `rᵢ : aᵢ ⇝ bᵢ` (internal paths of the pieces) and `wᵢ : cᵢ ⇝ dᵢ` (window segments), all
  pairwise vertex-disjoint, with exit edges `bᵢ cᵢ`, `dᵢ aᵢ₊₁` and `d_k a₁`, close a simple
  cycle of length `Σ |rᵢ| + Σ |wᵢ| + 2k`.  Hence the lengths realised by the chain contain
  the Minkowski sum of the internal path-length sets shifted by `Σ |wᵢ| + 2k`.
-/

namespace Hypostructure.Graph.BlobCycles

open SimpleGraph
open Hypostructure.Core.DyadicLength

universe u

section Generic

variable {V : Type u} {G : SimpleGraph V}

/-! ## (a) Distinct triangles are vertex-disjoint -/

/-- A triangle: three pairwise adjacent vertices. -/
def IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop :=
  t.card = 3 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b

/-- The graph has no `4`-cycle `a b c d`. -/
def FourCycleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

/-- **(a)** In a `4`-cycle-free graph, two distinct triangles whose common vertices have
degree at most `3` are vertex-disjoint. -/
theorem triangles_disjoint [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (noFour : FourCycleFree G) {s t : Finset V} (hs : IsTriangle G s) (ht : IsTriangle G t)
    (hne : s ≠ t) (deg : ∀ v ∈ s, v ∈ t → G.degree v ≤ 3) : Disjoint s t := by
  by_contra meet
  rw [Finset.not_disjoint_iff] at meet
  obtain ⟨v, hvs, hvt⟩ := meet
  have outside : ∀ {s t : Finset V}, s.card = 3 → t.card = 3 → s ≠ t → ∃ w ∈ s, w ∉ t := by
    intro s t cs ct ne
    by_contra none
    push Not at none
    exact ne (Finset.eq_of_subset_of_card_le none (by omega))
  obtain ⟨w, hws, hwt⟩ := outside hs.1 ht.1 hne
  obtain ⟨w', hw't, hw's⟩ := outside ht.1 hs.1 (Ne.symm hne)
  by_cases second : ∃ x ∈ s, x ∈ t ∧ x ≠ v
  · obtain ⟨x, hxs, hxt, hxv⟩ := second
    refine noFour x w v w' hxv ?_ ?_ ?_ ?_ ?_
    · intro e; exact hwt (e ▸ hw't)
    · exact hs.2 x hxs w hws (fun e => hwt (e ▸ hxt))
    · exact hs.2 w hws v hvs (fun e => hwt (e ▸ hvt))
    · exact ht.2 v hvt w' hw't (fun e => hw's (e ▸ hvs))
    · exact ht.2 w' hw't x hxt (fun e => hw's (e ▸ hxs))
  · push Not at second
    have sub : s.erase v ∪ t.erase v ⊆ G.neighborFinset v := by
      intro x hx
      rw [mem_neighborFinset]
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨xv, xs⟩ := Finset.mem_erase.mp hx
        exact hs.2 v hvs x xs (Ne.symm xv)
      · obtain ⟨xv, xt⟩ := Finset.mem_erase.mp hx
        exact ht.2 v hvt x xt (Ne.symm xv)
    have disj : Disjoint (s.erase v) (t.erase v) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨xv, xs⟩ := Finset.mem_erase.mp hx
      exact xv (second x xs (Finset.mem_erase.mp hx').2)
    have card := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint disj, Finset.card_erase_of_mem hvs,
      Finset.card_erase_of_mem hvt, hs.1, ht.1, card_neighborFinset_eq_degree] at card
    have := deg v hvs hvt
    omega

/-! ## (b) The triangle toggle -/

/-- **(b), one toggle.**  A path `q` through an edge `e` whose two ends are adjacent to a
vertex `z` off `q` has a detour through `z`: a path with the same ends, one edge longer,
whose vertices are those of `q` and `z`, keeping every other edge of `q`. -/
theorem toggle_one {a b z : V} (q : G.Walk a b) (hq : q.IsPath) {e : Sym2 V}
    (he : e ∈ q.edges) (hz : ∀ v ∈ e, G.Adj v z) (hzq : z ∉ q.support) :
    ∃ q' : G.Walk a b, q'.IsPath ∧ q'.length = q.length + 1 ∧
      (∀ v, v ∈ q'.support ↔ v = z ∨ v ∈ q.support) ∧
      ∀ f ∈ q.edges, f ≠ e → f ∈ q'.edges := by
  induction q with
  | nil => simp at he
  | @cons x c y h p ih =>
    have hc := (Walk.cons_isPath_iff h p).1 hq
    have xz : x ≠ z := fun eq => hzq (eq ▸ Walk.start_mem_support _)
    have zp : z ∉ p.support := fun m => hzq (by simp [m])
    rw [Walk.edges_cons, List.mem_cons] at he
    by_cases heq : e = s(x, c)
    · subst heq
      have xzAdj : G.Adj x z := hz x (Sym2.mem_mk_left x c)
      have zcAdj : G.Adj z c := (hz c (Sym2.mem_mk_right x c)).symm
      refine ⟨Walk.cons xzAdj (Walk.cons zcAdj p), ?_, by simp, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
        refine ⟨⟨hc.1, zp⟩, ?_⟩
        simp only [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨xz, hc.2⟩
      · intro v
        simp only [Walk.support_cons, List.mem_cons]
        tauto
      · intro f hf fne
        simp only [Walk.edges_cons, List.mem_cons] at hf ⊢
        rcases hf with hf | hf
        · exact absurd hf fne
        · exact Or.inr (Or.inr hf)
    · have he' : e ∈ p.edges := he.resolve_left heq
      obtain ⟨p', p'path, p'len, p'supp, p'edges⟩ := ih hc.1 he' zp
      refine ⟨Walk.cons h p', ?_, by simp [p'len], ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        refine ⟨p'path, fun m => ?_⟩
        rcases (p'supp x).1 m with m | m
        · exact xz m
        · exact hc.2 m
      · intro v
        simp only [Walk.support_cons, List.mem_cons, p'supp]
        tauto
      · intro f hf fne
        simp only [Walk.edges_cons, List.mem_cons] at hf ⊢
        rcases hf with hf | hf
        · exact Or.inl hf
        · exact Or.inr (p'edges f hf fne)

/-- **(b), all toggles of a subset.**  Toggles on distinct edges (an injective edge
assignment `edge` on `Z`), each third vertex off the path: for every `S ⊆ Z` the toggles of
`S` give a path of length `|p| + |S|`, and the toggles of `Z \ S` are still available. -/
theorem toggle_subset [DecidableEq V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (Z : Finset V) (edge : V → Sym2 V) (inj : Set.InjOn edge Z)
    (mem : ∀ z ∈ Z, edge z ∈ p.edges) (adj : ∀ z ∈ Z, ∀ v ∈ edge z, G.Adj v z)
    (off : ∀ z ∈ Z, z ∉ p.support) :
    ∀ S ⊆ Z, ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + S.card ∧
      (∀ v ∈ q.support, v ∈ p.support ∨ v ∈ S) ∧
      ∀ z ∈ Z, z ∉ S → edge z ∈ q.edges ∧ z ∉ q.support := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨p, hp, by simp, fun v hv => Or.inl hv, fun z hz _ => ⟨mem z hz, off z hz⟩⟩
  | @insert z S zS ih =>
    intro sub
    have zZ : z ∈ Z := sub (Finset.mem_insert_self z S)
    obtain ⟨q, qp, ql, qs, qfree⟩ := ih ((Finset.subset_insert z S).trans sub)
    obtain ⟨qe, qz⟩ := qfree z zZ zS
    obtain ⟨q', q'p, q'l, q's, q'e⟩ := toggle_one q qp qe (adj z zZ) qz
    refine ⟨q', q'p, by rw [q'l, ql, Finset.card_insert_of_notMem zS]; omega, ?_, ?_⟩
    · intro v hv
      rcases (q's v).1 hv with rfl | hv
      · exact Or.inr (Finset.mem_insert_self _ _)
      · rcases qs v hv with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
    · intro w wZ wS
      have wz : w ≠ z := fun e => wS (e ▸ Finset.mem_insert_self z S)
      have wS' : w ∉ S := fun m => wS (Finset.mem_insert_of_mem m)
      obtain ⟨we, wq⟩ := qfree w wZ wS'
      refine ⟨q'e _ we (fun e => wz (inj wZ zZ e)), fun m => ?_⟩
      rcases (q's w).1 m with m | m
      · exact wz m
      · exact wq m

/-- **(b) Triangle toggle interval.**  With `t = |Z|` toggles on distinct edges of a path
`p : a ⇝ b`, each third vertex adjacent to both ends of its edge and off `p`, every length in
`[|p|, |p| + t]` is the length of an `a`–`b` path using only vertices of `p` and `Z`. -/
theorem toggle_interval [DecidableEq V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (Z : Finset V) (edge : V → Sym2 V) (inj : Set.InjOn edge Z)
    (mem : ∀ z ∈ Z, edge z ∈ p.edges) (adj : ∀ z ∈ Z, ∀ v ∈ edge z, G.Adj v z)
    (off : ∀ z ∈ Z, z ∉ p.support) :
    ∀ m ≤ Z.card, ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + m ∧
      ∀ v ∈ q.support, v ∈ p.support ∨ v ∈ Z := by
  intro m hm
  obtain ⟨S, SZ, Scard⟩ := Finset.exists_subset_card_eq hm
  obtain ⟨q, qp, ql, qs, -⟩ := toggle_subset p hp Z edge inj mem adj off S SZ
  refine ⟨q, qp, by rw [ql, Scard], fun v hv => ?_⟩
  rcases qs v hv with h | h
  · exact Or.inl h
  · exact Or.inr (SZ h)

end Generic

/-! ## (c) Dyadic intervals -/

/-- **(c)** For `a ≥ 1` some power of two lies in `[a, 2a)`. -/
theorem exists_pow_two_mem {a : ℕ} (ha : 1 ≤ a) : ∃ k, a ≤ 2 ^ k ∧ 2 ^ k < 2 * a := by
  refine ⟨Nat.log 2 (2 * a - 1), ?_, ?_⟩
  · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2 * a - 1)
    rw [Nat.pow_succ] at h
    omega
  · have h := Nat.pow_log_le_self 2 (x := 2 * a - 1) (by omega)
    omega

/-- **(c), consequence.**  An integer interval `[a, b]` with `b ≥ 4` and `2a ≤ b + 1`
contains a power of two `≥ 4`.  (For `a ≤ 2` it contains `4`; for `a ≥ 3` the power of two
in `[a, 2a)` is at least `4`.) -/
theorem powerOfTwo_of_interval {a b : ℕ} (hb : 4 ≤ b) (hab : 2 * a ≤ b + 1) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ PowerOfTwoLength n := by
  by_cases small : a ≤ 2
  · exact ⟨4, by omega, hb, powerOfTwoLength_four⟩
  · obtain ⟨k, lo, hi⟩ := exists_pow_two_mem (a := a) (by omega)
    refine ⟨2 ^ k, lo, by omega, powerOfTwoLength_of_exists ⟨k, ?_, rfl⟩⟩
    by_contra hk
    interval_cases k <;> simp at lo <;> omega

/-- **(c), the run bound.**  If no integer of `[a, b]` is a power of two `≥ 4`, then
`b < 4` or `b + 1 < 2a`. -/
theorem interval_bound_of_no_pow_two {a b : ℕ}
    (free : ∀ n, a ≤ n → n ≤ b → ¬ PowerOfTwoLength n) : b < 4 ∨ b + 1 < 2 * a := by
  by_contra h
  push Not at h
  obtain ⟨n, lo, hi, pow⟩ := powerOfTwo_of_interval h.1 h.2
  exact free n lo hi pow

/-- **(c), for a family of lengths.**  A family of cycle lengths containing every integer of
`[a, b]`, with `a ≥ 3` and `b ≥ 2a − 1`, contains a power of two `≥ 4`. -/
theorem powerOfTwo_mem_of_interval_subset {S : Set ℕ} {a b : ℕ} (ha : 3 ≤ a)
    (hab : 2 * a ≤ b + 1) (sub : ∀ n, a ≤ n → n ≤ b → n ∈ S) :
    ∃ n ∈ S, PowerOfTwoLength n := by
  obtain ⟨n, lo, hi, pow⟩ := powerOfTwo_of_interval (a := a) (b := b) (by omega) hab
  exact ⟨n, sub n lo hi, pow⟩

section Chain

variable {V : Type u} {G : SimpleGraph V}

/-! ## (d) Chain cycles -/

/-- Two vertex-disjoint paths joined by an edge form a path. -/
theorem append_cons_isPath {x y z w : V} (p : G.Walk x y) (h : G.Adj y z) (q : G.Walk z w)
    (hp : p.IsPath) (hq : q.IsPath) (disj : ∀ v ∈ p.support, v ∉ q.support) :
    (p.append (Walk.cons h q)).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons]
  refine List.nodup_append.2 ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro a ha b hb eab
  subst eab
  exact disj a ha hb

/-- **(d), the open chain.**  `n + 1` pairwise vertex-disjoint paths `P i : s i ⇝ t i`, with
edges `t i — s (i+1)`, concatenate to one path `s 0 ⇝ t n` of length `Σ |P i| + n` through
their vertices only. -/
theorem open_chain : ∀ (n : ℕ) (s t : Fin (n + 1) → V)
    (P : (i : Fin (n + 1)) → G.Walk (s i) (t i)),
    (∀ i, (P i).IsPath) →
    (∀ i j, i ≠ j → ∀ v ∈ (P i).support, v ∉ (P j).support) →
    (∀ i : Fin n, G.Adj (t i.castSucc) (s i.succ)) →
    ∃ W : G.Walk (s 0) (t (Fin.last n)), W.IsPath ∧
      W.length = (∑ i, (P i).length) + n ∧ ∀ v ∈ W.support, ∃ i, v ∈ (P i).support
  | 0, s, t, P, hP, _, _ =>
    ⟨(P 0).copy rfl rfl, by simpa using hP 0, by simp, fun v hv => ⟨0, by simpa using hv⟩⟩
  | n + 1, s, t, P, hP, hdisj, hadj => by
    obtain ⟨W', W'p, W'l, W's⟩ := open_chain n (fun i => s i.castSucc) (fun i => t i.castSucc)
      (fun i => P i.castSucc) (fun i => hP _)
      (fun i j hij => hdisj _ _ (fun e => hij (Fin.castSucc_injective _ e)))
      (fun i => by have h := hadj i.castSucc; rw [Fin.succ_castSucc] at h; exact h)
    have link : G.Adj (t (Fin.last n).castSucc) (s (Fin.last (n + 1))) := by
      have h := hadj (Fin.last n); rw [Fin.succ_last] at h; exact h
    let tail : G.Walk (t (Fin.last n).castSucc) (t (Fin.last (n + 1))) :=
      Walk.cons link (P (Fin.last (n + 1)))
    refine ⟨(W'.append tail).copy (congrArg s Fin.castSucc_zero) rfl, ?_, ?_, ?_⟩
    · rw [Walk.isPath_copy]
      refine append_cons_isPath W' link _ W'p (hP _) ?_
      intro v hv hv'
      obtain ⟨i, hi⟩ := W's v hv
      exact hdisj i.castSucc (Fin.last (n + 1)) (Fin.castSucc_lt_last i).ne v hi hv'
    · simp only [Walk.length_copy, Walk.length_append, tail, Walk.length_cons, W'l,
        Fin.sum_univ_castSucc (f := fun i => (P i).length)]
      omega
    · intro v hv
      simp only [Walk.support_copy, Walk.mem_support_append_iff, tail, Walk.support_cons,
        List.mem_cons] at hv
      rcases hv with hv | hv | hv
      · obtain ⟨i, hi⟩ := W's v hv
        exact ⟨i.castSucc, hi⟩
      · obtain ⟨i, hi⟩ := W's v (hv ▸ Walk.end_mem_support W')
        exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hv⟩

/-- **(d), closing the chain.**  With the closing edge `t n — s 0` and total length
`Σ |P i| + n ≥ 2`, the open chain closes a cycle of length `Σ |P i| + n + 1`. -/
theorem chain_cycle (n : ℕ) (s t : Fin (n + 1) → V)
    (P : (i : Fin (n + 1)) → G.Walk (s i) (t i)) (hP : ∀ i, (P i).IsPath)
    (hdisj : ∀ i j, i ≠ j → ∀ v ∈ (P i).support, v ∉ (P j).support)
    (hadj : ∀ i : Fin n, G.Adj (t i.castSucc) (s i.succ))
    (close : G.Adj (t (Fin.last n)) (s 0)) (long : 2 ≤ (∑ i, (P i).length) + n) :
    ∃ c : G.Walk (s 0) (s 0), c.IsCycle ∧ c.length = (∑ i, (P i).length) + n + 1 := by
  obtain ⟨W, Wp, Wl, -⟩ := open_chain n s t P hP hdisj hadj
  let q : G.Walk (t (Fin.last n)) (s 0) := Walk.cons close Walk.nil
  have qp : q.IsPath := by
    simp only [q, Walk.cons_isPath_iff, Walk.support_nil, List.mem_singleton]
    exact ⟨Walk.IsPath.nil, close.ne⟩
  obtain ⟨c, cc, cl⟩ := PathChords.ear_cycle W q Wp qp
    (fun y _ hy => by
      simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl)
    (by omega) (by simp [q]) (by simp [q]; omega)
  exact ⟨c, cc, by rw [cl, Wl]; simp [q]⟩

/-- **(d) The chain cycle through pieces and windows.**  For `k = n + 1` blocks, internal
paths `r i : a i ⇝ b i`, window segments `w i : c i ⇝ d i`, all pairwise vertex-disjoint,
exit edges `b i — c i`, `d i — a (i+1)` and the closing exit `d k — a 0`, and total length
`Σ (|r i| + |w i|) + 2k ≥ 3`: there is a cycle of length `Σ (|r i| + |w i|) + 2k`.  So every
element of the Minkowski sum of the internal path-length sets, shifted by `Σ |w i| + 2k`, is
the length of a cycle. -/
theorem blob_chain_cycle (n : ℕ) (a b c d : Fin (n + 1) → V)
    (r : (i : Fin (n + 1)) → G.Walk (a i) (b i)) (w : (i : Fin (n + 1)) → G.Walk (c i) (d i))
    (hr : ∀ i, (r i).IsPath) (hw : ∀ i, (w i).IsPath)
    (rr : ∀ i j, i ≠ j → ∀ v ∈ (r i).support, v ∉ (r j).support)
    (ww : ∀ i j, i ≠ j → ∀ v ∈ (w i).support, v ∉ (w j).support)
    (rw' : ∀ i j, ∀ v ∈ (r i).support, v ∉ (w j).support)
    (exitIn : ∀ i, G.Adj (b i) (c i)) (exitOut : ∀ i : Fin n, G.Adj (d i.castSucc) (a i.succ))
    (close : G.Adj (d (Fin.last n)) (a 0))
    (long : 3 ≤ (∑ i, ((r i).length + (w i).length)) + 2 * (n + 1)) :
    ∃ (v : V) (cyc : G.Walk v v), cyc.IsCycle ∧
      cyc.length = (∑ i, ((r i).length + (w i).length)) + 2 * (n + 1) := by
  let P : (i : Fin (n + 1)) → G.Walk (a i) (d i) := fun i =>
    (r i).append (Walk.cons (exitIn i) (w i))
  have Pp : ∀ i, (P i).IsPath := fun i =>
    append_cons_isPath _ _ _ (hr i) (hw i) (fun v hv => rw' i i v hv)
  have Ps : ∀ i v, v ∈ (P i).support ↔ v ∈ (r i).support ∨ v ∈ (w i).support := by
    intro i v
    simp only [P, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inl (by rw [h]; exact Walk.end_mem_support _)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have Pd : ∀ i j, i ≠ j → ∀ v ∈ (P i).support, v ∉ (P j).support := by
    intro i j ij v hv hv'
    rcases (Ps i v).1 hv with h | h <;> rcases (Ps j v).1 hv' with h' | h'
    · exact rr i j ij v h h'
    · exact rw' i j v h h'
    · exact rw' j i v h' h
    · exact ww i j ij v h h'
  have Pl : ∀ i, (P i).length = (r i).length + (w i).length + 1 := by
    intro i
    simp only [P, Walk.length_append, Walk.length_cons]
    omega
  have sumP : (∑ i, (P i).length) = (∑ i, ((r i).length + (w i).length)) + (n + 1) := by
    simp only [Pl, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  obtain ⟨cyc, cc, cl⟩ := chain_cycle n a d P Pp Pd exitOut close (by rw [sumP]; omega)
  exact ⟨a 0, cyc, cc, by rw [cl, sumP]; ring⟩

end Chain

end Hypostructure.Graph.BlobCycles
