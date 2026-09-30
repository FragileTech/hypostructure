import Hypostructure.Graph.DensityCert.Transport

/-!
# Density certificate: auxiliary lemmas for the block decomposition

Generic facts used by `DensityCert.Blocks`:

* reachability inside a finset (`ReachIn`): symmetry, transitivity, monotonicity,
  membership, closed sets, and the passage to/from Mathlib walks via `resG`;
* concatenation of induced paths across a single edge, and existence of an
  induced path between two vertices joined inside a finset;
* witnesses for `lamIn` and `LIn`;
* `dIn` as a degree sum, its behaviour under disjoint unions.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

section Reach

variable {V : Type*} {G : SimpleGraph V}

theorem reachIn_trans {W : Finset V} {a b c : V} (h1 : ReachIn G W a b)
    (h2 : ReachIn G W b c) : ReachIn G W a c :=
  Relation.ReflTransGen.trans h1 h2

theorem reachIn_mem_left {W : Finset V} {a b : V} (h : ReachIn G W a b) (hab : a ≠ b) :
    a ∈ W := by
  rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, hc, _⟩
  · exact absurd h1 hab
  · exact hc.1

theorem reachIn_mem_right {W : Finset V} {a b : V} (h : ReachIn G W a b) (hab : a ≠ b) :
    b ∈ W := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, _, hc⟩
  · exact absurd h1.symm hab
  · exact hc.2.1

theorem reachIn_mem {W : Finset V} {a b : V} (h : ReachIn G W a b) (ha : a ∈ W) : b ∈ W := by
  by_cases hab : a = b
  · exact hab ▸ ha
  · exact reachIn_mem_right h hab

theorem reachIn_closed {W S : Finset V} (hS : ∀ x ∈ S, ∀ y ∈ W, G.Adj x y → y ∈ S) {a b : V}
    (h : ReachIn G W a b) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ h' ih => exact hS _ ih _ h'.2.1 h'.2.2

/-- Leaving a vertex `v`: if `v ≠ u` are joined inside `S`, then some neighbour `a ∈ S`
of `v` is joined to `u` inside `S \ {v}`. -/
theorem reachIn_first_step [DecidableEq V] {S : Finset V} {v u : V} (h : ReachIn G S v u)
    (hvu : v ≠ u) :
    ∃ a ∈ S, G.Adj v a ∧ ReachIn G (S.erase v) a u := by
  have hu : u ∈ S := reachIn_mem_right h hvu
  have key : ∀ x, ReachIn G S x u →
      (ReachIn G (S.erase v) x u ∨ ∃ a ∈ S, G.Adj v a ∧ ReachIn G (S.erase v) a u) := by
    intro x hx
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl => exact Or.inl .refl
    | @head x y hxy _ ih =>
      rcases ih with ih | ih
      · by_cases hyv : y = v
        · subst hyv
          exact absurd (reachIn_mem_left ih hvu) (by simp)
        · by_cases hxv : x = v
          · subst hxv
            exact Or.inr ⟨y, hxy.2.1, hxy.2.2, ih⟩
          · exact Or.inl (Relation.ReflTransGen.head
              ⟨mem_erase.2 ⟨hxv, hxy.1⟩, mem_erase.2 ⟨hyv, hxy.2.1⟩, hxy.2.2⟩ ih)
      · exact Or.inr ih
  rcases key v h with h' | h'
  · exact absurd (reachIn_mem_left h' hvu) (by simp)
  · exact h'

/-- The graph `G[W]` as a graph on the whole vertex type (vertices outside `W`
isolated). -/
def resG (G : SimpleGraph V) (W : Finset V) : SimpleGraph V where
  Adj u v := u ∈ W ∧ v ∈ W ∧ G.Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.2.2⟩

@[simp] theorem resG_adj {W : Finset V} {u v : V} :
    (resG G W).Adj u v ↔ u ∈ W ∧ v ∈ W ∧ G.Adj u v := Iff.rfl

theorem reachIn_iff_reachable {W : Finset V} {a b : V} :
    ReachIn G W a b ↔ (resG G W).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  rfl

/-- A walk whose vertices lie in `S` and whose steps are `G`-edges gives
reachability inside `S`. -/
theorem walk_reachIn {K : SimpleGraph V} (hK : ∀ x y, K.Adj x y → G.Adj x y) {S : Finset V}
    {a b : V} (p : K.Walk a b) (hS : ∀ x ∈ p.support, x ∈ S) : ReachIn G S a b := by
  induction p with
  | nil => exact .refl
  | cons h p ih =>
    refine Relation.ReflTransGen.head ⟨hS _ (by simp), hS _ (by simp [p.start_mem_support]),
      hK _ _ h⟩ (ih fun x hx => hS x (by simp [hx]))

/-- Every vertex of a walk is reachable from its start through steps along edges of
the walk. -/
theorem walk_support_rtg {K : SimpleGraph V} {R : V → V → Prop} {a b : V} (p : K.Walk a b)
    (hE : ∀ x y, s(x, y) ∈ p.edges → K.Adj x y → R x y) :
    ∀ x ∈ p.support, Relation.ReflTransGen R a x := by
  induction p with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact .refl
  | cons h p ih =>
    intro x hx
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact .refl
    · exact Relation.ReflTransGen.head (hE _ _ (by simp) h)
        (ih (fun x y hxy hK => hE x y (by simp [hxy]) hK) x hx)

end Reach

section Paths

variable {V : Type*} {G : SimpleGraph V}

theorem getElem_last_of_getLast? {l : List V} {a : V} (h : l.getLast? = some a) :
    ∃ hl : 0 < l.length, l[l.length - 1] = a := by
  rw [List.getLast?_eq_getElem?] at h
  have hl : l.length - 1 < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  refine ⟨by omega, ?_⟩
  rw [List.getElem?_eq_getElem hl] at h
  exact Option.some.inj h

theorem getElem_zero_of_head? {l : List V} {a : V} (h : l.head? = some a) :
    ∃ hl : 0 < l.length, l[0] = a := by
  rw [List.head?_eq_getElem?] at h
  have hl : 0 < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  refine ⟨hl, ?_⟩
  rw [List.getElem?_eq_getElem hl] at h
  exact Option.some.inj h

/-- Concatenation of two induced paths across a single edge `a – b` (`a` the last
vertex of `l1`, `b` the first of `l2`), provided that edge is the only one between
them and they are disjoint. -/
theorem IsIndPath.append' {l1 l2 : List V} (h1 : IsIndPath G l1) (h2 : IsIndPath G l2)
    {a b : V} (ha : l1.getLast? = some a) (hb : l2.head? = some b) (hab : G.Adj a b)
    (hd : ∀ x ∈ l1, x ∉ l2)
    (hx : ∀ x ∈ l1, ∀ y ∈ l2, G.Adj x y → x = a ∧ y = b) : IsIndPath G (l1 ++ l2) := by
  obtain ⟨hn1, ha'⟩ := getElem_last_of_getLast? ha
  obtain ⟨hn2, hb'⟩ := getElem_zero_of_head? hb
  have cross : ∀ i (hi : i < l1.length) k (hk : k < l2.length),
      (G.Adj l1[i] l2[k] ↔ (i + 1 = l1.length ∧ k = 0)) := by
    intro i hi k hk
    constructor
    · intro h
      obtain ⟨e1, e2⟩ := hx _ (List.getElem_mem hi) _ (List.getElem_mem hk) h
      rw [← ha'] at e1
      rw [← hb'] at e2
      have := (h1.1.getElem_inj_iff).1 e1
      have := (h2.1.getElem_inj_iff).1 e2
      omega
    · rintro ⟨hi1, rfl⟩
      obtain rfl : i = l1.length - 1 := by omega
      rw [ha', hb']
      exact hab
  refine ⟨List.nodup_append.2 ⟨h1.1, h2.1, fun x hx1 y hy2 hxy => hd x hx1 (hxy ▸ hy2)⟩,
    fun i j hi hj => ?_⟩
  simp only [List.length_append] at hi hj
  simp only [List.getElem_append]
  split_ifs with hi1 hj1 hj1
  · exact h1.2 i j hi1 hj1
  · rw [cross i hi1 (j - l1.length) (by omega)]
    omega
  · rw [G.adj_comm, cross j hj1 (i - l1.length) (by omega)]
    omega
  · rw [h2.2 _ _ (by omega) (by omega)]
    omega

/-- A walk inside `S` from `a ∈ S` to `b` can be replaced by an induced path of
`G[S]` from `a` to `b`. -/
theorem exists_indPath {S : Finset V} {a b : V} (ha : a ∈ S) (h : ReachIn G S a b) :
    ∃ l, IsIndPath G l ∧ (∀ x ∈ l, x ∈ S) ∧ l.head? = some a ∧ l.getLast? = some b := by
  classical
  induction h with
  | refl => exact ⟨[a], IsIndPath.singleton a, by simpa using ha, rfl, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, hl, hlS, hh, ht⟩ := ih
    obtain ⟨hn, hlast⟩ := getElem_last_of_getLast? ht
    obtain ⟨_, hhead⟩ := getElem_zero_of_head? hh
    by_cases hc : c ∈ l
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      refine ⟨l.take (k + 1), hl.take _, fun x hx => hlS x (List.mem_of_mem_take hx), ?_, ?_⟩
      · rw [List.head?_eq_getElem?, List.getElem?_take]
        simp only [show 0 < k + 1 by omega, if_true]
        rw [List.getElem?_eq_getElem hn, hhead]
      · rw [List.getLast?_eq_getElem?, List.length_take, List.getElem?_take]
        simp only [show min (k + 1) l.length - 1 < k + 1 by omega, if_true]
        rw [show min (k + 1) l.length - 1 = k by omega, List.getElem?_eq_getElem hk]
    · have hex : ∃ j, ∃ hj : j < l.length, G.Adj l[j] c :=
        ⟨l.length - 1, by omega, by rw [hlast]; exact hbc.2.2⟩
      obtain ⟨hi, hadj⟩ := Nat.find_spec hex
      set i := Nat.find hex with hi_def
      have hmin : ∀ j (hj : j < l.length), G.Adj l[j] c → i ≤ j := fun j hj h =>
        Nat.find_min' hex ⟨hj, h⟩
      refine ⟨l.take (i + 1) ++ [c], ?_, ?_, ?_, ?_⟩
      · refine IsIndPath.append' (hl.take _) (IsIndPath.singleton c) (a := l[i]) (b := c)
          ?_ rfl hadj ?_ ?_
        · rw [List.getLast?_eq_getElem?, List.length_take, List.getElem?_take]
          simp only [show min (i + 1) l.length - 1 < i + 1 by omega, if_true]
          rw [show min (i + 1) l.length - 1 = i by omega, List.getElem?_eq_getElem hi]
        · intro x hx hxc
          simp only [List.mem_singleton] at hxc
          exact hc (hxc ▸ List.mem_of_mem_take hx)
        · intro x hx y hy hxy
          simp only [List.mem_singleton] at hy
          subst hy
          obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hx
          have := hmin j (by omega) hxy
          obtain rfl : j = i := by omega
          exact ⟨rfl, rfl⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hlS x (List.mem_of_mem_take hx)
        · simp only [List.mem_singleton] at hx
          exact hx ▸ hbc.2.1
      · rw [List.head?_append, List.head?_eq_getElem?, List.getElem?_take]
        simp only [show 0 < i + 1 by omega, if_true]
        rw [List.getElem?_eq_getElem hn, hhead]
        rfl
      · simp

end Paths

section Lam

variable {V : Type*} {G : SimpleGraph V}

theorem length_le_card {W : Finset V} {l : List V} (hn : l.Nodup) (hl : ∀ x ∈ l, x ∈ W) :
    l.length ≤ W.card := by
  classical
  rw [← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card (fun x hx => hl x (List.mem_toFinset.1 hx))

theorem le_lamIn {W : Finset V} {v : V} {l : List V} (hp : IsIndPath G l)
    (hl : ∀ x ∈ l, x ∈ W) (hh : l.head? = some v) : l.length ≤ lamIn G W v := by
  classical
  unfold lamIn
  refine Nat.le_findGreatest (length_le_card hp.1 hl) ?_
  exact ⟨l, hp, hl, hh, rfl⟩

theorem exists_lamIn {W : Finset V} {v : V} (hv : v ∈ W) :
    ∃ l, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some v ∧ l.length = lamIn G W v := by
  classical
  unfold lamIn
  exact Nat.findGreatest_spec
    (P := fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some v ∧
      l.length = k) (m := 1) (Finset.card_pos.2 ⟨v, hv⟩)
    ⟨[v], IsIndPath.singleton v, by simpa using hv, rfl, rfl⟩

theorem le_LIn {W : Finset V} {u v : V} {l : List V} (hp : IsIndPath G l)
    (hl : ∀ x ∈ l, x ∈ W) (hh : l.head? = some u) (ht : l.getLast? = some v) :
    l.length ≤ LIn G W u v := by
  classical
  unfold LIn
  refine Nat.le_findGreatest (length_le_card hp.1 hl) ?_
  exact ⟨l, hp, hl, hh, ht, rfl⟩

theorem exists_LIn {W : Finset V} {u v : V} (hu : u ∈ W) (h : ReachIn G W u v) :
    ∃ l, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some u ∧ l.getLast? = some v ∧
      l.length = LIn G W u v := by
  classical
  obtain ⟨l, hp, hl, hh, ht⟩ := exists_indPath hu h
  unfold LIn
  exact Nat.findGreatest_spec
    (P := fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some u ∧
      l.getLast? = some v ∧ l.length = k) (m := l.length) (length_le_card hp.1 hl)
    ⟨l, hp, hl, hh, ht, rfl⟩

theorem lamIn_mono {A W : Finset V} (hAW : A ⊆ W) {v : V} : lamIn G A v ≤ lamIn G W v := by
  by_cases hv : v ∈ A
  · obtain ⟨l, hp, hl, hh, hlen⟩ := exists_lamIn (G := G) hv
    rw [← hlen]
    exact le_lamIn hp (fun x hx => hAW (hl x hx)) hh
  · have : lamIn G A v = 0 := by
      classical
      by_contra h0
      obtain ⟨l, _, hl, hh, _⟩ := Nat.findGreatest_of_ne_zero
        (P := fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ A) ∧ l.head? = some v ∧
          l.length = k) (n := A.card) (m := lamIn G A v) rfl h0
      obtain ⟨hl0, hv0⟩ := getElem_zero_of_head? hh
      exact hv (hv0 ▸ hl _ (List.getElem_mem hl0))
    omega

theorem lamIn_le_of_adm {W : Finset V} (ha : AdmIn G W) (v : V) : lamIn G W v ≤ 12 := by
  classical
  by_contra h
  obtain ⟨l, hp, hl, _, hlen⟩ := Nat.findGreatest_of_ne_zero
    (P := fun k => ∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ W) ∧ l.head? = some v ∧
      l.length = k) (n := W.card) (m := lamIn G W v) rfl (by omega)
  have := ha.length_le hl hp
  omega

theorem LIn_self_eq {W : Finset V} {v : V} (hv : v ∈ W) : LIn G W v v = 1 := by
  classical
  unfold LIn
  rw [Nat.findGreatest_eq_iff]
  refine ⟨Finset.card_pos.2 ⟨v, hv⟩, fun _ => ⟨[v], IsIndPath.singleton v, by simpa using hv,
    rfl, rfl, rfl⟩, fun n hn _ => ?_⟩
  rintro ⟨l, hp, _, hh, ht, rfl⟩
  obtain ⟨h0, e0⟩ := getElem_zero_of_head? hh
  obtain ⟨_, e1⟩ := getElem_last_of_getLast? ht
  have := (hp.1.getElem_inj_iff (i := 0) (j := l.length - 1)).1 (e0.trans e1.symm)
  omega

/-- P2 across one edge: two induced paths ending/starting at the ends of the only
edge between disjoint `A` and `C`. -/
theorem lam_add_lam_le {W A C : Finset V} (ha : AdmIn G W) (hA : A ⊆ W) (hC : C ⊆ W)
    (hd : Disjoint A C) {a c : V} (haA : a ∈ A) (hcC : c ∈ C) (hac : G.Adj a c)
    (hu : ∀ u ∈ C, ∀ v ∈ A, G.Adj u v → u = c ∧ v = a) :
    lamIn G A a + lamIn G C c ≤ 12 := by
  obtain ⟨l1, hp1, hl1, hh1, hlen1⟩ := exists_lamIn (G := G) haA
  obtain ⟨l2, hp2, hl2, hh2, hlen2⟩ := exists_lamIn (G := G) hcC
  have hp : IsIndPath G (l1.reverse ++ l2) := by
    refine IsIndPath.append' hp1.reverse hp2 (a := a) (b := c) (by rw [List.getLast?_reverse, hh1])
      hh2 hac ?_ ?_
    · intro x hx hx2
      exact Finset.disjoint_left.1 hd (hl1 x (List.mem_reverse.1 hx)) (hl2 x hx2)
    · intro x hx y hy hxy
      obtain ⟨h1, h2⟩ := hu y (hl2 y hy) x (hl1 x (List.mem_reverse.1 hx)) hxy.symm
      exact ⟨h2, h1⟩
  have := ha.length_le (fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact hA (hl1 x (List.mem_reverse.1 hx))
    · exact hC (hl2 x hx)) hp
  simp only [List.length_append, List.length_reverse] at this
  omega

/-- P2 through a middle piece `B`: `A – B – C` joined by the edges `a – p` and `q – c`. -/
theorem lam_L_lam_le [DecidableEq V] {W A B C : Finset V} (ha : AdmIn G W) (hA : A ⊆ W) (hB : B ⊆ W)
    (hC : C ⊆ W) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {a p q c : V} (haA : a ∈ A) (hpB : p ∈ B) (hcC : c ∈ C) (hap : G.Adj a p)
    (hqc : G.Adj q c) (huA : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u = a ∧ v = p)
    (huC : ∀ u ∈ C, ∀ v ∈ A ∪ B, G.Adj u v → u = c ∧ v = q) (hpq : ReachIn G B p q) :
    lamIn G A a + LIn G B p q + lamIn G C c ≤ 12 := by
  obtain ⟨l1, hp1, hl1, hh1, hlen1⟩ := exists_lamIn (G := G) haA
  obtain ⟨m, hpm, hlm, hhm, htm, hlenm⟩ := exists_LIn hpB hpq
  obtain ⟨l2, hp2, hl2, hh2, hlen2⟩ := exists_lamIn (G := G) hcC
  have hL1 : IsIndPath G (l1.reverse ++ m) := by
    refine IsIndPath.append' hp1.reverse hpm (a := a) (b := p) (by rw [List.getLast?_reverse, hh1])
      hhm hap ?_ ?_
    · intro x hx hx2
      exact Finset.disjoint_left.1 hAB (hl1 x (List.mem_reverse.1 hx)) (hlm x hx2)
    · intro x hx y hy hxy
      exact huA x (hl1 x (List.mem_reverse.1 hx)) y (hlm y hy) hxy
  have hL1S : ∀ x ∈ l1.reverse ++ m, x ∈ A ∪ B := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Finset.mem_union_left _ (hl1 x (List.mem_reverse.1 hx))
    · exact Finset.mem_union_right _ (hlm x hx)
  have hL : IsIndPath G ((l1.reverse ++ m) ++ l2) := by
    refine IsIndPath.append' hL1 hp2 (a := q) (b := c) (by simp [List.getLast?_append, htm])
      hh2 hqc ?_ ?_
    · intro x hx hx2
      rcases Finset.mem_union.1 (hL1S x hx) with h | h
      · exact Finset.disjoint_left.1 hAC h (hl2 x hx2)
      · exact Finset.disjoint_left.1 hBC h (hl2 x hx2)
    · intro x hx y hy hxy
      obtain ⟨h1, h2⟩ := huC y (hl2 y hy) x (hL1S x hx) hxy.symm
      exact ⟨h2, h1⟩
  have := ha.length_le (fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · rcases Finset.mem_union.1 (hL1S x hx) with h | h
      · exact hA h
      · exact hB h
    · exact hC (hl2 x hx)) hL
  simp only [List.length_append, List.length_reverse] at this
  omega

/-- A path of `B` from `r` to `p`, continued across the edge `p – c` into `C`. -/
theorem L_add_lam_le_lam {W B C : Finset V} (hB : B ⊆ W) (hC : C ⊆ W) (hBC : Disjoint B C)
    {r p c : V} (hr : r ∈ B) (hcC : c ∈ C) (hpc : G.Adj p c)
    (hu : ∀ u ∈ C, ∀ v ∈ B, G.Adj u v → u = c ∧ v = p) (hrp : ReachIn G B r p) :
    LIn G B r p + lamIn G C c ≤ lamIn G W r := by
  obtain ⟨m, hpm, hlm, hhm, htm, hlenm⟩ := exists_LIn hr hrp
  obtain ⟨l2, hp2, hl2, hh2, hlen2⟩ := exists_lamIn (G := G) hcC
  have hL : IsIndPath G (m ++ l2) := by
    refine IsIndPath.append' hpm hp2 (a := p) (b := c) htm hh2 hpc ?_ ?_
    · intro x hx hx2
      exact Finset.disjoint_left.1 hBC (hlm x hx) (hl2 x hx2)
    · intro x hx y hy hxy
      obtain ⟨h1, h2⟩ := hu y (hl2 y hy) x (hlm x hx) hxy.symm
      exact ⟨h2, h1⟩
  have := le_lamIn (W := W) (v := r) hL (fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact hB (hlm x hx)
    · exact hC (hl2 x hx)) (by simp [List.head?_append, hhm])
  simp only [List.length_append] at this
  omega

end Lam

section Deg

variable {V : Type*} {G : SimpleGraph V}

theorem degIn_union [DecidableEq V] {A C : Finset V} (h : Disjoint A C) (x : V) :
    degIn G (A ∪ C) x = degIn G A x + degIn G C x := by
  classical
  unfold degIn
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem degIn_biUnion [DecidableEq V] (K : Finset (Finset V))
    (hK : (K : Set (Finset V)).PairwiseDisjoint id) (x : V) :
    degIn G (K.biUnion id) x = ∑ C ∈ K, degIn G C x := by
  classical
  unfold degIn
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · rfl
  · intro C hC C' hC' hne
    exact Finset.disjoint_filter_filter (hK hC hC' hne)

theorem dIn_eq_sum (W : Finset V) :
    dIn G W = 4 * ((∑ x ∈ W, degIn G W x : ℕ) : ℤ) - 11 * W.card := by
  classical
  unfold dIn degIn
  congr 3
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter]

theorem dIn_union [DecidableEq V] {A C : Finset V} (h : Disjoint A C) :
    dIn G (A ∪ C) = dIn G A + dIn G C +
      4 * (((∑ x ∈ A, degIn G C x) + (∑ x ∈ C, degIn G A x) : ℕ) : ℤ) := by
  rw [dIn_eq_sum, dIn_eq_sum, dIn_eq_sum, Finset.sum_union h, Finset.card_union_of_disjoint h]
  simp only [degIn_union h, Finset.sum_add_distrib]
  push_cast
  ring

/-- Degree into `C` of a vertex `x ∈ A`, when the only `A`–`C` edge is `a – c`. -/
theorem degIn_eq_ite {A C : Finset V} {a c : V} [DecidableEq V] (hc : c ∈ C)
    (hac : G.Adj a c) (hu : ∀ u ∈ C, ∀ v ∈ A, G.Adj u v → u = c ∧ v = a) {x : V} (hx : x ∈ A) :
    degIn G C x = if x = a then 1 else 0 := by
  classical
  unfold degIn
  split_ifs with hxa
  · subst hxa
    rw [Finset.card_eq_one]
    refine ⟨c, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hxy⟩
      exact (hu y hy x hx hxy.symm).1
    · rintro rfl
      exact ⟨hc, hac⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hxy
    exact hxa (hu y hy x hx hxy.symm).2

theorem sum_degIn_eq_one {A C : Finset V} {a c : V} [DecidableEq V] (ha : a ∈ A) (hc : c ∈ C)
    (hac : G.Adj a c) (hu : ∀ u ∈ C, ∀ v ∈ A, G.Adj u v → u = c ∧ v = a) :
    (∑ x ∈ A, degIn G C x) = 1 := by
  rw [Finset.sum_congr rfl fun x hx => degIn_eq_ite hc hac hu hx, Finset.sum_ite_eq' A a]
  simp [ha]

theorem le_degIn {S T : Finset V} {v : V} (hT : ∀ x ∈ T, x ∈ S ∧ G.Adj v x) :
    T.card ≤ degIn G S v := by
  classical
  unfold degIn
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.2 (hT x hx))

/-- Reachability avoiding a set of edges none of which lies inside `S`. -/
theorem reachIn_deleteEdges {S W : Finset V} (hSW : S ⊆ W) {E : Set (Sym2 V)}
    (hE : ∀ x ∈ S, ∀ y ∈ S, s(x, y) ∉ E) {a b : V} (h : ReachIn G S a b) :
    ReachIn (G.deleteEdges E) W a b :=
  Relation.ReflTransGen.mono (fun x y hxy => ⟨hSW hxy.1, hSW hxy.2.1,
    (SimpleGraph.deleteEdges_adj ..).2 ⟨hxy.2.2, hE x hxy.1 y hxy.2.1⟩⟩) h

end Deg

end Hypostructure.Graph.DensityCert
