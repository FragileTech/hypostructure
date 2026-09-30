import Hypostructure.Graph.DensityCert.Transport

/-!
# Density certificate: ear closure

`closure_of_cert`: if a list `L` of concrete graphs contains `K₂` and is closed
under admissible ear extensions with at most `11` new vertices
(`ClosureCert L`), then every admissible 2-connected `G[W]` is a copy of a
member of `L`.

Proof: strong induction on `W`.  For `|W| ≥ 3` take a proper 2-connected
`T ⊊ W` of maximum size, a copy of some `M ∈ L` by induction, and an ear of `T`
in `W` of minimum length `m`.  Minimality makes the ear an induced path whose
attachments to `T` are exactly those of `CG.ear` (`q₀ ~ x`, `q_{m-1} ~ y`, and for
`m = 1` possibly one more `q₀ ~ z`); `T ∪ ear` is 2-connected, hence equals `W`
by maximality; the path `x q₀ … q_{m-1}` is induced, so `m ≤ 11`; and `G[W]` is
a copy of `M.ear m x y z`, to which the certificate applies.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

section Reach

variable {V : Type*} {G : SimpleGraph V}

theorem connIn_of_hub {S : Finset V} {r : V} (hr : r ∈ S) (h : ∀ u ∈ S, ReachIn G S u r) :
    ConnIn G S :=
  ⟨⟨r, hr⟩, fun u hu v hv => (h u hu).trans (reachIn_symm (h v hv))⟩

/-- A chain from a point satisfying `P` to one that does not crosses `P`. -/
theorem exists_cross {α : Type*} {r : α → α → Prop} {P : α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) (ha : P a) (hb : ¬ P b) : ∃ c d, r c d ∧ P c ∧ ¬ P d := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : P c
    · exact ⟨c, d, hcd, hc, hb⟩
    · exact ih hc

theorem connIn_singleton (a : V) : ConnIn G {a} :=
  connIn_of_hub (mem_singleton_self a) fun u hu => by
    rw [mem_singleton.1 hu]; exact Relation.ReflTransGen.refl

variable [DecidableEq V]

theorem twoConnIn_pair {a b : V} (h : G.Adj a b) : TwoConnIn G {a, b} := by
  refine ⟨by rw [card_pair h.ne], connIn_of_hub (mem_insert_self a {b}) fun u hu => ?_,
    fun v hv => ?_⟩
  · rcases mem_insert.1 hu with rfl | hu
    · exact Relation.ReflTransGen.refl
    · rw [mem_singleton.1 hu]
      exact reachIn_step (by simp) (by simp) h.symm
  · have e1 : ({a, b} : Finset V).erase a = {b} := by
      ext u; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h1
        · exact h2
      · rintro rfl; exact ⟨h.ne.symm, Or.inr rfl⟩
    have e2 : ({a, b} : Finset V).erase b = {a} := by
      ext u; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · rintro rfl; exact ⟨h.ne, Or.inl rfl⟩
    rcases mem_insert.1 hv with rfl | hv
    · rw [e1]; exact connIn_singleton b
    · rw [mem_singleton.1 hv, e2]; exact connIn_singleton a

end Reach

section PathHelpers

variable {V : Type*} {G : SimpleGraph V}

theorem isIndPath_range_map {f : ℕ → V} {n : ℕ} (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hadj : ∀ i < n, ∀ j < n, (G.Adj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) :
    IsIndPath G ((List.range n).map f) := by
  refine ⟨List.Nodup.map_on (fun a ha b hb h => hinj a (List.mem_range.1 ha) b
    (List.mem_range.1 hb) h) List.nodup_range, fun i j hi hj => ?_⟩
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  exact hadj i hi j hj

variable {S : Finset V} {x y : V} {m : ℕ} {q : ℕ → V}

theorem reach_back (hx : x ∈ S) (h0 : G.Adj x (q 0))
    (hc : ∀ i, i + 1 < m → G.Adj (q i) (q (i + 1))) :
    ∀ i < m, (∀ j ≤ i, q j ∈ S) → ReachIn G S (q i) x := by
  intro i
  induction i with
  | zero => exact fun _ hS => reachIn_step (hS 0 le_rfl) hx h0.symm
  | succ i ih =>
    intro hi hS
    exact Relation.ReflTransGen.head ⟨hS (i + 1) le_rfl, hS i (by omega), (hc i hi).symm⟩
      (ih (by omega) fun j hj => hS j (by omega))

theorem reach_fwd (hy : y ∈ S) (hl : G.Adj (q (m - 1)) y)
    (hc : ∀ i, i + 1 < m → G.Adj (q i) (q (i + 1))) :
    ∀ i < m, (∀ j, i ≤ j → j < m → q j ∈ S) → ReachIn G S (q i) y := by
  suffices h : ∀ k i, i + k = m - 1 → i < m → (∀ j, i ≤ j → j < m → q j ∈ S) →
      ReachIn G S (q i) y from fun i hi hS => h (m - 1 - i) i (by omega) hi hS
  intro k
  induction k with
  | zero =>
    intro i hik hi hS
    rw [show i = m - 1 by omega] at hS ⊢
    exact reachIn_step (hS _ le_rfl (by omega)) hy hl
  | succ k ih =>
    intro i hik hi hS
    exact Relation.ReflTransGen.head ⟨hS i le_rfl hi, hS (i + 1) (by omega) (by omega),
      hc i (by omega)⟩ (ih (i + 1) (by omega) (by omega) fun j hj hjm => hS j (by omega) hjm)

/-- Four distinct neighbours of a vertex contradict subcubicity. -/
theorem four_nbrs_false {W : Finset V} (hA : AdmIn G W) {v a b c d : V} (hv : v ∈ W)
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c) (hvd : G.Adj v d) : False := by
  classical
  have hdeg := hA.1 v hv
  unfold degIn at hdeg
  have hsub : ({a, b, c, d} : Finset V) ⊆ W.filter (fun w => G.Adj v w) := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp [*]
  have hcard : ({a, b, c, d} : Finset V).card = 4 := by
    rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
      card_pair hcd]
  have := card_le_card hsub
  omega

end PathHelpers

section EarDef

variable {V : Type*} {G : SimpleGraph V}

/-- An ear of `T` in `W`: ends `x ≠ y` in `T`, and a walk `q 0, …, q (m-1)` (`m ≥ 1`) of
vertices of `W \ T` with `x ~ q 0`, `q (m-1) ~ y`. -/
def IsEar (G : SimpleGraph V) (T W : Finset V) (x y : V) (m : ℕ) (q : ℕ → V) : Prop :=
  x ∈ T ∧ y ∈ T ∧ x ≠ y ∧ 1 ≤ m ∧ (∀ i < m, q i ∈ W ∧ q i ∉ T) ∧ G.Adj x (q 0) ∧
    G.Adj (q (m - 1)) y ∧ ∀ i, i + 1 < m → G.Adj (q i) (q (i + 1))

/-- Cut a walk from `b ∉ T` to `t ∈ T` at its first vertex in `T`. -/
theorem exists_cut {T S : Finset V} {b t : V} (h : ReachIn G S b t) (ht : t ∈ T) :
    b ∉ T → b ∈ S → ∃ (m : ℕ) (q : ℕ → V) (y : V), 1 ≤ m ∧ q 0 = b ∧
      (∀ i < m, q i ∈ S ∧ q i ∉ T) ∧ (∀ i, i + 1 < m → G.Adj (q i) (q (i + 1))) ∧
      y ∈ T ∧ y ∈ S ∧ G.Adj (q (m - 1)) y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hb => absurd ht hb
  | @head a c hac _ ih =>
    intro ha haS
    obtain ⟨-, hcS, hadj⟩ := hac
    by_cases hc : c ∈ T
    · exact ⟨1, fun _ => a, c, le_rfl, rfl, fun i _ => ⟨haS, ha⟩, fun i hi => by omega, hc, hcS,
        hadj⟩
    · obtain ⟨m, q, y, hm, hq0, hq, hch, hy, hyS, hl⟩ := ih hc hcS
      refine ⟨m + 1, fun i => if i = 0 then a else q (i - 1), y, by omega, by simp,
        fun i hi => ?_, fun i hi => ?_, hy, hyS, ?_⟩
      · by_cases h0 : i = 0
        · simp [h0, haS, ha]
        · simp only [h0, if_false]; exact hq _ (by omega)
      · by_cases h0 : i = 0
        · subst h0; simpa [hq0] using hadj
        · simp only [h0, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
          have := hch (i - 1) (by omega)
          rwa [show i - 1 + 1 = i + 1 - 1 by omega] at this
      · simp only [Nat.add_sub_cancel, show m ≠ 0 by omega, if_false]
        exact hl

theorem exists_ear [DecidableEq V] {T W : Finset V} (hTW : T ⊆ W) (hne : T ≠ W)
    (hT2 : 2 ≤ T.card) (hW : TwoConnIn G W) : ∃ m x y q, IsEar G T W x y m q := by
  obtain ⟨w, hwW, hwT⟩ : ∃ w ∈ W, w ∉ T := by
    by_contra h
    push Not at h
    exact hne (Subset.antisymm hTW h)
  obtain ⟨t, ht⟩ : T.Nonempty := card_pos.1 (by omega)
  obtain ⟨c, d, ⟨hcW, hdW, hcd⟩, hcT, hdT⟩ :=
    exists_cross (P := (· ∈ T)) (hW.2.1.2 t (hTW ht) w hwW) ht hwT
  obtain ⟨t', ht', ht'c⟩ := exists_mem_ne (by omega : 1 < T.card) c
  have hconn := (hW.2.2 c hcW).2
  have hdc : d ≠ c := fun h => hdT (h ▸ hcT)
  obtain ⟨m, q, y, hm, hq0, hq, hch, hy, hyS, hl⟩ :=
    exists_cut (T := T) (hconn d (mem_erase.2 ⟨hdc, hdW⟩) t' (mem_erase.2 ⟨ht'c, hTW ht'⟩)) ht'
      hdT (mem_erase.2 ⟨hdc, hdW⟩)
  refine ⟨m, c, y, q, hcT, hy, fun h => (mem_erase.1 hyS).1 h.symm, hm,
    fun i hi => ⟨mem_of_mem_erase (hq i hi).1, (hq i hi).2⟩, hq0 ▸ hcd, hl, hch⟩

theorem exists_min_ear [DecidableEq V] {T W : Finset V} (hTW : T ⊆ W) (hne : T ≠ W)
    (hT2 : 2 ≤ T.card) (hW : TwoConnIn G W) :
    ∃ m x y q, IsEar G T W x y m q ∧ ∀ m' < m, ∀ x' y' q', ¬ IsEar G T W x' y' m' q' := by
  classical
  have hex := exists_ear hTW hne hT2 hW
  obtain ⟨x, y, q, hE⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, x, y, q, hE, fun m' hm' x' y' q' h => Nat.find_min hex hm' ⟨x', y', q', h⟩⟩

/-! ### Shorter ears -/

variable {T W : Finset V} {x y : V} {m : ℕ} {q : ℕ → V}

theorem IsEar.prefix (E : IsEar G T W x y m q) {i : ℕ} (hi : i < m) {z : V} (hz : z ∈ T)
    (hzx : z ≠ x) (hadj : G.Adj (q i) z) : IsEar G T W x z (i + 1) q := by
  obtain ⟨hx, _, _, _, hq, h0, _, hc⟩ := E
  exact ⟨hx, hz, Ne.symm hzx, by omega, fun k hk => hq k (by omega), h0, by simpa using hadj,
    fun k hk => hc k (by omega)⟩

theorem IsEar.suffix (E : IsEar G T W x y m q) {i : ℕ} (hi : i < m) {z : V} (hz : z ∈ T)
    (hzy : z ≠ y) (hadj : G.Adj z (q i)) : IsEar G T W z y (m - i) (fun k => q (k + i)) := by
  obtain ⟨_, hy, _, _, hq, _, hl, hc⟩ := E
  refine ⟨hz, hy, hzy, by omega, fun k hk => hq (k + i) (by omega), by simpa using hadj, ?_,
    fun k hk => ?_⟩
  · show G.Adj (q (m - i - 1 + i)) y
    rwa [show m - i - 1 + i = m - 1 by omega]
  · show G.Adj (q (k + i)) (q (k + 1 + i))
    rw [show k + 1 + i = k + i + 1 by omega]
    exact hc _ (by omega)

/-- Skip `q (i+1), …, q (i+d)`. -/
theorem IsEar.skip (E : IsEar G T W x y m q) {i d : ℕ} (hid : i + d < m)
    (h1 : i + 1 + d < m → G.Adj (q i) (q (i + 1 + d))) (h2 : m ≤ i + 1 + d → G.Adj (q i) y) :
    IsEar G T W x y (m - d) (fun k => if k ≤ i then q k else q (k + d)) := by
  obtain ⟨hx, hy, hxy, _, hq, h0, hl, hc⟩ := E
  refine ⟨hx, hy, hxy, by omega, fun k hk => ?_, by simpa using h0, ?_, fun k hk => ?_⟩
  · by_cases hki : k ≤ i
    · simp only [hki, if_true]; exact hq k (by omega)
    · simp only [hki, if_false]; exact hq _ (by omega)
  · by_cases hmi : m - d - 1 ≤ i
    · simp only [hmi, if_true]
      rw [show m - d - 1 = i by omega]
      exact h2 (by omega)
    · simp only [hmi, if_false]
      rwa [show m - d - 1 + d = m - 1 by omega]
  · by_cases hki : k + 1 ≤ i
    · simp only [hki, show k ≤ i by omega, if_true]; exact hc k (by omega)
    · by_cases hk : k ≤ i
      · obtain rfl : k = i := by omega
        simp only [hki, le_refl, if_true, if_false]
        exact h1 (by omega)
      · simp only [hki, hk, if_false]
        rw [show k + 1 + d = k + d + 1 by omega]
        exact hc _ (by omega)

/-! ### Consequences of minimality -/

variable (E : IsEar G T W x y m q) (hmin : ∀ m' < m, ∀ x' y' q', ¬ IsEar G T W x' y' m' q')
include E hmin

theorem IsEar.inj_of_min {i j : ℕ} (hij : i < j) (hj : j < m) : q i ≠ q j := by
  intro h
  refine hmin (m - (j - i)) (by omega) x y _ (E.skip (i := i) (d := j - i) (by omega) ?_ ?_)
  · intro hlt
    rw [h, show i + 1 + (j - i) = j + 1 by omega]
    exact E.2.2.2.2.2.2.2 j (by omega)
  · intro hle
    rw [h, show j = m - 1 by omega]
    exact E.2.2.2.2.2.2.1

theorem IsEar.nonadj_of_min {i j : ℕ} (hij : i + 1 < j) (hj : j < m) : ¬ G.Adj (q i) (q j) := by
  intro h
  refine hmin (m - (j - i - 1)) (by omega) x y _
    (E.skip (i := i) (d := j - i - 1) (by omega) ?_ ?_)
  · intro _
    rwa [show i + 1 + (j - i - 1) = j by omega]
  · intro hle; omega

theorem IsEar.adj_iff_of_min {i j : ℕ} (hi : i < m) (hj : j < m) :
    G.Adj (q i) (q j) ↔ (i + 1 = j ∨ j + 1 = i) := by
  have hc := E.2.2.2.2.2.2.2
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact E.nonadj_of_min hmin (by omega) hj h
    · exact h.ne rfl
    · exact E.nonadj_of_min hmin (by omega) hi h.symm
  · rintro (rfl | rfl)
    · exact hc i hj
    · exact (hc j hi).symm

theorem IsEar.nbr_of_min (hm : 2 ≤ m) {i : ℕ} (hi : i < m) {z : V} (hz : z ∈ T)
    (h : G.Adj (q i) z) : (i = 0 ∧ z = x) ∨ (i = m - 1 ∧ z = y) := by
  by_cases hzx : z = x
  · subst hzx
    by_cases hi0 : i = 0
    · exact Or.inl ⟨hi0, rfl⟩
    · exact absurd (E.suffix hi hz E.2.2.1 h.symm) (hmin (m - i) (by omega) _ _ _)
  · by_cases hi1 : i + 1 < m
    · exact absurd (E.prefix hi hz hzx h) (hmin (i + 1) hi1 _ _ _)
    · by_cases hzy : z = y
      · exact Or.inr ⟨by omega, hzy⟩
      · exact absurd (E.suffix hi hz hzy h.symm) (hmin (m - i) (by omega) _ _ _)

theorem IsEar.le_eleven_of_min (hTW : T ⊆ W) (hA : AdmIn G W) : m ≤ 11 := by
  have hx := E.1
  have hxy := E.2.2.1
  have hq := E.2.2.2.2.1
  have h0 := E.2.2.2.2.2.1
  let f : ℕ → V := fun k => if k = 0 then x else q (k - 1)
  have hxq : ∀ k < m, (G.Adj x (q k) ↔ k = 0) := by
    intro k hk
    constructor
    · intro h
      by_contra hk0
      by_cases hm2 : 2 ≤ m
      · rcases E.nbr_of_min hmin hm2 hk hx h.symm with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hk0 h1
        · exact hxy h2
      · omega
    · rintro rfl; exact h0
  have hp : IsIndPath G ((List.range (m + 1)).map f) := by
    refine isIndPath_range_map (fun i hi j hj hij => ?_) (fun i hi j hj => ?_)
    · by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
      · omega
      · simp only [f, hi0, hj0, if_true, if_false] at hij
        exact absurd (hij ▸ hx) (hq _ (by omega)).2
      · simp only [f, hi0, hj0, if_true, if_false] at hij
        exact absurd (hij ▸ hx) (hq _ (by omega)).2
      · simp only [f, hi0, hj0, if_false] at hij
        rcases lt_trichotomy (i - 1) (j - 1) with h | h | h
        · exact absurd hij (E.inj_of_min hmin h (by omega))
        · omega
        · exact absurd hij.symm (E.inj_of_min hmin h (by omega))
    · by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
      · subst hi0 hj0; simp [f]
      · simp only [f, hi0, hj0, if_true, if_false]
        rw [hxq _ (by omega)]; omega
      · simp only [f, hi0, hj0, if_true, if_false]
        rw [G.adj_comm, hxq _ (by omega)]; omega
      · simp only [f, hi0, hj0, if_false]
        rw [E.adj_iff_of_min hmin (by omega) (by omega)]; omega
  have := hA.length_le (l := (List.range (m + 1)).map f) (fun v hv => ?_) hp
  · simp only [List.length_map, List.length_range] at this
    omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    rw [List.mem_range] at hk
    by_cases hk0 : k = 0
    · simp only [f, hk0, if_true]; exact hTW hx
    · simp only [f, hk0, if_false]; exact (hq _ (by omega)).1

omit E hmin in
theorem IsEar.twoConnIn_union [DecidableEq V] (E : IsEar G T W x y m q) (hT : TwoConnIn G T)
    (hinj : ∀ i < m, ∀ j < m, q i = q j → i = j) :
    TwoConnIn G (T ∪ (range m).image q) := by
  obtain ⟨hx, hy, hxy, hm, hq, h0, hl, hc⟩ := E
  set T' := T ∪ (range m).image q with hT'def
  have hqT' : ∀ i < m, q i ∈ T' := fun i hi => mem_union_right _ (mem_image_of_mem q (mem_range.2 hi))
  have hTT' : T ⊆ T' := subset_union_left
  have hqne : ∀ i < m, ∀ v ∈ T, q i ≠ v := fun i hi v hv h => (hq i hi).2 (h ▸ hv)
  have hmemT' : ∀ u ∈ T', u ∈ T ∨ ∃ i < m, q i = u := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · exact Or.inl hu
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hu
      exact Or.inr ⟨i, mem_range.1 hi, rfl⟩
  refine ⟨le_trans hT.1 (card_le_card hTT'), connIn_of_hub (hTT' hx) fun u hu => ?_,
    fun v hv => ?_⟩
  · rcases hmemT' u hu with hu | ⟨i, hi, rfl⟩
    · exact reachIn_mono hTT' (hT.2.1.2 u hu x hx)
    · exact reach_back (hTT' hx) h0 hc i hi fun j hj => hqT' j (by omega)
  · rcases hmemT' v hv with hvT | ⟨k, hk, rfl⟩
    · have hsub : T.erase v ⊆ T'.erase v := erase_subset_erase v hTT'
      have hqv : ∀ i < m, q i ∈ T'.erase v := fun i hi => mem_erase.2 ⟨hqne i hi v hvT, hqT' i hi⟩
      by_cases hvx : v = x
      · subst hvx
        have hyv : y ∈ T.erase v := mem_erase.2 ⟨Ne.symm hxy, hy⟩
        refine connIn_of_hub (hsub hyv) fun u hu => ?_
        rcases hmemT' u (mem_of_mem_erase hu) with hu' | ⟨i, hi, rfl⟩
        · exact reachIn_mono hsub
            ((hT.2.2 v hvT).2 u (mem_erase.2 ⟨(mem_erase.1 hu).1, hu'⟩) y hyv)
        · exact reach_fwd (hsub hyv) hl hc i hi fun j _ hj => hqv j hj
      · have hxv : x ∈ T.erase v := mem_erase.2 ⟨Ne.symm hvx, hx⟩
        refine connIn_of_hub (hsub hxv) fun u hu => ?_
        rcases hmemT' u (mem_of_mem_erase hu) with hu' | ⟨i, hi, rfl⟩
        · exact reachIn_mono hsub
            ((hT.2.2 v hvT).2 u (mem_erase.2 ⟨(mem_erase.1 hu).1, hu'⟩) x hxv)
        · exact reach_back (hsub hxv) h0 hc i hi fun j hj => hqv j (by omega)
    · have hsub : T ⊆ T'.erase (q k) := fun u hu => mem_erase.2 ⟨fun h => hqne k hk u hu h.symm, hTT' hu⟩
      refine connIn_of_hub (hsub hx) fun u hu => ?_
      rcases hmemT' u (mem_of_mem_erase hu) with hu' | ⟨i, hi, rfl⟩
      · exact reachIn_mono hsub (hT.2.1.2 u hu' x hx)
      · have hik : i ≠ k := fun h => (mem_erase.1 hu).1 (h ▸ rfl)
        have hqk : ∀ j < m, j ≠ k → q j ∈ T'.erase (q k) := fun j hj hjk =>
          mem_erase.2 ⟨fun h => hjk (hinj j hj k hk h), hqT' j hj⟩
        rcases lt_or_gt_of_ne hik with hlt | hlt
        · exact reach_back (hsub hx) h0 hc i hi fun j hj => hqk j (by omega) (by omega)
        · exact (reach_fwd (hsub hy) hl hc i hi fun j hij hj => hqk j hj (by omega)).trans
            (reachIn_mono hsub (hT.2.1.2 y hy x hx))

end EarDef

section Emb

theorem CG.ear_A_iff (M : CG) (m x y : ℕ) (z : Option ℕ) (i j : ℕ) :
    (M.ear m x y z).A i j = true ↔
      (i < M.n ∧ j < M.n ∧ M.A i j = true) ∨
      (i < M.n ∧ M.n ≤ j ∧
        ((j - M.n = 0 ∧ i = x) ∨ (j - M.n + 1 = m ∧ i = y) ∨ (m = 1 ∧ z = some i))) ∨
      (M.n ≤ i ∧ j < M.n ∧
        ((i - M.n = 0 ∧ j = x) ∨ (i - M.n + 1 = m ∧ j = y) ∨ (m = 1 ∧ z = some j))) ∨
      (M.n ≤ i ∧ M.n ≤ j ∧ (i + 1 = j ∨ j + 1 = i)) := by
  have hMA : ∀ a b, ((a != b) && (M.A a b || M.A b a)) = M.A a b := by
    intro a b
    rw [CG.A_symm M b a, Bool.or_self]
    by_cases h : a = b
    · subst h; simp [CG.A_irrefl]
    · simp [h]
  show ((i != j) && ((M.ear m x y z).adj i j || (M.ear m x y z).adj j i)) = true ↔ _
  simp only [CG.ear]
  by_cases hi : i < M.n <;> by_cases hj : j < M.n
  · simp only [hi, hj, if_true, hMA]
    simp [hi, hj]
  · have hne : i ≠ j := by omega
    simp only [hi, hj, if_true, if_false, Bool.or_false]
    simp [hne, show M.n ≤ j by omega, show ¬ M.n ≤ i by omega, or_assoc]
  · have hne : i ≠ j := by omega
    simp only [hi, hj, if_true, if_false, Bool.false_or]
    simp [hne, show M.n ≤ i by omega, show ¬ M.n ≤ j by omega, or_assoc]
  · simp only [hi, hj, if_false]
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq]
    simp only [show M.n ≤ i by omega, show M.n ≤ j by omega, false_and, true_and, false_or]
    omega

variable {V : Type*} {G : SimpleGraph V}

theorem ear_embOnto {M : CG} {T W : Finset V} (φ : M.graph ↪g G) (hφ : ∀ v, v ∈ T ↔ ∃ i, φ i = v)
    {m x y : ℕ} {z : Option ℕ} {q : ℕ → V}
    (hqT : ∀ k < m, q k ∉ T)
    (hqinj : ∀ i < m, ∀ j < m, q i = q j → i = j)
    (hqq : ∀ i < m, ∀ j < m, (G.Adj (q i) (q j) ↔ (i + 1 = j ∨ j + 1 = i)))
    (hTq : ∀ (i : Fin M.n), ∀ k < m, (G.Adj (φ i) (q k) ↔
      ((k = 0 ∧ i.val = x) ∨ (k + 1 = m ∧ i.val = y) ∨ (m = 1 ∧ z = some i.val))))
    (hW : ∀ v, v ∈ W ↔ v ∈ T ∨ ∃ k < m, q k = v) :
    EmbOnto (M.ear m x y z).graph G W := by
  have hn : (M.ear m x y z).n = M.n + m := rfl
  let ψ : Fin (M.ear m x y z).n → V := fun i =>
    if h : (i : ℕ) < M.n then φ ⟨i, h⟩ else q (i - M.n)
  have hφT : ∀ a, φ a ∈ T := fun a => (hφ _).2 ⟨a, rfl⟩
  have hlt : ∀ i : Fin (M.ear m x y z).n, (i : ℕ) < M.n + m := fun i => i.isLt
  have hadj : ∀ i j : Fin (M.ear m x y z).n,
      G.Adj (ψ i) (ψ j) ↔ (M.ear m x y z).graph.Adj i j := by
    intro i j
    rw [CG.graph_adj, CG.ear_A_iff]
    have hi := hlt i
    have hj := hlt j
    by_cases hi' : (i : ℕ) < M.n <;> by_cases hj' : (j : ℕ) < M.n
    · simp only [ψ, hi', hj', dif_pos, φ.map_adj_iff, CG.graph_adj]
      simp [hi', hj']
    · simp only [ψ, hi', hj', dif_pos, dif_neg, not_false_eq_true]
      rw [hTq ⟨i, hi'⟩ _ (by omega)]
      simp [show M.n ≤ (j : ℕ) by omega, show ¬ M.n ≤ (i : ℕ) by omega]
    · simp only [ψ, hi', hj', dif_pos, dif_neg, not_false_eq_true]
      rw [G.adj_comm, hTq ⟨j, hj'⟩ _ (by omega)]
      simp [show M.n ≤ (i : ℕ) by omega, show ¬ M.n ≤ (j : ℕ) by omega]
    · simp only [ψ, hi', hj', dif_neg, not_false_eq_true]
      rw [hqq _ (by omega) _ (by omega)]
      simp only [show M.n ≤ (i : ℕ) by omega, show M.n ≤ (j : ℕ) by omega, false_and,
        true_and, false_or]
      omega
  refine ⟨⟨⟨ψ, fun i j h => ?_⟩, fun {i j} => hadj i j⟩, fun v => ?_⟩
  · have hi := hlt i
    have hj := hlt j
    by_cases hi' : (i : ℕ) < M.n <;> by_cases hj' : (j : ℕ) < M.n
    · simp only [ψ, hi', hj', dif_pos] at h
      have := congrArg Fin.val (φ.injective h)
      exact Fin.ext (by simpa using this)
    · simp only [ψ, hi', hj', dif_pos, dif_neg, not_false_eq_true] at h
      exact absurd (h ▸ hφT _) (hqT _ (by omega))
    · simp only [ψ, hi', hj', dif_pos, dif_neg, not_false_eq_true] at h
      exact absurd (h ▸ hφT _) (hqT _ (by omega))
    · simp only [ψ, hi', hj', dif_neg, not_false_eq_true] at h
      have := hqinj _ (by omega) _ (by omega) h
      exact Fin.ext (by omega)
  · rw [hW]
    constructor
    · rintro (hv | ⟨k, hk, rfl⟩)
      · obtain ⟨a, rfl⟩ := (hφ v).1 hv
        refine ⟨⟨a.val, by rw [hn]; omega⟩, ?_⟩
        simp [ψ, a.isLt]
      · refine ⟨⟨M.n + k, by rw [hn]; omega⟩, ?_⟩
        simp [ψ]
    · rintro ⟨i, rfl⟩
      by_cases hi' : (i : ℕ) < M.n
      · left
        show ψ i ∈ T
        simp only [ψ, hi', dif_pos]
        exact hφT _
      · right
        have := hlt i
        exact ⟨i - M.n, by omega, by simp [ψ, hi']⟩

theorem embOnto_K2 [DecidableEq V] {a b : V} (h : G.Adj a b) : EmbOnto CG.K2.graph G {a, b} := by
  have hn : CG.K2.n = 2 := rfl
  have hA : ∀ u v : ℕ, CG.K2.A u v = (u != v) := by intro u v; simp [CG.A, CG.K2]
  let f : Fin CG.K2.n → V := fun i => if (i : ℕ) = 0 then a else b
  have hval : ∀ i : Fin CG.K2.n, (i : ℕ) = 0 ∨ (i : ℕ) = 1 := fun i => by
    have : (i : ℕ) < 2 := i.isLt
    omega
  have hadj : ∀ i j : Fin CG.K2.n, G.Adj (f i) (f j) ↔ CG.K2.graph.Adj i j := by
    intro i j
    rw [CG.graph_adj, hA]
    rcases hval i with hi | hi <;> rcases hval j with hj | hj <;> simp [f, hi, hj, h, h.symm]
  refine ⟨⟨⟨f, fun i j hij => ?_⟩, fun {i j} => hadj i j⟩, fun v => ?_⟩
  · apply Fin.ext
    rcases hval i with hi | hi <;> rcases hval j with hj | hj <;>
      simp only [f, hi, hj, if_true, one_ne_zero, if_false] at hij
    · omega
    · exact absurd hij h.ne
    · exact absurd hij.symm h.ne
    · omega
  · simp only [mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by rw [hn]; omega⟩, by simp [f]⟩
      · exact ⟨⟨1, by rw [hn]; omega⟩, by simp [f]⟩
    · rintro ⟨i, rfl⟩
      show f i = a ∨ f i = b
      rcases hval i with hi | hi <;> simp [f, hi]

end Emb

/-! ## The ear-closure theorem -/

/-- **Ear closure.**  If `L` contains `K₂` and is closed under admissible ear extensions
with at most `11` new vertices, then every admissible 2-connected `G[W]` is a copy of a
member of `L`. -/
theorem closure_of_cert {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : List CG) (hK2 : CG.K2 ∈ L) (hcert : ClosureCert L) :
    ∀ W : Finset V, AdmIn G W → TwoConnIn G W → ∃ M ∈ L, EmbOnto M.graph G W := by
  classical
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
  intro hA h2
  by_cases hW2 : W.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hW2
    obtain ⟨c, d, ⟨_, hd, hcd⟩, hc, hda⟩ := exists_cross (P := (· = a))
      (h2.2.1.2 a (by simp) b (by simp)) rfl (Ne.symm hab)
    subst hc
    have hdb : d = b := by
      rcases mem_insert.1 hd with h | h
      · exact absurd h hda
      · exact mem_singleton.1 h
    subst hdb
    exact ⟨CG.K2, hK2, embOnto_K2 hcd⟩
  have hW3 : 3 ≤ W.card := by have := h2.1; omega
  -- an edge of `G[W]`
  obtain ⟨a, haW⟩ := h2.2.1.1
  obtain ⟨b, hbW, hba⟩ := exists_mem_ne (by omega : 1 < W.card) a
  obtain ⟨c, d, ⟨hcW, hdW, hcd⟩, _, _⟩ := exists_cross (P := (· = a))
    (h2.2.1.2 a haW b hbW) rfl hba
  -- a maximum proper 2-connected subset
  let F := W.powerset.filter (fun T => T ≠ W ∧ TwoConnIn G T)
  have hF : ({c, d} : Finset V) ∈ F := by
    simp only [F, mem_filter, mem_powerset]
    refine ⟨insert_subset_iff.2 ⟨hcW, singleton_subset_iff.2 hdW⟩, fun h => ?_, twoConnIn_pair hcd⟩
    have := congrArg card h
    rw [card_pair hcd.ne] at this
    omega
  obtain ⟨T, hTF, hTmax⟩ := F.exists_max_image card ⟨_, hF⟩
  simp only [F, mem_filter, mem_powerset] at hTF
  obtain ⟨hTW, hTne, hT⟩ := hTF
  obtain ⟨M, hM, φ, hφ⟩ := ih T (Finset.ssubset_iff_subset_ne.2 ⟨hTW, hTne⟩) (hA.mono hTW) hT
  -- a minimum ear
  obtain ⟨m, x, y, q, E, hmin⟩ := exists_min_ear hTW hTne hT.1 h2
  have hm1 := E.2.2.2.1
  have hqWT := E.2.2.2.2.1
  have hinj : ∀ i < m, ∀ j < m, q i = q j → i = j := by
    intro i hi j hj h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact absurd h (E.inj_of_min hmin hij hj)
    · exact hij
    · exact absurd h.symm (E.inj_of_min hmin hij hi)
  -- `T ∪ ear = W`
  have hWeq : T ∪ (range m).image q = W := by
    by_contra hne
    have hsub : T ∪ (range m).image q ⊆ W := union_subset hTW fun v hv => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hv
      exact (hqWT k (mem_range.1 hk)).1
    have hmem : T ∪ (range m).image q ∈ F := by
      simp only [F, mem_filter, mem_powerset]
      exact ⟨hsub, hne, E.twoConnIn_union hT hinj⟩
    have h1 := hTmax _ hmem
    have h2 : T.card < (T ∪ (range m).image q).card := by
      refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_union_left, fun h => ?_⟩)
      have : q 0 ∈ T ∪ (range m).image q :=
        mem_union_right _ (mem_image_of_mem q (mem_range.2 (by omega)))
      rw [← h] at this
      exact (hqWT 0 (by omega)).2 this
    omega
  have hWmem : ∀ v, v ∈ W ↔ v ∈ T ∨ ∃ k < m, q k = v := by
    intro v
    rw [← hWeq]
    simp [mem_union, mem_image, mem_range]
  have hm11 := E.le_eleven_of_min hmin hTW hA
  have hφT : ∀ a, φ a ∈ T := fun a => (hφ _).2 ⟨a, rfl⟩
  obtain ⟨x', rfl⟩ := (hφ x).1 E.1
  obtain ⟨y', rfl⟩ := (hφ y).1 E.2.1
  have hxy : x' ≠ y' := fun h => E.2.2.1 (h ▸ rfl)
  -- the third attachment
  obtain ⟨z, hz1, hz2, hTq⟩ : ∃ z : Option ℕ, (2 ≤ m → z = none) ∧
      (∀ w, z = some w → w < M.n ∧ w ≠ x'.val ∧ w ≠ y'.val) ∧
      ∀ (i : Fin M.n), ∀ k < m, (G.Adj (φ i) (q k) ↔
        ((k = 0 ∧ i.val = x'.val) ∨ (k + 1 = m ∧ i.val = y'.val) ∨ (m = 1 ∧ z = some i.val))) := by
    by_cases hm2 : 2 ≤ m
    · refine ⟨none, fun _ => rfl, by simp, fun i k hk => ?_⟩
      constructor
      · intro h
        rcases E.nbr_of_min hmin hm2 hk (hφT i) h.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by rw [φ.injective h2]⟩
        · exact Or.inr (Or.inl ⟨by omega, by rw [φ.injective h2]⟩)
      · rintro (⟨rfl, h⟩ | ⟨h1, h⟩ | ⟨h1, _⟩)
        · rw [Fin.ext h]; exact E.2.2.2.2.2.1
        · rw [Fin.ext h, show k = m - 1 by omega]; exact E.2.2.2.2.2.2.1.symm
        · omega
    · obtain rfl : m = 1 := by omega
      have hx0 : G.Adj (φ x') (q 0) := E.2.2.2.2.2.1
      have hy0 : G.Adj (φ y') (q 0) := E.2.2.2.2.2.2.1.symm
      by_cases hex : ∃ w : Fin M.n, w ≠ x' ∧ w ≠ y' ∧ G.Adj (φ w) (q 0)
      · obtain ⟨w, hwx, hwy, hw⟩ := hex
        refine ⟨some w.val, by omega, fun w' h => ?_, fun i k hk => ?_⟩
        · obtain rfl := Option.some.inj h
          exact ⟨w.isLt, fun h => hwx (Fin.ext h), fun h => hwy (Fin.ext h)⟩
        · obtain rfl : k = 0 := by omega
          constructor
          · intro h
            by_cases hix : i = x'
            · exact Or.inl ⟨rfl, by rw [hix]⟩
            by_cases hiy : i = y'
            · exact Or.inr (Or.inl ⟨rfl, by rw [hiy]⟩)
            by_cases hiw : i = w
            · exact Or.inr (Or.inr ⟨rfl, by rw [hiw]⟩)
            exfalso
            have hq0W := (hqWT 0 (by omega)).1
            exact four_nbrs_false hA hq0W (hTW (hφT x')) (hTW (hφT y')) (hTW (hφT w))
              (hTW (hφT i)) (fun h => hxy (φ.injective h)) (fun h => hwx (φ.injective h).symm)
              (fun h => hix (φ.injective h).symm) (fun h => hwy (φ.injective h).symm)
              (fun h => hiy (φ.injective h).symm) (fun h => hiw (φ.injective h).symm)
              hx0.symm hy0.symm hw.symm h.symm
          · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
            · rw [Fin.ext h]; exact hx0
            · rw [Fin.ext h]; exact hy0
            · rw [Fin.ext (Option.some.inj h).symm]; exact hw
      · refine ⟨none, by omega, by simp, fun i k hk => ?_⟩
        obtain rfl : k = 0 := by omega
        constructor
        · intro h
          by_cases hix : i = x'
          · exact Or.inl ⟨rfl, by rw [hix]⟩
          by_cases hiy : i = y'
          · exact Or.inr (Or.inl ⟨rfl, by rw [hiy]⟩)
          exact absurd ⟨i, hix, hiy, h⟩ hex
        · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
          · rw [Fin.ext h]; exact hx0
          · rw [Fin.ext h]; exact hy0
          · exact absurd h (by simp)
  have hemb : EmbOnto (M.ear m x'.val y'.val z).graph G W :=
    ear_embOnto φ hφ (fun k hk => (hqWT k hk).2) hinj (fun i hi j hj => E.adj_iff_of_min hmin hi hj)
      hTq hWmem
  rcases hcert M hM m hm1 hm11 x' x'.isLt y' y'.isLt (fun h => hxy (Fin.ext h)) z hz1 hz2 with
    hbad | ⟨M', hM', ⟨f⟩⟩
  · obtain ⟨ψ, hψ⟩ := hemb
    exact absurd ((admIn_onto_iff ψ hψ).2 hA) hbad
  · exact ⟨M', hM', hemb.of_iso' f⟩

end Hypostructure.Graph.DensityCert
