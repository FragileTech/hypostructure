import Hypostructure.Graph.PackingExchange

/-!
# Arms at windows: counting, single cuts, and the one-window trigger

An *arm* at a placed window `p` is an induced path `α : Fin (a + 1) → V` inside the remainder
whose end `α (last a)` is adjacent to a position `p i` (a stub of the window).  Three facts:

* **Counting** (`card_mul_le_of_subset`, `thirteen_le_of_exchange`): a window packing of
  order `n` inside `U` has `n·|W| ≤ |U|`.  So `|Q| + 1` windows of order 13 inside
  `T ∪ A` with `|T| ≤ 13·|Q|` force `|A| ≥ 13`: an exchange needs arm total at least 13.
* **Single cut** (`mem_of_cross`): if every edge between `Y` and `Z` has an end at `c`, a
  window inside `Y ∪ Z` meeting both sides contains `c`.  Hence
  - arms attached to `T` only at one vertex `u` (`card_le_of_single_attachment`): the
    windows inside `T ∪ A` not contained in `A` number at most `1 + (|T| − 1)/n`; with
    `|T| = 26`, `n = 13`, at most `2` — two arms at the same window vertex never give an
    exchange at a pair of windows;
  - a window `X` hanging on `T` by edges at one vertex `g ∈ X`
    (`exists_packing_iff_hanging`): `T ∪ X` carries `k + 1` disjoint windows iff `T`
    carries `k`.
* **One-window trigger** (`false_of_two_arms_one_window`): at a maximum packing, two
  disjoint arms at positions `i < j` of one member, with at least `n − 1 − i` and `j`
  vertices, each meeting the segment it is glued to only at its landing edge, do not exist:
  the suffixes of the arms glued to `P[0..i]` and `P[j..n−1]` are two disjoint windows inside
  `P ∪ R` (`PackingExchange.false_of_two_arm_segments`).

The counting and single-cut facts hold in every finite object; the trigger reads only the
maximality of the packing.
-/

namespace Hypostructure.Graph.WindowExchange

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.LocalRigidity

universe u

variable {object : FiniteObject.{u}}

/-! ## Counting -/

/-- A window packing of order `n` whose members lie in `U` has `n · |W| ≤ |U|`. -/
theorem card_mul_le_of_subset {n : ℕ} {W : Finset (Finset object.Vertex)}
    (packed : object.IsWindowPacking n W) {U : Finset object.Vertex}
    (inside : ∀ S ∈ W, S ⊆ U) : n * W.card ≤ U.card := by
  classical
  have hcard : (W.biUnion id).card = ∑ S ∈ W, S.card :=
    Finset.card_biUnion fun S hS T hT ne => packed.2 S hS T hT ne
  have hsum : ∑ S ∈ W, S.card = W.card * n := by
    rw [Finset.sum_congr rfl fun S hS => (packed.1 S hS).2, Finset.sum_const, smul_eq_mul]
  have hsub : W.biUnion id ⊆ U := Finset.biUnion_subset.2 inside
  have := Finset.card_le_card hsub
  rw [hcard, hsum] at this
  linarith

/-- **An exchange needs arm total at least 13.**  `k + 1` disjoint windows of order 13
inside `T ∪ A`, with `|T| ≤ 13·k` (the union of `k` windows), force `|A| ≥ 13`. -/
theorem thirteen_le_of_exchange [DecidableEq object.Vertex] {k : ℕ} {W : Finset (Finset object.Vertex)}
    (packed : object.IsWindowPacking 13 W) (size : W.card = k + 1)
    {T A : Finset object.Vertex} (small : T.card ≤ 13 * k)
    (inside : ∀ S ∈ W, S ⊆ T ∪ A) : 13 ≤ A.card := by
  classical
  have h := card_mul_le_of_subset packed inside
  have := Finset.card_union_le T A
  rw [size] at h
  omega

/-! ## Single cuts -/

/-- A Boolean sequence that changes between `a` and `a + d` changes at a consecutive
pair. -/
theorem exists_change (g : ℕ → Bool) : ∀ d a, g a ≠ g (a + d) →
    ∃ k, a ≤ k ∧ k < a + d ∧ g k ≠ g (k + 1)
  | 0, a, h => absurd rfl h
  | d + 1, a, h => by
    by_cases step : g a = g (a + 1)
    · obtain ⟨k, h1, h2, h3⟩ := exists_change g d (a + 1) (by
        rw [← step, show a + 1 + d = a + (d + 1) by omega]; exact h)
      exact ⟨k, by omega, by omega, h3⟩
    · exact ⟨a, le_rfl, by omega, step⟩

/-- **Single cut.**  Let every edge between `Y` and `Z` (disjoint) have an end at `c`.  A
window inside `Y ∪ Z` that meets both `Y` and `Z` contains `c`. -/
theorem mem_of_cross {n : ℕ} {S Y Z : Finset object.Vertex}
    (hS : object.InducesWindow n S) (sub : ∀ v ∈ S, v ∈ Y ∨ v ∈ Z) (YZ : Disjoint Y Z)
    {y z : object.Vertex} (hy : y ∈ S) (hyY : y ∈ Y) (hz : z ∈ S) (hzZ : z ∈ Z)
    {c : object.Vertex}
    (cut : ∀ y ∈ Y, ∀ z ∈ Z, object.graph.Adj y z → y = c ∨ z = c) : c ∈ S := by
  classical
  obtain ⟨q, hq⟩ := exists_windowPlacement hS
  obtain ⟨ky, rfl⟩ := hq.surjective hS.2 _ hy
  obtain ⟨kz, rfl⟩ := hq.surjective hS.2 _ hz
  let g : ℕ → Bool := fun k => if h : k < n then decide (q ⟨k, h⟩ ∈ Y) else false
  have gy : g ky.1 = true := by simp [g, ky.2, hyY]
  have gz : g kz.1 = false := by
    have : q kz ∉ Y := fun h => Finset.disjoint_left.1 YZ h hzZ
    simp [g, kz.2, this]
  have change : ∃ k, k + 1 < n ∧ g k ≠ g (k + 1) := by
    rcases le_total ky.1 kz.1 with le | le
    · obtain ⟨k, _, h2, h3⟩ := exists_change g (kz.1 - ky.1) ky.1
        (by rw [show ky.1 + (kz.1 - ky.1) = kz.1 by omega, gy, gz]; simp)
      exact ⟨k, by have := kz.2; omega, h3⟩
    · obtain ⟨k, _, h2, h3⟩ := exists_change g (ky.1 - kz.1) kz.1
        (by rw [show kz.1 + (ky.1 - kz.1) = ky.1 by omega, gy, gz]; simp)
      exact ⟨k, by have := ky.2; omega, h3⟩
  obtain ⟨k, hk, hne⟩ := change
  have adj : object.graph.Adj (q ⟨k, by omega⟩) (q ⟨k + 1, hk⟩) := (hq.2.2 _ _).2 (Or.inl rfl)
  have side : ∀ m (h : m < n), q ⟨m, h⟩ ∈ Y ∨ q ⟨m, h⟩ ∈ Z := fun m h => sub _ (hq.2.1 _)
  have g1 : g k = decide (q ⟨k, by omega⟩ ∈ Y) := by simp [g, show k < n by omega]
  have g2 : g (k + 1) = decide (q ⟨k + 1, hk⟩ ∈ Y) := by simp [g, hk]
  rw [g1, g2] at hne
  by_cases h1 : q ⟨k, by omega⟩ ∈ Y
  · have h2 : q ⟨k + 1, hk⟩ ∉ Y := by intro h; simp [h1, h] at hne
    have h2' : q ⟨k + 1, hk⟩ ∈ Z := (side _ hk).resolve_left h2
    rcases cut _ h1 _ h2' adj with e | e
    · exact e ▸ hq.2.1 _
    · exact e ▸ hq.2.1 _
  · have h1' : q ⟨k, by omega⟩ ∈ Z := (side _ (by omega)).resolve_left h1
    have h2 : q ⟨k + 1, hk⟩ ∈ Y := by
      by_contra h; simp [h1, h] at hne
    rcases cut _ h2 _ h1' adj.symm with e | e
    · exact e ▸ hq.2.1 _
    · exact e ▸ hq.2.1 _

/-- **Arms attached at one vertex.**  Let `A` be disjoint from `T` and every edge between
`A` and `T` end at `u ∈ T`.  A window packing of order `n` inside `T ∪ A` none of whose
members lies inside `A` has `n · (|W| − 1) ≤ |T| − 1`: the members meeting `A` contain `u`
(`mem_of_cross`), so at most one member contains `u`, and the others lie in `T \ {u}`. -/
theorem card_le_of_single_attachment [DecidableEq object.Vertex] {n : ℕ}
    {W : Finset (Finset object.Vertex)} (packed : object.IsWindowPacking n W)
    {T A : Finset object.Vertex} (TA : Disjoint T A) {u : object.Vertex} (hu : u ∈ T)
    (attach : ∀ x ∈ A, ∀ t ∈ T, object.graph.Adj x t → t = u)
    (inside : ∀ S ∈ W, S ⊆ T ∪ A) (notArm : ∀ S ∈ W, ¬ S ⊆ A) :
    n * (W.card - 1) ≤ T.card - 1 := by
  classical
  -- every member meeting `A` contains `u`
  have meetU : ∀ S ∈ W, (∃ x ∈ S, x ∈ A) → u ∈ S := by
    intro S hS ⟨x, hxS, hxA⟩
    obtain ⟨t, htS, htA⟩ := Finset.not_subset.1 (notArm S hS)
    have htT : t ∈ T := by
      rcases Finset.mem_union.1 (inside S hS htS) with h | h
      · exact h
      · exact absurd h htA
    refine mem_of_cross (packed.1 S hS) (fun v hv => ?_) TA htS htT hxS hxA
      (fun t ht x hx adj => Or.inl (attach x hx t ht adj.symm))
    rcases Finset.mem_union.1 (inside S hS hv) with h | h
    · exact Or.inl h
    · exact Or.inr h
  let W₀ := W.filter fun S => u ∉ S
  have W₀in : ∀ S ∈ W₀, S ⊆ T.erase u := by
    intro S hS v hv
    obtain ⟨hSW, huS⟩ := Finset.mem_filter.1 hS
    have hvA : v ∉ A := fun hvA => huS (meetU S hSW ⟨v, hv, hvA⟩)
    rcases Finset.mem_union.1 (inside S hSW hv) with h | h
    · exact Finset.mem_erase.2 ⟨fun e => huS (e ▸ hv), h⟩
    · exact absurd h hvA
  have W₀packed : object.IsWindowPacking n W₀ :=
    ⟨fun S hS => packed.1 S (Finset.mem_filter.1 hS).1,
      fun L hL R hR ne => packed.2 L (Finset.mem_filter.1 hL).1 R (Finset.mem_filter.1 hR).1 ne⟩
  have bound := card_mul_le_of_subset W₀packed W₀in
  rw [Finset.card_erase_of_mem hu] at bound
  -- at most one member contains `u`
  have one : (W.filter fun S => u ∈ S).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro L hL R hR
    by_contra ne
    exact Finset.disjoint_left.1 (packed.2 L (Finset.mem_filter.1 hL).1 R
      (Finset.mem_filter.1 hR).1 ne) (Finset.mem_filter.1 hL).2 (Finset.mem_filter.1 hR).2
  have split := Finset.card_filter_add_card_filter_not (s := W) (fun S => u ∈ S)
  have hW₀ : W₀.card = (W.filter fun S => u ∉ S).card := rfl
  have : W.card - 1 ≤ W₀.card := by omega
  calc n * (W.card - 1) ≤ n * W₀.card := Nat.mul_le_mul_left n this
    _ ≤ T.card - 1 := bound

/-- **Two arms at one window vertex give no exchange at a pair of windows.**  With `T` the
26 vertices of two windows of order 13 and arms `A` attached to `T` only at `u`: at most two
disjoint windows of order 13 lie inside `T ∪ A` without lying inside `A`. -/
theorem card_le_two_of_single_attachment [DecidableEq object.Vertex] {W : Finset (Finset object.Vertex)}
    (packed : object.IsWindowPacking 13 W)
    {T A : Finset object.Vertex} (TA : Disjoint T A) (hT : T.card = 26)
    {u : object.Vertex} (hu : u ∈ T)
    (attach : ∀ x ∈ A, ∀ t ∈ T, object.graph.Adj x t → t = u)
    (inside : ∀ S ∈ W, S ⊆ T ∪ A) (notArm : ∀ S ∈ W, ¬ S ⊆ A) : W.card ≤ 2 := by
  have := card_le_of_single_attachment packed TA hu attach inside notArm
  rw [hT] at this
  omega

/-- **A window hanging at one vertex.**  Let `X` induce a window of order `n > 0`, be
disjoint from `T`, and let every edge between `X` and `T` end at `g ∈ X`.  Then `T ∪ X`
carries `k + 1` disjoint windows of order `n` iff `T` carries `k`: every member meeting `X`
contains `g` (it crosses the cut, or it lies in `X` and has `|X|` vertices), so at most one
member meets `X`; conversely `X` extends a packing inside `T`. -/
theorem exists_packing_iff_hanging [DecidableEq object.Vertex] {n : ℕ} (positive : 0 < n)
    {T X : Finset object.Vertex} (hX : object.InducesWindow n X) (TX : Disjoint T X)
    {g : object.Vertex} (hg : g ∈ X)
    (hang : ∀ x ∈ X, ∀ t ∈ T, object.graph.Adj x t → x = g) (k : ℕ) :
    (∃ W : Finset (Finset object.Vertex), object.IsWindowPacking n W ∧
        (∀ S ∈ W, S ⊆ T ∪ X) ∧ W.card = k + 1) ↔
      ∃ W : Finset (Finset object.Vertex), object.IsWindowPacking n W ∧
        (∀ S ∈ W, S ⊆ T) ∧ W.card = k := by
  classical
  constructor
  · rintro ⟨W, packed, inside, size⟩
    have meetG : ∀ S ∈ W, (∃ x ∈ S, x ∈ X) → g ∈ S := by
      intro S hS ⟨x, hxS, hxX⟩
      by_cases sub : S ⊆ X
      · have hSX : S = X := Finset.eq_of_subset_of_card_le sub
          (by rw [(packed.1 S hS).2, hX.2])
        exact hSX ▸ hg
      · obtain ⟨t, htS, htX⟩ := Finset.not_subset.1 sub
        have htT : t ∈ T := by
          rcases Finset.mem_union.1 (inside S hS htS) with h | h
          · exact h
          · exact absurd h htX
        refine mem_of_cross (packed.1 S hS) (fun v hv => ?_) TX htS htT hxS hxX
          (fun t ht x hx adj => Or.inr (hang x hx t ht adj.symm))
        rcases Finset.mem_union.1 (inside S hS hv) with h | h
        · exact Or.inl h
        · exact Or.inr h
    let W₀ := W.filter fun S => g ∉ S
    have W₀in : ∀ S ∈ W₀, S ⊆ T := by
      intro S hS v hv
      obtain ⟨hSW, hgS⟩ := Finset.mem_filter.1 hS
      rcases Finset.mem_union.1 (inside S hSW hv) with h | h
      · exact h
      · exact absurd (meetG S hSW ⟨v, hv, h⟩) hgS
    have one : (W.filter fun S => g ∈ S).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro L hL R hR
      by_contra ne
      exact Finset.disjoint_left.1 (packed.2 L (Finset.mem_filter.1 hL).1 R
        (Finset.mem_filter.1 hR).1 ne) (Finset.mem_filter.1 hL).2 (Finset.mem_filter.1 hR).2
    have split := Finset.card_filter_add_card_filter_not (s := W) (fun S => g ∈ S)
    have hW₀ : W₀.card = (W.filter fun S => g ∉ S).card := rfl
    obtain ⟨W₁, sub, card⟩ := Finset.exists_subset_card_eq (s := W₀) (n := k) (by omega)
    refine ⟨W₁, ⟨fun S hS => packed.1 S (Finset.mem_filter.1 (sub hS)).1,
      fun L hL R hR ne => packed.2 L (Finset.mem_filter.1 (sub hL)).1 R
        (Finset.mem_filter.1 (sub hR)).1 ne⟩, fun S hS => W₀in S (sub hS), card⟩
  · rintro ⟨W, packed, inside, size⟩
    have notMem : X ∉ W := by
      intro hXW
      obtain ⟨x, hx⟩ := object.nonempty_of_inducesWindow positive hX
      exact Finset.disjoint_left.1 TX (inside X hXW hx) hx
    refine ⟨insert X W, ⟨fun S hS => ?_, fun L hL R hR ne => ?_⟩, fun S hS => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hS with rfl | h
      · exact hX
      · exact packed.1 S h
    · have off : ∀ S ∈ W, Disjoint S X := fun S hS =>
        Finset.disjoint_of_subset_left (inside S hS) TX
      rcases Finset.mem_insert.1 hL with eL | hL' <;>
        rcases Finset.mem_insert.1 hR with eR | hR'
      · exact absurd (eL.trans eR.symm) ne
      · exact eL ▸ (off R hR').symm
      · exact eR ▸ off L hL'
      · exact packed.2 L hL' R hR' ne
    · rcases Finset.mem_insert.1 hS with rfl | h
      · exact Finset.subset_union_right
      · exact (inside S h).trans Finset.subset_union_left
    · rw [Finset.card_insert_of_notMem notMem, size]

/-! ## The one-window trigger -/

/-- The last `m + 1` vertices of an induced path on `a + 1` vertices form an induced path
ending at the same vertex. -/
theorem suffix_placement {S : Finset object.Vertex} {a m : ℕ} (hm : m ≤ a)
    {α : Fin (a + 1) → object.Vertex} (hα : IsWindowPlacement object S α) :
    IsWindowPlacement object S (fun k : Fin (m + 1) => α ⟨k.1 + (a - m), by omega⟩) := by
  refine ⟨fun k k' e => ?_, fun k => hα.2.1 _, fun k k' => ?_⟩
  · have := congrArg Fin.val (hα.1 e)
    simp only at this
    exact Fin.ext (by omega)
  · rw [hα.2.2]
    simp only
    omega

/-- **Two arms on one window trigger.**  At a maximum window packing of order `n` with
remainder `R`, a member `P` placed by `p`, positions `i < j`, and two vertex-disjoint arms
`α`, `β` inside `R` (induced paths on `a + 1 ≥ n − 1 − i` and `b + 1 ≥ j` vertices) ending at
`α (last a) ~ p i` and `β (last b) ~ p j`, where `α` meets `p[0..i]` only by that edge and
`β` meets `p[j..n−1]` only by that edge: `False`.  The last `n − 1 − i` vertices of `α` with
`p[0..i]` and the last `j` vertices of `β` with `p[j..n−1]` are two disjoint windows inside
`P ∪ R`. -/
theorem false_of_two_arms_one_window {n : ℕ} (positive : 0 < n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {a b : ℕ} {α : Fin (a + 1) → object.Vertex} {β : Fin (b + 1) → object.Vertex}
    (hα : IsWindowPlacement object (object.remainderSupport packing) α)
    (hβ : IsWindowPlacement object (object.remainderSupport packing) β)
    (αβ : ∀ k k', α k ≠ β k')
    (i j : Fin n) (ij : i.1 < j.1)
    (longα : n ≤ (a + 1) + (i.1 + 1)) (longβ : n ≤ (b + 1) + (n - j.1))
    (ex : object.graph.Adj (α (Fin.last a)) (p i))
    (ey : object.graph.Adj (β (Fin.last b)) (p j))
    (onlyx : ∀ k (t : Fin n), t.1 ≤ i.1 → object.graph.Adj (α k) (p t) →
      k = Fin.last a ∧ t = i)
    (onlyy : ∀ k (t : Fin n), j.1 ≤ t.1 → object.graph.Adj (β k) (p t) →
      k = Fin.last b ∧ t = j) : False := by
  have jn := j.2
  -- suffixes: `n − 2 − i + 1 = n − 1 − i` vertices of `α`, `j − 1 + 1 = j` vertices of `β`
  set a' := n - 2 - i.1 with ha'
  set b' := j.1 - 1 with hb'
  have hα' := suffix_placement (m := a') (by omega) hα
  have hβ' := suffix_placement (m := b') (by omega) hβ
  have lastα : α ⟨(Fin.last a').1 + (a - a'), by omega⟩ = α (Fin.last a) :=
    congrArg α (Fin.ext (by simp; omega))
  have lastβ : β ⟨(Fin.last b').1 + (b - b'), by omega⟩ = β (Fin.last b) :=
    congrArg β (Fin.ext (by simp; omega))
  refine PackingExchange.false_of_two_arm_segments positive valid maximum hP hp hα' hβ'
    (fun k k' => αβ _ _) i j 0 i.1 j.1 (n - 1 - j.1) (by omega) (by omega)
    (Or.inr (by simp)) (Or.inl rfl) (Or.inl (by omega)) (by omega) (by omega)
    (by simpa only [lastα] using ex) (by simpa only [lastβ] using ey) ?_ ?_
  · intro k t _ h2 adj
    obtain ⟨hk, ht⟩ := onlyx _ t (by omega) adj
    refine ⟨Fin.ext ?_, ht⟩
    have := congrArg Fin.val hk
    simp only [Fin.val_last] at this ⊢
    omega
  · intro k t h1 _ adj
    obtain ⟨hk, ht⟩ := onlyy _ t h1 adj
    refine ⟨Fin.ext ?_, ht⟩
    have := congrArg Fin.val hk
    simp only [Fin.val_last] at this ⊢
    omega

end Hypostructure.Graph.WindowExchange
