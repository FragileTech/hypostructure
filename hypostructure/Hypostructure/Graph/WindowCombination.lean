import Mathlib

/-!
# Windows × forced paths × hubs × density

Vocabulary-free, Mathlib-only.

Abstract model.  `W : Set V` is the vertex set of the window packing; maximality is
`∀ g, InducedSeq G 12 g → ∃ t ≤ 12, g t ∈ W` (every induced 13-vertex path meets a window).
Walks, induced paths and cycles are sequences `ℕ → V`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.WindowCombination

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 0. Sequences -/

/-- `g 0, …, g k` is a walk of length `k` with every vertex in `S`. -/
abbrev SWalk (S : Set V) (k : ℕ) (g : ℕ → V) : Prop :=
  (∀ t < k, G.Adj (g t) (g (t + 1))) ∧ ∀ t ≤ k, g t ∈ S

/-- `u` reaches `v` inside `S` by a walk of length exactly `k`. -/
abbrev Reach (S : Set V) (u v : V) (k : ℕ) : Prop :=
  ∃ g : ℕ → V, SWalk G S k g ∧ g 0 = u ∧ g k = v

/-- `g 0, …, g N` is an induced path on `N + 1` vertices. -/
abbrev InducedSeq (N : ℕ) (g : ℕ → V) : Prop :=
  (∀ a ≤ N, ∀ b ≤ N, g a = g b → a = b) ∧
    ∀ a ≤ N, ∀ b ≤ N, (G.Adj (g a) (g b) ↔ (a + 1 = b ∨ b + 1 = a))

/-- `c 0, …, c (n-1)` is a cycle of length `n`. -/
abbrev CycleSeq (n : ℕ) (c : ℕ → V) : Prop :=
  (∀ a < n, ∀ b < n, c a = c b → a = b) ∧ (∀ t, t + 1 < n → G.Adj (c t) (c (t + 1))) ∧
    G.Adj (c (n - 1)) (c 0)

/-- No cycle of length `2^m`, `m ≥ 2`. -/
abbrev NoPow2Cycles : Prop := ∀ m, 2 ≤ m → ∀ c : ℕ → V, ¬ CycleSeq G (2 ^ m) c

/-- Every induced `P13` of `G` has a vertex outside `S`. -/
abbrev NoInducedP13In (S : Set V) : Prop :=
  ∀ g : ℕ → V, InducedSeq G 12 g → ∃ t ≤ 12, g t ∉ S

/-- C4-freeness: two distinct vertices have at most one common neighbour. -/
abbrev C4Free : Prop :=
  ∀ a b c c' : V, a ≠ b → G.Adj a c → G.Adj b c → G.Adj a c' → G.Adj b c' → c = c'

def spliceFn (g : ℕ → V) (i c t : ℕ) : V := if t ≤ i then g t else g (t + c)
def hubCycle (h : V) (g : ℕ → V) (t : ℕ) : V := if t = 0 then h else g (t - 1)
def shiftFn (g : ℕ → V) (i t : ℕ) : V := g (i + t)

/-- Window maximality restricts to any `S` disjoint from the windows. -/
theorem noP13_of_disjoint (W : Set V) (hmax : ∀ g, InducedSeq G 12 g → ∃ t ≤ 12, g t ∈ W)
    (S : Set V) (hS : ∀ v ∈ S, v ∉ W) : NoInducedP13In G S := by
  intro g hg
  obtain ⟨t, ht, hW⟩ := hmax g hg
  exact ⟨t, ht, fun hs => hS _ hs hW⟩

/-! ## 1. Splicing: chords and repetitions shorten walks -/

theorem splice_chord {S : Set V} {k : ℕ} {g : ℕ → V} (hw : SWalk G S k g) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j ≤ k) (hadj : G.Adj (g i) (g j)) :
    SWalk G S (k - (j - i - 1)) (spliceFn g i (j - i - 1)) ∧
      spliceFn g i (j - i - 1) 0 = g 0 ∧ spliceFn g i (j - i - 1) (k - (j - i - 1)) = g k := by
  obtain ⟨hA, hS⟩ := hw
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_⟩
  · unfold spliceFn
    by_cases h1 : t + 1 ≤ i
    · rw [if_pos (by omega : t ≤ i), if_pos h1]; exact hA t (by omega)
    · by_cases h2 : t ≤ i
      · rw [if_pos h2, if_neg h1]
        have e1 : t + 1 + (j - i - 1) = j := by omega
        have e2 : t = i := by omega
        rw [e1, e2]; exact hadj
      · rw [if_neg h2, if_neg h1]
        have e : t + 1 + (j - i - 1) = t + (j - i - 1) + 1 := by omega
        rw [e]; exact hA _ (by omega)
  · unfold spliceFn
    by_cases h1 : t ≤ i
    · rw [if_pos h1]; exact hS t (by omega)
    · rw [if_neg h1]; exact hS _ (by omega)
  · unfold spliceFn; rw [if_pos (Nat.zero_le _)]
  · unfold spliceFn; rw [if_neg (by omega)]; congr 1; omega

theorem splice_eq {S : Set V} {k : ℕ} {g : ℕ → V} (hw : SWalk G S k g) {i j : ℕ}
    (hij : i < j) (hj : j ≤ k) (he : g i = g j) :
    SWalk G S (k - (j - i)) (spliceFn g i (j - i)) ∧
      spliceFn g i (j - i) 0 = g 0 ∧ spliceFn g i (j - i) (k - (j - i)) = g k := by
  obtain ⟨hA, hS⟩ := hw
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_⟩
  · unfold spliceFn
    by_cases h1 : t + 1 ≤ i
    · rw [if_pos (by omega : t ≤ i), if_pos h1]; exact hA t (by omega)
    · by_cases h2 : t ≤ i
      · rw [if_pos h2, if_neg h1]
        have e1 : t + 1 + (j - i) = j + 1 := by omega
        have e2 : t = i := by omega
        rw [e1, e2, he]; exact hA j (by omega)
      · rw [if_neg h2, if_neg h1]
        have e : t + 1 + (j - i) = t + (j - i) + 1 := by omega
        rw [e]; exact hA _ (by omega)
  · unfold spliceFn
    by_cases h1 : t ≤ i
    · rw [if_pos h1]; exact hS t (by omega)
    · rw [if_neg h1]; exact hS _ (by omega)
  · unfold spliceFn; rw [if_pos (Nat.zero_le _)]
  · unfold spliceFn
    by_cases h1 : k - (j - i) ≤ i
    · rw [if_pos h1]
      have e : k - (j - i) = i := by omega
      rw [e, he]; congr 1; omega
    · rw [if_neg h1]; congr 1; omega

/-- A splice of an injective walk is injective. -/
theorem splice_chord_inj {k : ℕ} {g : ℕ → V} (hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b)
    {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ k) :
    ∀ a ≤ k - (j - i - 1), ∀ b ≤ k - (j - i - 1),
      spliceFn g i (j - i - 1) a = spliceFn g i (j - i - 1) b → a = b := by
  intro a ha b hb hab
  unfold spliceFn at hab
  by_cases h1 : a ≤ i <;> by_cases h2 : b ≤ i
  · rw [if_pos h1, if_pos h2] at hab; exact hinj a (by omega) b (by omega) hab
  · rw [if_pos h1, if_neg h2] at hab
    have := hinj a (by omega) _ (by omega) hab; omega
  · rw [if_neg h1, if_pos h2] at hab
    have := hinj _ (by omega) b (by omega) hab; omega
  · rw [if_neg h1, if_neg h2] at hab
    have := hinj _ (by omega) _ (by omega) hab; omega

/-! ## 2. Minimal walks are induced; diameter ≤ 11 inside any window-free set -/

theorem exists_minimal_walk {S : Set V} {u v : V} (h : ∃ k, Reach G S u v k) :
    ∃ k g, SWalk G S k g ∧ g 0 = u ∧ g k = v ∧ (∀ k' < k, ¬ Reach G S u v k') := by
  classical
  obtain ⟨g, hw, h0, hk⟩ := Nat.find_spec h
  exact ⟨Nat.find h, g, hw, h0, hk, fun k' hk' => Nat.find_min h hk'⟩

/-- **Geodesics are induced.**  A shortest `S`-walk is an induced path of `G`. -/
theorem minimal_walk_induced {S : Set V} {u v : V} {k : ℕ} {g : ℕ → V}
    (hw : SWalk G S k g) (h0 : g 0 = u) (hk : g k = v)
    (hmin : ∀ k' < k, ¬ Reach G S u v k') : InducedSeq G k g := by
  have hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨hw', h0', hk'⟩ := splice_eq G hw hlt hb hab
      exact hmin _ (by omega) ⟨_, hw', h0'.trans h0, hk'.trans hk⟩
    · obtain ⟨hw', h0', hk'⟩ := splice_eq G hw hlt ha hab.symm
      exact hmin _ (by omega) ⟨_, hw', h0'.trans h0, hk'.trans hk⟩
  refine ⟨hinj, fun a ha b hb => ⟨fun hadj => ?_, fun hc => ?_⟩⟩
  · by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hne : a ≠ b := fun e => by subst e; exact G.irrefl hadj
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨hw', h0', hk'⟩ := splice_chord G hw (i := a) (j := b) (by omega) hb hadj
      exact hmin _ (by omega) ⟨_, hw', h0'.trans h0, hk'.trans hk⟩
    · obtain ⟨hw', h0', hk'⟩ := splice_chord G hw (i := b) (j := a) (by omega) ha hadj.symm
      exact hmin _ (by omega) ⟨_, hw', h0'.trans h0, hk'.trans hk⟩
  · rcases hc with hc | hc
    · subst hc; exact hw.1 a (by omega)
    · subst hc; exact (hw.1 b (by omega)).symm

theorem induced_prefix {N k : ℕ} {g : ℕ → V} (hg : InducedSeq G k g) (hN : N ≤ k) :
    InducedSeq G N g :=
  ⟨fun a ha b hb => hg.1 a (by omega) b (by omega),
    fun a ha b hb => hg.2 a (by omega) b (by omega)⟩

/-- **Diameter ≤ 11.**  In any vertex set `S` containing no induced `P13` (e.g. any
`S ⊆ R = V \ W`, any component of `G[R]`, or `R \ {h}`), two `S`-connected vertices are
joined by an induced `S`-path of length `≤ 11` that is a shortest `S`-walk. -/
theorem short_walk {S : Set V} (hno : NoInducedP13In G S) {u v : V}
    (h : ∃ k, Reach G S u v k) :
    ∃ k g, k ≤ 11 ∧ SWalk G S k g ∧ g 0 = u ∧ g k = v ∧ InducedSeq G k g ∧
      (∀ k' < k, ¬ Reach G S u v k') := by
  obtain ⟨k, g, hw, h0, hk, hmin⟩ := exists_minimal_walk G h
  have hind := minimal_walk_induced G hw h0 hk hmin
  refine ⟨k, g, ?_, hw, h0, hk, hind, hmin⟩
  by_contra hlt
  obtain ⟨t, ht, hts⟩ := hno g (induced_prefix G hind (by omega))
  exact hts (hw.2 t (by omega))

/-! ## 3. Hub pairs: short bypass inside a window-free piece, or every path meets a window -/

theorem cycle_through_hub {S : Set V} {h : V} (hh : h ∉ S) {k : ℕ} {g : ℕ → V}
    (hw : SWalk G S k g) (hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b)
    (hx : G.Adj h (g 0)) (hy : G.Adj h (g k)) :
    CycleSeq G (k + 2) (hubCycle h g) := by
  refine ⟨fun a ha b hb hab => ?_, fun t ht => ?_, ?_⟩
  · unfold hubCycle at hab
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
    · omega
    · rw [if_pos ha0, if_neg hb0] at hab
      have := hw.2 (b - 1) (by omega); rw [← hab] at this; exact (hh this).elim
    · rw [if_neg ha0, if_pos hb0] at hab
      have := hw.2 (a - 1) (by omega); rw [hab] at this; exact (hh this).elim
    · rw [if_neg ha0, if_neg hb0] at hab
      have := hinj (a - 1) (by omega) (b - 1) (by omega) hab; omega
  · unfold hubCycle
    by_cases h0 : t = 0
    · rw [if_pos h0, if_neg (by omega)]
      subst h0; simpa using hx
    · rw [if_neg h0, if_neg (by omega)]
      have e : t + 1 - 1 = t - 1 + 1 := by omega
      rw [e]; exact hw.1 _ (by omega)
  · unfold hubCycle
    rw [if_neg (by omega), if_pos rfl]
    have e : k + 2 - 1 - 1 = k := by omega
    rw [e]; exact hy.symm

/-- **Hub bypass.**  Let `x, y` be non-adjacent neighbours of a hub `h ∉ S`, connected
inside a window-free `S`.  Then the shortest `S`-path `x → y` is induced, has length
`k ∈ {3,4,5,7,8,9,10,11}` and closes a cycle of length `k + 2` through `h`; if the pair is a
*long* pair (no `x–u–w–y` avoiding `h`) then `k ≠ 3`, i.e. `k ∈ {4,5,7,8,9,10,11}`. -/
theorem hub_pair_bypass {S : Set V} (hno : NoInducedP13In G S) (hcyc : NoPow2Cycles G)
    {h x y : V} (hh : h ∉ S) (hx : G.Adj h x) (hy : G.Adj h y) (hxy : x ≠ y)
    (hnadj : ¬ G.Adj x y) (hconn : ∃ k, Reach G S x y k) :
    ∃ k g, SWalk G S k g ∧ g 0 = x ∧ g k = y ∧ InducedSeq G k g ∧
      CycleSeq G (k + 2) (hubCycle h g) ∧
      k ∈ ({3, 4, 5, 7, 8, 9, 10, 11} : Finset ℕ) ∧
      ((¬ ∃ u w, u ≠ h ∧ w ≠ h ∧ G.Adj x u ∧ G.Adj u w ∧ G.Adj w y) → k ≠ 3) := by
  obtain ⟨k, g, hk11, hw, h0, hk, hind, _⟩ := short_walk G hno hconn
  have hcy := cycle_through_hub G hh hw hind.1 (by rw [h0]; exact hx) (by rw [hk]; exact hy)
  have hk0 : k ≠ 0 := by rintro rfl; exact hxy (h0.symm.trans hk)
  have hk1 : k ≠ 1 := by
    rintro rfl
    have := hw.1 0 (by omega)
    rw [zero_add, h0, hk] at this
    exact hnadj this
  have hk2 : k ≠ 2 := by
    rintro rfl
    rw [show (2 : ℕ) + 2 = 2 ^ 2 by norm_num] at hcy
    exact hcyc 2 le_rfl _ hcy
  have hk6 : k ≠ 6 := by
    rintro rfl
    rw [show (6 : ℕ) + 2 = 2 ^ 3 by norm_num] at hcy
    exact hcyc 3 (by norm_num) _ hcy
  refine ⟨k, g, hw, h0, hk, hind, hcy, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro hno3 hk3
    subst hk3
    apply hno3
    refine ⟨g 1, g 2, fun e => ?_, fun e => ?_, ?_, ?_, ?_⟩
    · have := hw.2 1 (by omega); rw [e] at this; exact hh this
    · have := hw.2 2 (by omega); rw [e] at this; exact hh this
    · have := hw.1 0 (by omega); rw [h0] at this; exact this
    · exact hw.1 1 (by omega)
    · have := hw.1 2 (by omega); rw [hk] at this; exact this

/-- **Dichotomy at a hub pair (hub anywhere, `S = R \ {h}`).**  Either the short bypass of
`hub_pair_bypass` exists inside `R \ {h}`, or *every* `x → y` walk hits a window or `h`
(so every forced path, which avoids the edges `hx, hy`, passes through `W ∪ {h}`). -/
theorem hub_pair_dichotomy (W : Set V) (hmax : ∀ g, InducedSeq G 12 g → ∃ t ≤ 12, g t ∈ W)
    (hcyc : NoPow2Cycles G) {h x y : V} (hx : G.Adj h x) (hy : G.Adj h y) (hxy : x ≠ y)
    (hnadj : ¬ G.Adj x y) :
    (∃ k g, SWalk G {v | v ∉ W ∧ v ≠ h} k g ∧ g 0 = x ∧ g k = y ∧ InducedSeq G k g ∧
      CycleSeq G (k + 2) (hubCycle h g) ∧ k ∈ ({3, 4, 5, 7, 8, 9, 10, 11} : Finset ℕ) ∧
      ((¬ ∃ u w, u ≠ h ∧ w ≠ h ∧ G.Adj x u ∧ G.Adj u w ∧ G.Adj w y) → k ≠ 3)) ∨
    (∀ k (g : ℕ → V), (∀ t < k, G.Adj (g t) (g (t + 1))) → g 0 = x → g k = y →
      ∃ t ≤ k, g t ∈ W ∨ g t = h) := by
  by_cases hc : ∃ k, Reach G {v | v ∉ W ∧ v ≠ h} x y k
  · left
    exact hub_pair_bypass G
      (noP13_of_disjoint G W hmax _ (fun v (hv : v ∉ W ∧ v ≠ h) => hv.1)) hcyc
      (fun (hh : h ∉ W ∧ h ≠ h) => hh.2 rfl) hx hy hxy hnadj hc
  · right
    intro k g hadj h0 hk
    by_contra hall
    push Not at hall
    exact hc ⟨k, g, ⟨hadj, fun t ht => by exact hall t ht⟩, h0, hk⟩

/-! ## 4. Long paths inside a window-free set carry chords -/

/-- Every 13 consecutive vertices of an injective `S`-walk carry a chord. -/
theorem block_has_chord {S : Set V} (hno : NoInducedP13In G S) {k : ℕ} {g : ℕ → V}
    (hw : SWalk G S k g) (hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) {a : ℕ}
    (ha : a + 12 ≤ k) :
    ∃ i j, a ≤ i ∧ i + 2 ≤ j ∧ j ≤ a + 12 ∧ G.Adj (g i) (g j) := by
  by_contra hcon
  push Not at hcon
  have hind : InducedSeq G 12 (shiftFn g a) := by
    refine ⟨fun p hp q hq hpq => ?_, fun p hp q hq => ⟨fun hadj => ?_, fun hc => ?_⟩⟩
    · unfold shiftFn at hpq
      have := hinj (a + p) (by omega) (a + q) (by omega) hpq; omega
    · unfold shiftFn at hadj
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      rcases lt_trichotomy p q with hlt | heq | hgt
      · exact hcon (a + p) (a + q) (by omega) (by omega) (by omega) hadj
      · subst heq; exact G.irrefl hadj
      · exact hcon (a + q) (a + p) (by omega) (by omega) (by omega) hadj.symm
    · unfold shiftFn
      rcases hc with hc | hc
      · subst hc; rw [← Nat.add_assoc]; exact hw.1 (a + p) (by omega)
      · subst hc; rw [← Nat.add_assoc]; exact (hw.1 (a + q) (by omega)).symm
  obtain ⟨t, ht, hts⟩ := hno _ hind
  exact hts (hw.2 (a + t) (by omega))

/-- A chord of span `j - i` on an injective walk closes a cycle of length `j - i + 1`. -/
theorem chord_cycle {k : ℕ} {g : ℕ → V} {S : Set V} (hw : SWalk G S k g)
    (hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ k)
    (hadj : G.Adj (g i) (g j)) : CycleSeq G (j - i + 1) (shiftFn g i) := by
  refine ⟨fun p hp q hq hpq => ?_, fun t ht => ?_, ?_⟩
  · unfold shiftFn at hpq
    have := hinj (i + p) (by omega) (i + q) (by omega) hpq; omega
  · unfold shiftFn; rw [← Nat.add_assoc]; exact hw.1 (i + t) (by omega)
  · unfold shiftFn
    have e : i + (j - i + 1 - 1) = j := by omega
    rw [e, Nat.add_zero]; exact hadj.symm

/-- **Forced path inside a window-free set.**  Let `g` be an injective `S`-path of length
`L ≥ 12` between two neighbours of `h ∉ S` (e.g. a forced path of length `2^j - 1 ≥ 15` that
stays in `R \ {h}`).  Then its first 13 vertices carry a chord `(i, j)`, and the span
`s = j - i` satisfies: `s + 1` is not a power of two `≥ 4` (chord cycle) and
`L - s + 3` is not a power of two `≥ 4` (bypass cycle through `h`). -/
theorem forced_path_chord {S : Set V} (hno : NoInducedP13In G S) (hcyc : NoPow2Cycles G)
    {h : V} (hh : h ∉ S) {L : ℕ} {g : ℕ → V} (hw : SWalk G S L g)
    (hinj : ∀ a ≤ L, ∀ b ≤ L, g a = g b → a = b)
    (hx : G.Adj h (g 0)) (hy : G.Adj h (g L)) (hL : 12 ≤ L) :
    ∃ i j, i + 2 ≤ j ∧ j ≤ 12 ∧ G.Adj (g i) (g j) ∧
      ∀ m, 2 ≤ m → j - i + 1 ≠ 2 ^ m ∧ L - (j - i) + 3 ≠ 2 ^ m := by
  obtain ⟨i, j, _, hij, hj, hadj⟩ := block_has_chord G hno hw hinj (a := 0) (by omega)
  refine ⟨i, j, hij, by omega, hadj, fun m hm => ⟨fun he => ?_, fun he => ?_⟩⟩
  · have hc := chord_cycle G hw hinj hij (by omega) hadj
    rw [he] at hc; exact hcyc m hm _ hc
  · obtain ⟨hw', h0', hk'⟩ := splice_chord G hw hij (by omega) hadj
    have hinj' := splice_chord_inj hinj hij (by omega)
    have hc := cycle_through_hub G hh hw' hinj' (by rw [h0']; exact hx) (by rw [hk']; exact hy)
    have e : L - (j - i - 1) + 2 = 2 ^ m := by omega
    rw [e] at hc; exact hcyc m hm _ hc

/-- For the length-15 forced path (16 vertices): the chord span lies in
`{4,5,6,8,9,11,12}` — in particular no triangle (span 2) and no span 3, 7, 10. -/
theorem span_set_L15 (s : ℕ) (h2 : 2 ≤ s) (h12 : s ≤ 12)
    (h : ∀ m, 2 ≤ m → s + 1 ≠ 2 ^ m ∧ 15 - s + 3 ≠ 2 ^ m) :
    s ∈ ({4, 5, 6, 8, 9, 11, 12} : Finset ℕ) := by
  have a := h 2 le_rfl
  have b := h 3 (by norm_num)
  have c := h 4 (by norm_num)
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at a
  rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at b
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at c
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **Chord count.**  An injective `S`-walk on `k + 1` vertices has at least `⌊(k+1)/13⌋`
chords (one per disjoint block of 13 consecutive vertices). -/
theorem chord_count {S : Set V} (hno : NoInducedP13In G S) {k : ℕ} {g : ℕ → V}
    (hw : SWalk G S k g) (hinj : ∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) :
    (k + 1) / 13 ≤ ((range (k + 1) ×ˢ range (k + 1)).filter
        (fun p : ℕ × ℕ => p.1 + 2 ≤ p.2 ∧ G.Adj (g p.1) (g p.2))).card := by
  have key : ∀ b, ∃ p : ℕ × ℕ, b < (k + 1) / 13 →
      13 * b ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 ≤ 13 * b + 12 ∧ G.Adj (g p.1) (g p.2) := by
    intro b
    by_cases hb : b < (k + 1) / 13
    · obtain ⟨i, j, h1, h2, h3, h4⟩ := block_has_chord G hno hw hinj (a := 13 * b) (by omega)
      exact ⟨(i, j), fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hb⟩
  choose f hf using key
  refine le_trans (le_of_eq (card_range _).symm) (card_le_card_of_injOn f ?_ ?_)
  · intro b hb
    have hb' : b < (k + 1) / 13 := by simpa using hb
    obtain ⟨h1, h2, h3, h4⟩ := hf b hb'
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨⟨by omega, by omega⟩, h2, h4⟩
  · intro b hb b' hb' he
    have hb1 : b < (k + 1) / 13 := by simpa using hb
    have hb2 : b' < (k + 1) / 13 := by simpa using hb'
    obtain ⟨h1, _, h3, _⟩ := hf b hb1
    obtain ⟨h1', _, h3', _⟩ := hf b' hb2
    rw [he] at h1 h3
    omega

/-! ## 5. Size of a window-free component: layered (Moore-type) bound -/

theorem reach_extend {S : Set V} {u w v : V} {k : ℕ} (h : Reach G S u w k)
    (hadj : G.Adj w v) (hv : v ∈ S) : Reach G S u v (k + 1) := by
  obtain ⟨g, hw, h0, hk⟩ := h
  refine ⟨fun t => if t ≤ k then g t else v, ⟨fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_⟩
  · show G.Adj (if t ≤ k then g t else v) (if t + 1 ≤ k then g (t + 1) else v)
    by_cases h1 : t + 1 ≤ k
    · rw [if_pos (by omega), if_pos h1]; exact hw.1 t (by omega)
    · rw [if_pos (by omega), if_neg h1, show t = k by omega, hk]; exact hadj
  · show (if t ≤ k then g t else v) ∈ S
    by_cases h1 : t ≤ k
    · rw [if_pos h1]; exact hw.2 t h1
    · rw [if_neg h1]; exact hv
  · show (if 0 ≤ k then g 0 else v) = u
    rw [if_pos (Nat.zero_le _), h0]
  · show (if k + 1 ≤ k then g (k + 1) else v) = v
    rw [if_neg (by omega)]

/-- **Canonical BFS layering** of `K` from `r` by shortest `K`-walk length. -/
theorem exists_layering (K : Finset V) (r : V) (hr : r ∈ K) (D : ℕ)
    (hreach : ∀ v ∈ K, ∃ k ≤ D, Reach G (↑K : Set V) r v k) :
    ∃ lay : V → ℕ, (∀ v ∈ K, lay v ≤ D) ∧ (∀ v ∈ K, lay v = 0 → v = r) ∧ lay r = 0 ∧
      (∀ v ∈ K, ∀ i, lay v = i + 1 → ∃ u ∈ K, lay u = i ∧ G.Adj u v) := by
  classical
  refine ⟨fun v => if hv : ∃ k, Reach G (↑K : Set V) r v k then Nat.find hv else 0,
    ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨k, hk, hR⟩ := hreach v hv
    have hex : ∃ k, Reach G (↑K : Set V) r v k := ⟨k, hR⟩
    simp only [dif_pos hex]
    exact (Nat.find_min' hex hR).trans hk
  · intro v hv h0
    obtain ⟨k, hk, hR⟩ := hreach v hv
    have hex : ∃ k, Reach G (↑K : Set V) r v k := ⟨k, hR⟩
    simp only [dif_pos hex] at h0
    obtain ⟨g, _, hg0, hgk⟩ := Nat.find_spec hex
    rw [h0] at hgk
    exact hgk.symm.trans hg0
  · have hR0 : Reach G (↑K : Set V) r r 0 :=
      ⟨fun _ => r, ⟨fun t ht => absurd ht (Nat.not_lt_zero t), fun t _ => Finset.mem_coe.2 hr⟩,
        rfl, rfl⟩
    have hex : ∃ k, Reach G (↑K : Set V) r r k := ⟨0, hR0⟩
    simp only [dif_pos hex]
    exact Nat.find_eq_zero hex |>.2 hR0
  · intro v hv i hi
    obtain ⟨k, hk, hR⟩ := hreach v hv
    have hex : ∃ k, Reach G (↑K : Set V) r v k := ⟨k, hR⟩
    simp only [dif_pos hex] at hi
    obtain ⟨g, hw, hg0, hgk⟩ := Nat.find_spec hex
    rw [hi] at hw hgk
    have hu : g i ∈ K := Finset.mem_coe.1 (hw.2 i (by omega))
    have hRu : Reach G (↑K : Set V) r (g i) i :=
      ⟨g, ⟨fun t ht => hw.1 t (by omega), fun t ht => hw.2 t (by omega)⟩, hg0, rfl⟩
    have hexu : ∃ k, Reach G (↑K : Set V) r (g i) k := ⟨i, hRu⟩
    refine ⟨g i, hu, ?_, by rw [← hgk]; exact hw.1 i (by omega)⟩
    simp only [dif_pos hexu]
    apply le_antisymm (Nat.find_min' hexu hRu)
    by_contra hlt
    push Not at hlt
    have hRv : Reach G (↑K : Set V) r v (Nat.find hexu + 1) := by
      refine reach_extend G (Nat.find_spec hexu) ?_ (Finset.mem_coe.2 hv)
      rw [← hgk]; exact hw.1 i (by omega)
    exact Nat.find_min hex (by omega) hRv

theorem geom_two (D : ℕ) : ∑ i ∈ range D, 2 ^ i + 1 = 2 ^ D := by
  induction D with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

/-- **Layer bound.**  `|L_{i+1}| ≤ 2|L_i| + σ(L_i)` for `i ≥ 1`, `|L_1| ≤ deg r`; hence
`|K| ≤ 1 + (3 + σ_K)(2^D - 1)` where `σ_K = ∑_K (deg - 3)` (full degrees in `G`). -/
theorem layer_bound (K : Finset V) (r : V) (hr : r ∈ K) (lay : V → ℕ) (D : ℕ)
    (hD : ∀ v ∈ K, lay v ≤ D) (h0 : ∀ v ∈ K, lay v = 0 → v = r) (hr0 : lay r = 0)
    (hpred : ∀ v ∈ K, ∀ i, lay v = i + 1 → ∃ u ∈ K, lay u = i ∧ G.Adj u v)
    (hdeg : ∀ v ∈ K, 3 ≤ G.degree v) :
    K.card ≤ 1 + (3 + ∑ v ∈ K, (G.degree v - 3)) * (2 ^ D - 1) := by
  classical
  have hL0 : K.filter (fun v => lay v = 0) = {r} := by
    ext v
    simp only [mem_filter, mem_singleton]
    exact ⟨fun hv => h0 v hv.1 hv.2, fun hv => by subst hv; exact ⟨hr, hr0⟩⟩
  have hcover : ∀ i, (K.filter (fun v => lay v = i + 1)).card ≤
      ∑ u ∈ K.filter (fun v => lay v = i),
        ((G.neighborFinset u).filter (fun v => v ∈ K ∧ lay v = i + 1)).card := by
    intro i
    refine le_trans (card_le_card ?_) card_biUnion_le
    intro v hv
    rw [mem_filter] at hv
    obtain ⟨u, hu, hui, hadj⟩ := hpred v hv.1 i hv.2
    rw [mem_biUnion]
    exact ⟨u, mem_filter.2 ⟨hu, hui⟩,
      mem_filter.2 ⟨by simpa using hadj, hv.1, hv.2⟩⟩
  have hfib0 : ((G.neighborFinset r).filter (fun v => v ∈ K ∧ lay v = 0 + 1)).card
      ≤ G.degree r := by
    rw [← G.card_neighborFinset_eq_degree]; exact card_filter_le _ _
  have hfib : ∀ i, ∀ u ∈ K.filter (fun v => lay v = i + 1),
      ((G.neighborFinset u).filter (fun v => v ∈ K ∧ lay v = i + 1 + 1)).card
        ≤ 2 + (G.degree u - 3) := by
    intro i u hu
    rw [mem_filter] at hu
    obtain ⟨w, hw, hwi, hwu⟩ := hpred u hu.1 i hu.2
    have hsub : (G.neighborFinset u).filter (fun v => v ∈ K ∧ lay v = i + 1 + 1)
        ⊆ (G.neighborFinset u).erase w := by
      intro v hv
      rw [mem_filter] at hv
      obtain ⟨hv1, _, hv3⟩ := hv
      refine mem_erase.2 ⟨?_, hv1⟩
      rintro rfl
      omega
    have hc := card_le_card hsub
    have hwN : w ∈ G.neighborFinset u := by simpa using hwu.symm
    rw [card_erase_of_mem hwN, G.card_neighborFinset_eq_degree] at hc
    have := hdeg u hu.1
    omega
  have hrec : ∀ i, (K.filter (fun v => lay v = i + 1 + 1)).card ≤
      2 * (K.filter (fun v => lay v = i + 1)).card +
        ∑ v ∈ K.filter (fun v => lay v = i + 1), (G.degree v - 3) := by
    intro i
    refine (hcover (i + 1)).trans ?_
    refine (sum_le_sum (hfib i)).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm]
  have hbase : (K.filter (fun v => lay v = 0 + 1)).card ≤ 3 + (G.degree r - 3) := by
    refine (hcover 0).trans ?_
    rw [hL0, sum_singleton]
    have := hdeg r hr
    omega
  have hgrow : ∀ i, (K.filter (fun v => lay v = i + 1)).card ≤
      2 ^ i * (3 + ∑ j ∈ range (i + 1),
        ∑ v ∈ K.filter (fun v => lay v = j), (G.degree v - 3)) := by
    intro i
    induction i with
    | zero =>
      rw [sum_range_succ, sum_range_zero, hL0, sum_singleton, pow_zero, one_mul]
      have := hbase
      omega
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      have hr' := hrec n
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hS : ∑ v ∈ K.filter (fun v => lay v = n + 1), (G.degree v - 3) ≤
          2 ^ n * 2 * ∑ v ∈ K.filter (fun v => lay v = n + 1), (G.degree v - 3) := by
        calc _ = 1 * ∑ v ∈ K.filter (fun v => lay v = n + 1), (G.degree v - 3) :=
              (one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul (by omega) le_rfl
      linarith
  have hmaps : ∀ v ∈ K, lay v ∈ range (D + 1) := fun v hv =>
    mem_range.2 (Nat.lt_succ_of_le (hD v hv))
  have hcardK : K.card = ∑ i ∈ range (D + 1), (K.filter (fun v => lay v = i)).card :=
    card_eq_sum_card_fiberwise hmaps
  have hT : ∀ i, i ≤ D + 1 → ∑ j ∈ range i,
      ∑ v ∈ K.filter (fun v => lay v = j), (G.degree v - 3) ≤ ∑ v ∈ K, (G.degree v - 3) := by
    intro i hi
    calc _ ≤ ∑ j ∈ range (D + 1), ∑ v ∈ K.filter (fun v => lay v = j), (G.degree v - 3) :=
          sum_le_sum_of_subset (fun x hx => mem_range.2 (lt_of_lt_of_le (mem_range.1 hx) hi))
      _ = ∑ v ∈ K, (G.degree v - 3) := sum_fiberwise_of_maps_to hmaps _
  rw [hcardK, sum_range_succ', hL0, card_singleton]
  have hsum : ∑ i ∈ range D, (K.filter (fun v => lay v = i + 1)).card ≤
      ∑ i ∈ range D, 2 ^ i * (3 + ∑ v ∈ K, (G.degree v - 3)) := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.1 hi
    exact (hgrow i).trans (Nat.mul_le_mul le_rfl (by have := hT (i + 1) (by omega); omega))
  rw [← sum_mul] at hsum
  have hg := geom_two D
  have e : ∑ i ∈ range D, 2 ^ i = 2 ^ D - 1 := by omega
  rw [e] at hsum
  linarith

/-- **Component size.**  A window-free `K` (no induced `P13`), connected inside itself,
with `δ ≥ 3`, has `|K| ≤ 1 + 2047 (3 + σ_K)`. -/
theorem component_card_le (K : Finset V) (hno : NoInducedP13In G (↑K : Set V)) (r : V)
    (hr : r ∈ K) (hconn : ∀ v ∈ K, ∃ k, Reach G (↑K : Set V) r v k)
    (hdeg : ∀ v ∈ K, 3 ≤ G.degree v) :
    K.card ≤ 1 + (3 + ∑ v ∈ K, (G.degree v - 3)) * (2 ^ 11 - 1) := by
  have hreach : ∀ v ∈ K, ∃ k ≤ 11, Reach G (↑K : Set V) r v k := by
    intro v hv
    obtain ⟨k, g, hk, hw, h0, hk', _⟩ := short_walk G hno (hconn v hv)
    exact ⟨k, hk, g, hw, h0, hk'⟩
  obtain ⟨lay, hD, h0, hr0, hpred⟩ := exists_layering G K r hr 11 hreach
  exact layer_bound G K r hr lay 11 hD h0 hr0 hpred hdeg

/-! ## 6. Global window budget -/

/-- **Remainder budget.**  Over the components `C` of `G[R]` (sizes `κ`, surplus `s`, cuts
`b = e(K, W)`): with the component bound, density per component, bridgelessness (`b ≥ 2`)
and the join identity, `n ≤ 46078 ν + 3071 σ_W + 2047 σ_R`, `2c(R) ≤ 15ν + σ_W`, and
`σ_R + 6 c(R) ≤ |R| + 15ν + σ_W`. -/
theorem remainder_budget {ι : Type*} (C : Finset ι) (κ s b : ι → ℕ)
    (ν σW σR eRW ex R n : ℕ)
    (hκ : ∀ K ∈ C, κ K ≤ 1 + (3 + s K) * (2 ^ 11 - 1))
    (hdens : ∀ K ∈ C, s K + 6 ≤ κ K + b K)
    (hb : ∀ K ∈ C, 2 ≤ b K)
    (hR : R = ∑ K ∈ C, κ K) (hσR : σR = ∑ K ∈ C, s K) (hRW : eRW = ∑ K ∈ C, b K)
    (hjoin : eRW + 2 * ex = 15 * ν + σW) (hn : n = 13 * ν + R) :
    n ≤ 46078 * ν + 3071 * σW + 2047 * σR ∧ 2 * C.card ≤ 15 * ν + σW ∧
      σR + 6 * C.card ≤ R + 15 * ν + σW := by
  have h1 : R ≤ ∑ K ∈ C, (6142 + 2047 * s K) := by
    rw [hR]; apply sum_le_sum; intro K hK
    have := hκ K hK
    norm_num at this
    omega
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, ← hσR] at h1
  have h2 : ∑ K ∈ C, 2 ≤ eRW := by rw [hRW]; exact sum_le_sum hb
  rw [sum_const, smul_eq_mul] at h2
  have h3 : ∑ K ∈ C, (s K + 6) ≤ ∑ K ∈ C, (κ K + b K) := sum_le_sum hdens
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, ← hR, ← hσR, ← hRW] at h3
  refine ⟨by omega, by omega, by omega⟩

/-- **Window density.**  Density at `S = W` (`int W + 6 ≤ 4|W|`, `|W| = 13ν`) with
`int W = 24ν + 2e×` gives `e× ≤ 14ν − 3`, and then the join identity gives
`e(R, W) ≥ σ_W + 6 − 13ν`. -/
theorem window_density (ν ex intW σW eRW : ℕ) (hint : intW = 24 * ν + 2 * ex)
    (hdens : intW + 6 ≤ 4 * (13 * ν)) (hjoin : eRW + 2 * ex = 15 * ν + σW) :
    ex + 3 ≤ 14 * ν ∧ σW + 6 ≤ eRW + 13 * ν := by
  omega

/-! ## 7. Hub pieces inside a component: singleton pieces consume window edges -/

theorem succ_le_choose_two (m : ℕ) : m + 1 ≤ (m + 1 + 1).choose 2 := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
  have e : m + 1 + 1 - 1 = m + 1 := by omega
  rw [e]; nlinarith

theorem le_one_add_choose_two (c : ℕ) : c ≤ 1 + c.choose 2 := by
  rcases c with _ | _ | m
  · omega
  · omega
  · have := succ_le_choose_two m; omega

/-- `∑ k_Q ≤ 2 ∑ C(k_Q, 2) + #{Q : k_Q = 1}`: neighbours not in singleton pieces are
paired inside their piece. -/
theorem piece_pairs {ι : Type*} (P : Finset ι) (k : ι → ℕ) :
    ∑ Q ∈ P, k Q ≤ 2 * ∑ Q ∈ P, (k Q).choose 2 + (P.filter (fun Q => k Q = 1)).card := by
  rw [card_filter, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro Q _
  rcases h : k Q with _ | _ | m
  · split_ifs <;> omega
  · split_ifs <;> omega
  · have := succ_le_choose_two m
    split_ifs <;> omega

/-- A piece `Q` of `K − h` (all out-neighbours are `h` or window vertices) with exactly one
edge to `h` and cut `≥ 2` (bridgeless) sends at least one edge into the windows. -/
theorem singleton_piece_meets_W (Q W : Finset V) (h : V)
    (hbd : 2 ≤ ∑ u ∈ Q, (G.neighborFinset u \ Q).card)
    (hout : ∀ u ∈ Q, ∀ w, G.Adj u w → w ∉ Q → w = h ∨ w ∈ W)
    (hone : ∑ u ∈ Q, (if G.Adj u h then 1 else 0) = 1) :
    1 ≤ ∑ u ∈ Q, (G.neighborFinset u ∩ W).card := by
  have hpt : ∀ u ∈ Q, (G.neighborFinset u \ Q).card ≤
      (if G.Adj u h then 1 else 0) + (G.neighborFinset u ∩ W).card := by
    intro u hu
    have hsub : G.neighborFinset u \ Q ⊆
        (G.neighborFinset u).filter (fun w => w = h) ∪ (G.neighborFinset u ∩ W) := by
      intro w hw
      rw [mem_sdiff] at hw
      have hadj : G.Adj u w := by simpa using hw.1
      rcases hout u hu w hadj hw.2 with e | e
      · exact mem_union_left _ (mem_filter.2 ⟨hw.1, e⟩)
      · exact mem_union_right _ (mem_inter.2 ⟨hw.1, e⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right ?_ _))
    split_ifs with hh
    · apply card_le_one.2
      intro a ha b hb
      rw [mem_filter] at ha hb
      rw [ha.2, hb.2]
    · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
      intro w hw e
      apply hh
      rw [← e]
      simpa using hw
  have := sum_le_sum hpt
  rw [sum_add_distrib, hone] at this
  omega

/-! ## 8. Hub clusters: C4 double count and density slack -/

theorem cluster_count (hC4 : C4Free G) (A : Finset V) :
    ∑ a ∈ A, G.degree a ≤ (A.biUnion (fun v => G.neighborFinset v)).card + A.card.choose 2 := by
  have h1 : ∑ a ∈ A, G.degree a =
      ∑ a ∈ A, ((A.biUnion (fun v => G.neighborFinset v)).filter (fun w => G.Adj a w)).card := by
    apply sum_congr rfl
    intro a ha
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp only [mem_filter, mem_biUnion, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => ⟨⟨a, ha, h⟩, h⟩, fun h => h.2⟩
  have h2 : ∑ a ∈ A, ((A.biUnion (fun v => G.neighborFinset v)).filter (fun w => G.Adj a w)).card =
      ∑ w ∈ A.biUnion (fun v => G.neighborFinset v), (A.filter (fun a => G.Adj a w)).card := by
    simp only [card_filter]
    exact sum_comm
  have h3 : ∑ w ∈ A.biUnion (fun v => G.neighborFinset v), ((A.filter (fun a => G.Adj a w)).card).choose 2
      ≤ A.card.choose 2 := by
    have e1 : ∑ w ∈ A.biUnion (fun v => G.neighborFinset v), ((A.filter (fun a => G.Adj a w)).card).choose 2
        = ((A.biUnion (fun v => G.neighborFinset v)).sigma
            (fun w => powersetCard 2 (A.filter (fun a => G.Adj a w)))).card := by
      rw [card_sigma]
      exact sum_congr rfl (fun w _ => (card_powersetCard 2 _).symm)
    rw [e1, ← card_powersetCard 2 A]
    apply card_le_card_of_injOn (fun x => x.2)
    · rintro ⟨w, P⟩ hx
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hx ⊢
      exact ⟨hx.2.1.trans (filter_subset _ _), hx.2.2⟩
    · rintro ⟨w, P⟩ hx ⟨w', P'⟩ hy hxy
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hx hy
      simp only at hxy
      subst hxy
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hx.2.2
      have ha := hx.2.1 (mem_insert_self a {b})
      have hb := hx.2.1 (mem_insert_of_mem (mem_singleton_self b))
      have ha' := hy.2.1 (mem_insert_self a {b})
      have hb' := hy.2.1 (mem_insert_of_mem (mem_singleton_self b))
      rw [mem_filter] at ha hb ha' hb'
      have := hC4 a b w w' hab ha.2 hb.2 ha'.2 hb'.2
      subst this
      rfl
  have h4 : ∑ w ∈ A.biUnion (fun v => G.neighborFinset v), (A.filter (fun a => G.Adj a w)).card ≤
      ∑ w ∈ A.biUnion (fun v => G.neighborFinset v), (1 + ((A.filter (fun a => G.Adj a w)).card).choose 2) :=
    sum_le_sum (fun w _ => le_one_add_choose_two _)
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at h4
  omega

theorem degree_split (S : Finset V) :
    ∑ u ∈ S, G.degree u
      = ∑ u ∈ S, (G.neighborFinset u ∩ S).card + ∑ u ∈ S, (G.neighborFinset u \ S).card := by
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro u _
  rw [← G.card_neighborFinset_eq_degree, ← card_sdiff_add_card_inter (G.neighborFinset u) S]
  ring

theorem slack_formula (S : Finset V) :
    (4 * S.card - 6 - ∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℤ)
      = S.card + ∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) - 6
        - ∑ u ∈ S, ((G.degree u : ℤ) - 3) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (degree_split G S)
  simp only [Nat.cast_add, Nat.cast_sum] at h
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, h]
  push_cast
  ring

/-- **Cluster slack.**  For an independent hub set `A` and `S = A ∪ N(A)`:
`slack(S) ≥ 4|A| − C(|A|,2) + ∂S − 6 − σ_{N(A)}`. -/
theorem cluster_slack (hC4 : C4Free G) (A : Finset V)
    (hind : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) :
    (4 * (A ∪ A.biUnion (fun v => G.neighborFinset v)).card - 6
        - ∑ u ∈ A ∪ A.biUnion (fun v => G.neighborFinset v),
            (G.neighborFinset u ∩ (A ∪ A.biUnion (fun v => G.neighborFinset v))).card : ℤ)
      ≥ 4 * (A.card : ℤ) - (A.card.choose 2 : ℤ)
        + ∑ u ∈ A ∪ A.biUnion (fun v => G.neighborFinset v),
            ((G.neighborFinset u \ (A ∪ A.biUnion (fun v => G.neighborFinset v))).card : ℤ) - 6
        - ∑ u ∈ A.biUnion (fun v => G.neighborFinset v), ((G.degree u : ℤ) - 3) := by
  have hdisj : Disjoint A (A.biUnion (fun v => G.neighborFinset v)) := by
    rw [disjoint_left]
    intro a ha hN
    rw [mem_biUnion] at hN
    obtain ⟨b, hb, hab⟩ := hN
    exact hind b hb a ha (by simpa using hab)
  have hs := slack_formula G (A ∪ A.biUnion (fun v => G.neighborFinset v))
  have hsplit : ∑ u ∈ A ∪ A.biUnion (fun v => G.neighborFinset v), ((G.degree u : ℤ) - 3) =
      ∑ u ∈ A, ((G.degree u : ℤ) - 3) + ∑ u ∈ A.biUnion (fun v => G.neighborFinset v), ((G.degree u : ℤ) - 3) :=
    sum_union hdisj
  have hcard : (A ∪ A.biUnion (fun v => G.neighborFinset v)).card = A.card + (A.biUnion (fun v => G.neighborFinset v)).card := by
    rw [← card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 hdisj, card_empty, add_zero]
  have hc := cluster_count G hC4 A
  have hcZ : (∑ a ∈ A, (G.degree a : ℤ)) ≤
      ((A.biUnion (fun v => G.neighborFinset v)).card : ℤ) + (A.card.choose 2 : ℤ) := by exact_mod_cast hc
  have hA3 : ∑ a ∈ A, ((G.degree a : ℤ) - 3) = ∑ a ∈ A, (G.degree a : ℤ) - 3 * A.card := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  have hcardZ : ((A ∪ A.biUnion (fun v => G.neighborFinset v)).card : ℤ) =
      (A.card : ℤ) + ((A.biUnion (fun v => G.neighborFinset v)).card : ℤ) := by exact_mod_cast hcard
  linarith

/-- Clusters of at most 8 hubs with cubic `N(A)` and cut `≥ 2` never bind density. -/
theorem small_cluster_nonbinding (a : ℕ) (h1 : 1 ≤ a) (h8 : a ≤ 8) :
    0 ≤ 4 * (a : ℤ) - (a.choose 2 : ℤ) + 2 - 6 := by
  interval_cases a <;> decide

/-! ## 9. Inventory additions (ranked add-and-test) -/

/-- **`def⁺(R) ≤ e(R,W)` is automatic, with exact slack.**  For any `R` with `δ ≥ 3`:
`def⁺(R) + ∑_R min(e(v, V∖R), deg v − 3) = e(R, V∖R)`.  The slack of the ledger fact is
`∑_R min(e(v,W), d_v − 3) ∈ [0, σ_R]`; it vanishes iff no hub of `R` touches a window. -/
theorem remainder_deficiency_slack (R : Finset V) (hdeg : ∀ v ∈ R, 3 ≤ G.degree v) :
    ∑ v ∈ R, (3 - (G.neighborFinset v ∩ R).card) +
        ∑ v ∈ R, min (G.neighborFinset v \ R).card (G.degree v - 3)
      = ∑ v ∈ R, (G.neighborFinset v \ R).card := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have h1 := card_sdiff_add_card_inter (G.neighborFinset v) R
  rw [G.card_neighborFinset_eq_degree] at h1
  have := hdeg v hv
  omega

/-- **The window count cancels out of the capacity layer.**  With the token count
`|𝔗| + 24ν = 4n + 3σ + 39ν`, the overload-of-fits bound
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)` and `|Π_blk| ≤ C(σ,2)` give the `ν`-free
`c²K + 2M₀(8n + σ) ≤ 2 C(σ,2)`; and G2 is equivalent to G3 whatever `|𝔗|` is. -/
theorem capacity_nu_cancels (n σ ν T blk free P B M₀ c2K : ℤ)
    (htok : T + 24 * ν = 4 * n + 3 * σ + 39 * ν) (hpart : blk + free = P) :
    ((c2K + 2 * M₀ * (8 * n + σ - T) ≤ 2 * (free - B) + 2 * (blk - M₀ * T)) ↔
      (c2K + 2 * M₀ * (8 * n + σ) ≤ 2 * (P - B))) ∧
    (c2K + 2 * M₀ * (8 * n + σ - T) ≤ 2 * (blk - M₀ * T) → blk ≤ P →
      c2K + 2 * M₀ * (8 * n + σ) ≤ 2 * P) ∧
    8 * n + σ - T = 4 * n - 2 * σ - 15 * ν := by
  refine ⟨⟨fun h => by nlinarith, fun h => by nlinarith⟩, fun h hb => by nlinarith, by linarith⟩

/-- **Hub envelope from C4 double counting.**  For the independent hub set `H`:
`∑_H deg + |H| ≤ n + C(|H|,2)`, i.e. `σ + 4|H| ≤ n + C(|H|,2)`. -/
theorem hub_envelope (hC4 : C4Free G) (H : Finset V) (hind : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b) :
    ∑ a ∈ H, G.degree a + H.card ≤ Fintype.card V + H.card.choose 2 := by
  have hc := cluster_count G hC4 H
  have hdisj : Disjoint H (H.biUnion (fun v => G.neighborFinset v)) := by
    rw [disjoint_left]
    intro a ha hN
    rw [mem_biUnion] at hN
    obtain ⟨b, hb, hab⟩ := hN
    exact hind b hb a ha (by simpa using hab)
  have hcard : H.card + (H.biUnion (fun v => G.neighborFinset v)).card ≤ Fintype.card V := by
    rw [← card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 hdisj, card_empty, add_zero]
    exact card_le_univ _
  omega

/-- numeric: with `∑_H deg = 3|H| + σ`, for `3 ≤ |H| ≤ 6` the hub envelope gives
`σ ≤ n − 9`, sharper than the six-vertex envelope `σ ≤ n − 8`. -/
theorem hub_envelope_sharp (n σ h : ℕ) (hh3 : 3 ≤ h) (hh6 : h ≤ 6)
    (henv : 3 * h + σ + h ≤ n + h.choose 2) : σ + 9 ≤ n := by
  interval_cases h <;> simp [Nat.choose] at henv <;> omega

/-- An independent set of a 13-vertex path has at most 7 vertices. -/
theorem indep_in_P13 (I : Finset ℕ) (hI : I ⊆ range 13) (hnc : ∀ i ∈ I, i + 1 ∉ I) :
    I.card ≤ 7 := by
  have hinj : Set.InjOn (fun a : ℕ => a / 2) I := by
    intro a ha b hb hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have e : b = a + 1 := by omega
      exact hnc a ha (by rw [← e]; exact hb)
    · have e : a = b + 1 := by omega
      exact hnc b hb (by rw [← e]; exact ha)
  rw [← card_image_of_injOn hinj]
  calc _ ≤ (range 7).card := card_le_card (by
        intro x hx
        rw [mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        have := mem_range.1 (hI ha)
        exact mem_range.2 (by omega))
    _ = 7 := card_range 7

/-- **At most 7 hubs per window** (`H` independent, window induced). Hence
`|H ∩ W| ≤ 7ν` and at least `|H| − 7ν` hubs lie in `R`. -/
theorem window_hubs_le_seven (H : Finset V) (hind : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b)
    (g : ℕ → V) (hg : InducedSeq G 12 g) :
    ((range 13).filter (fun t => g t ∈ H)).card ≤ 7 :=
  indep_in_P13 _ (filter_subset _ _) (fun i hi hi1 => by
    simp only [mem_filter, mem_range] at hi hi1
    exact hind _ hi.2 _ hi1.2 ((hg.2 i (by omega) (i + 1) (by omega)).2 (Or.inl rfl)))

/-- **Pair-count deficit ⇒ `n ≥ K`.**  From G3 `c²K + 2M₀(8n+σ) ≤ 2(C(σ,2) − B)`
with `n ≤ c²`, `2C(σ,2) ≤ σ²`, `σ ≤ n`, nonnegative `K, M₀, B`: `K ≤ n`.  So `n` is at
least `K ≈ 4.14·10⁴⁷`, and every window constant of this file is negligible against it. -/
theorem pair_deficit_forces_order (n σ c2 K M₀ B P : ℤ) (hn : 0 < n) (hc : n ≤ c2)
    (hK : 0 ≤ K) (hM : 0 ≤ M₀) (hB : 0 ≤ B) (hσ0 : 0 ≤ σ) (hσ : σ ≤ n)
    (hP : 2 * P ≤ σ * σ) (hG3 : c2 * K + 2 * M₀ * (8 * n + σ) ≤ 2 * (P - B)) : K ≤ n := by
  have h1 : n * K ≤ c2 * K := mul_le_mul_of_nonneg_right hc hK
  have h2 : 0 ≤ 2 * M₀ * (8 * n + σ) := by positivity
  have h3 : σ * σ ≤ n * n := mul_le_mul hσ hσ hσ0 (le_of_lt hn)
  have h4 : n * K ≤ n * n := by linarith
  exact le_of_mul_le_mul_left h4 hn

/-- **Cut hubs.**  The component lemma (`d_h = 2·#blocks` when `G − h` is
disconnected) and the one-boundary shape (`deg = 4`) give exactly two blocks. -/
theorem cut_hub_two_blocks (d blocks : ℕ) (hpar : d = 2 * blocks) (hshape : d = 4) :
    blocks = 2 := by omega

/-! ## 10. Window capacity in the capacity layer (abstract charge `θ : Π → Option 𝔗`) -/

section Capacity

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- The load of a token class `C`: pairs of `Π` charged into `C`.  It is the sum of the
per-token loads (single-valued charge ⇒ disjoint fibres). -/
theorem class_load_eq_sum (Pi : Finset P) (θ : P → Option T) (C : Finset T) :
    (Pi.filter (fun π => ∃ t ∈ C, θ π = some t)).card =
      ∑ t ∈ C, (Pi.filter (fun π => θ π = some t)).card := by
  rw [← card_biUnion]
  · congr 1
    ext π
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨hπ, t, ht, he⟩; exact ⟨t, ht, hπ, he⟩
    · rintro ⟨t, ht, hπ, he⟩; exact ⟨hπ, t, ht, he⟩
  · intro t _ t' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro π h1 h2
    simp only [mem_filter] at h1 h2
    exact hne (Option.some_injective _ (h1.2.symm.trans h2.2))

/-- **Capped window load.**  If every window token carries load `≤ M₀`, the window load
is at most `M₀ |𝔗_W| = M₀ (15ν + σ_W)`. -/
theorem capped_window_load (Pi : Finset P) (θ : P → Option T) (TW : Finset T) (M₀ ν σW : ℕ)
    (hcap : ∀ t ∈ TW, (Pi.filter (fun π => θ π = some t)).card ≤ M₀)
    (hTW : TW.card = 15 * ν + σW) :
    (Pi.filter (fun π => ∃ t ∈ TW, θ π = some t)).card ≤ M₀ * (15 * ν + σW) := by
  rw [class_load_eq_sum, ← hTW, mul_comm]
  exact (sum_le_card_nsmul _ _ _ hcap).trans (by rw [smul_eq_mul])

/-- **Window-load lower bound from geometry.**  Any family `A ⊆ Π` of pairs each charged
into `𝔗_W` (e.g. the coordinate-blocked pairs whose support meets `R` and `W`, by
`coordinate_spread_window_charge`) is at most the window load. -/
theorem window_load_ge (Pi : Finset P) (θ : P → Option T) (TW : Finset T) (A : Finset P)
    (hA : A ⊆ Pi) (hch : ∀ π ∈ A, ∃ t ∈ TW, θ π = some t) :
    A.card ≤ (Pi.filter (fun π => ∃ t ∈ TW, θ π = some t)).card :=
  card_le_card (fun π hπ => mem_filter.2 ⟨hA hπ, hch π hπ⟩)

/-- **Capped arm, combined.**  Coordinate-blocked pairs spread across `R` and `W`:
`13·|A| ≤ M₀ (15n + 13σ_W)` (using `13ν ≤ n`). -/
theorem capped_spread_pairs (Pi : Finset P) (θ : P → Option T) (TW : Finset T) (A : Finset P)
    (M₀ ν σW n : ℕ) (hA : A ⊆ Pi) (hch : ∀ π ∈ A, ∃ t ∈ TW, θ π = some t)
    (hcap : ∀ t ∈ TW, (Pi.filter (fun π => θ π = some t)).card ≤ M₀)
    (hTW : TW.card = 15 * ν + σW) (hν : 13 * ν ≤ n) :
    A.card ≤ M₀ * (15 * ν + σW) ∧ 13 * A.card ≤ M₀ * (15 * n + 13 * σW) := by
  have h1 := (window_load_ge Pi θ TW A hA hch).trans (capped_window_load Pi θ TW M₀ ν σW hcap hTW)
  refine ⟨h1, ?_⟩
  have h2 : M₀ * (15 * (13 * ν)) ≤ M₀ * (15 * n) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Cross-region pairs split.**  Pairs `A` (seed meeting `R` and `W`) are free,
early-blocked (vertex/incidence/buffer, charged to `𝔗_R ∪ 𝔗_prim`), chord-blocked, or
coordinate-blocked — the last are all window-charged. -/
theorem cross_region_split (A F Vb Ch Co Wch : Finset P)
    (hcover : A ⊆ F ∪ Vb ∪ Ch ∪ Co) (hCo : A ∩ Co ⊆ Wch) :
    A.card ≤ (A ∩ F).card + (A ∩ Vb).card + (A ∩ Ch).card + Wch.card := by
  have hsub : A ⊆ (A ∩ F) ∪ (A ∩ Vb) ∪ (A ∩ Ch) ∪ (A ∩ Co) := by
    intro π hπ
    have := hcover hπ
    simp only [mem_union, mem_inter] at this ⊢
    tauto
  calc A.card ≤ ((A ∩ F) ∪ (A ∩ Vb) ∪ (A ∩ Ch) ∪ (A ∩ Co)).card := card_le_card hsub
    _ ≤ (A ∩ F).card + (A ∩ Vb).card + (A ∩ Ch).card + (A ∩ Co).card := by
        refine (card_union_le _ _).trans ?_
        refine Nat.add_le_add_right ((card_union_le _ _).trans ?_) _
        exact Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_left (card_le_card hCo) _

end Capacity

/-- **The class-split G2 (ν no longer cancels class by class).**  With
`|Π_blk| = L_W + L_R + L_P`, `|𝔗_W| = 15ν + σ_W`, `|𝔗_R| = σ_R`, `|𝔗_P| = 4n + 2σ`,
`σ = σ_W + σ_R`, G2 reads
`c²K + 2M₀(4n − 2σ − 15ν) ≤ 2(|Π_free| − B) + 2(L_W − M₀(15ν+σ_W)) + 2(L_R − M₀σ_R)
  + 2(L_P − M₀(4n+2σ))`. -/
theorem class_split_G2 (n σ σW σR ν T blk free B M₀ c2K LW LR LP : ℤ)
    (hblk : blk = LW + LR + LP) (hσ : σ = σW + σR)
    (hT : T = (15 * ν + σW) + σR + (4 * n + 2 * σ))
    (hG2 : c2K + 2 * M₀ * (8 * n + σ - T) ≤ 2 * (free - B) + 2 * (blk - M₀ * T)) :
    c2K + 2 * M₀ * (4 * n - 2 * σ - 15 * ν) ≤
      2 * (free - B) + 2 * (LW - M₀ * (15 * ν + σW)) + 2 * (LR - M₀ * σR) +
        2 * (LP - M₀ * (4 * n + 2 * σ)) := by
  subst hblk hT hσ; linear_combination hG2

/-- **Fits arm, per class.**  If `|Π_free| ≤ B` then one of the three classes carries at
least a third of the overload: `3(L_c − M₀|𝔗_c|) ≥ c²K/2 + M₀(4n − 2σ − 15ν)`. -/
theorem fits_class_pigeonhole (X a b c : ℤ) (h : X ≤ a + b + c) :
    X ≤ 3 * a ∨ X ≤ 3 * b ∨ X ≤ 3 * c := by
  by_contra hc; push Not at hc; linarith [hc.1, hc.2.1, hc.2.2]

/-! ## 11. Same-hub pairs, vertex-token capacity, short returns -/

theorem sq_eq_two_choose_add (e : ℕ) : e ^ 2 = 2 * e.choose 2 + e := by
  have h2 : 2 ∣ e * (e - 1) := (Nat.even_mul_pred_self e).two_dvd
  have hc : e.choose 2 * 2 = e * (e - 1) := by
    rw [Nat.choose_two_right]; exact Nat.div_mul_cancel h2
  rcases e with _ | m
  · simp
  · have : m + 1 - 1 = m := by omega
    rw [this] at hc
    nlinarith

/-- **Cauchy at the hubs**: `σ² ≤ |H| (2 Σ_h C(e_h,2) + σ)`, `e_h = d_h − 3`,
`σ = Σ_h e_h`.  `Σ_h C(e_h,2)` is the number of same-hub port pairs. -/
theorem sameHub_cauchy {ι : Type*} (H : Finset ι) (e : ι → ℕ) :
    (∑ h ∈ H, e h) ^ 2 ≤ H.card * (2 * ∑ h ∈ H, (e h).choose 2 + ∑ h ∈ H, e h) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := H) (f := e)
  have hsq : ∑ h ∈ H, e h ^ 2 = 2 * ∑ h ∈ H, (e h).choose 2 + ∑ h ∈ H, e h := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun h _ => sq_eq_two_choose_add (e h)
  rw [← hsq]; exact hcs

/-- A token class of card `N` whose tokens are all capped at `M₀` carries `≤ M₀ N`. -/
theorem capped_class_load {P T : Type*} [DecidableEq P] [DecidableEq T] (Pi : Finset P)
    (θ : P → Option T) (C : Finset T) (M₀ : ℕ)
    (hcap : ∀ t ∈ C, (Pi.filter (fun π => θ π = some t)).card ≤ M₀) :
    (Pi.filter (fun π => ∃ t ∈ C, θ π = some t)).card ≤ M₀ * C.card := by
  rw [class_load_eq_sum, mul_comm]
  exact (sum_le_card_nsmul _ _ _ hcap).trans (by rw [smul_eq_mul])

/-- G3 in the form `n·K ≤ σ²`. -/
theorem pair_deficit_nK (n σ c2 K M₀ B P : ℤ) (hc : n ≤ c2) (hK : 0 ≤ K) (hM : 0 ≤ M₀)
    (hB : 0 ≤ B) (hσ0 : 0 ≤ σ) (hn : 0 ≤ n) (hP : 2 * P ≤ σ * σ)
    (hG3 : c2 * K + 2 * M₀ * (8 * n + σ) ≤ 2 * (P - B)) : n * K ≤ σ * σ := by
  have h1 : n * K ≤ c2 * K := mul_le_mul_of_nonneg_right hc hK
  have h2 : 0 ≤ 2 * M₀ * (8 * n + σ) := by positivity
  linarith

/-- **Capped arm ⇒ many hubs.**  Same-hub pairs are early-blocked and charged to the
`n + σ_R` vertex tokens (`sameHub_early_recorded`, `early_charge`), so in the capped arm
`Σ_h C(e_h,2) ≤ M₀ (n + σ_R)`.  With Cauchy and G3 (`nK ≤ σ²`):
`K ≤ |H| (4M₀ + 1)`. -/
theorem capped_hub_lower (n σ σR Hc S M₀ K : ℕ) (hn : 0 < n) (hσR : σR ≤ σ) (hσn : σ ≤ n)
    (hcau : σ ^ 2 ≤ Hc * (2 * S + σ)) (hcap : S ≤ M₀ * (n + σR)) (hK : n * K ≤ σ ^ 2) :
    K ≤ Hc * (4 * M₀ + 1) := by
  have h1 : 2 * S + σ ≤ n * (4 * M₀ + 1) := by
    have : M₀ * (n + σR) ≤ M₀ * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h2 : n * K ≤ n * (Hc * (4 * M₀ + 1)) := by
    calc n * K ≤ σ ^ 2 := hK
      _ ≤ Hc * (2 * S + σ) := hcau
      _ ≤ Hc * (n * (4 * M₀ + 1)) := Nat.mul_le_mul_left _ h1
      _ = n * (Hc * (4 * M₀ + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left h2 hn

/-- **Returns inside `R` are short.**  Let `x ~ h`, `s` a neighbour of `x` with `s ≠ h`,
and `L` the length of a shortest `x → h` walk avoiding the edge `hx` (the canonical
`R_p`, `selectOfReachable_length_le`).  If `s` reaches `h` inside a window-free `S ∌ x`,
then `L ≤ 12`.  So a return of length `≥ 13` leaves every window-free set: it meets
`W ∪ {x}`. -/
theorem return_short {S : Set V} (hno : NoInducedP13In G S) {x h s : V} (hxh : G.Adj x h)
    (hxs : G.Adj x s) (hsh : s ≠ h) (hxS : x ∉ S) (L : ℕ)
    (hmin : ∀ k (g : ℕ → V), (∀ t < k, G.Adj (g t) (g (t + 1)) ∧
        ¬ (g t = x ∧ g (t + 1) = h) ∧ ¬ (g t = h ∧ g (t + 1) = x)) →
        g 0 = x → g k = h → L ≤ k)
    (hconn : ∃ k, Reach G S s h k) : L ≤ 12 := by
  obtain ⟨k, g, hk, hw, h0, hkh, _, _⟩ := short_walk G hno hconn
  have := hmin (k + 1) (hubCycle x g) (fun t ht => ?_) (by simp [hubCycle]) (by
    simp [hubCycle, hkh])
  · omega
  · unfold hubCycle
    have hxne : ∀ t ≤ k, g t ≠ x := fun t ht e => hxS (e ▸ hw.2 t ht)
    by_cases h0' : t = 0
    · subst h0'
      simp only [if_true, show (0 + 1 = 0) = False from by simp, if_false, Nat.add_sub_cancel]
      rw [h0]
      refine ⟨hxs, fun e => hsh e.2, fun e => (G.ne_of_adj hxh) e.1⟩
    · rw [if_neg h0', if_neg (by omega)]
      have e1 : t + 1 - 1 = t - 1 + 1 := by omega
      rw [e1]
      refine ⟨hw.1 _ (by omega), fun e => hxne _ (by omega) e.1, fun e => hxne _ (by omega) e.2⟩

/-- **Capped arm with one hub is closed.**  If `|H| = 1` every pair is a same-hub pair,
hence early-blocked, so `|Π_free| = 0`; but the capped free excess
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)` with `c²K > 0`, `|𝔗| ≤ 8n + σ`,
`B ≥ 0` forces `|Π_free| > 0`. -/
theorem capped_single_hub_closed (free B M₀ c2K n σ T : ℤ) (hfree : free = 0)
    (hc2K : 0 < c2K) (hB : 0 ≤ B) (hM : 0 ≤ M₀) (hT : T ≤ 8 * n + σ)
    (hex : c2K + 2 * M₀ * (8 * n + σ - T) ≤ 2 * (free - B)) : False := by
  have : 0 ≤ 2 * M₀ * (8 * n + σ - T) := by
    have : 0 ≤ 8 * n + σ - T := by linarith
    positivity
  linarith

/-- **Capped arm, general `|H|`.**  Same-hub pairs are never free, so
`|Π_free| ≤ C(σ,2) − Σ_h C(e_h,2)`; with Cauchy `σ² ≤ |H|(2Σ_h C(e_h,2) + σ)` and the
capped free excess this gives
`|H| (c²K + 2M₀(8n + σ − |𝔗|) + 2B) ≤ (|H| − 1) σ²`. -/
theorem capped_free_hubs (free B M₀ c2K n σ T S Hc : ℤ) (hHc : 0 < Hc)
    (hfree : 2 * free ≤ σ * (σ - 1) - 2 * S)
    (hcau : σ ^ 2 ≤ Hc * (2 * S + σ))
    (hex : c2K + 2 * M₀ * (8 * n + σ - T) ≤ 2 * (free - B)) :
    Hc * (c2K + 2 * M₀ * (8 * n + σ - T) + 2 * B) ≤ (Hc - 1) * σ ^ 2 := by
  have h1 : Hc * (c2K + 2 * M₀ * (8 * n + σ - T) + 2 * B) ≤ Hc * (2 * free) := by
    apply mul_le_mul_of_nonneg_left _ hHc.le; linarith
  have h2 : Hc * (2 * free) ≤ Hc * (σ * (σ - 1) - 2 * S) :=
    mul_le_mul_of_nonneg_left hfree hHc.le
  nlinarith

/-! ## 12. Clause-(e) pairs: partition and the `r_π` split -/

/-- **Exact partition of `Π` by canonical kind** ((d) empty at G): free, early (vertex
blockers of (a)/(b)), chord (f), target-response (e).  Hence
`|Π_e| = C(σ,2) − |Π_free| − |Π_early| − |Π_chord|`; in the fits arm
`|Π_early| + |Π_chord| + |Π_e| ≥ C(σ,2) − B`. -/
theorem late_partition (P free early chord E B : ℕ) (hpart : free + early + chord + E = P)
    (hfit : free ≤ B) : E + P = P + P - free - early - chord ∧ P ≤ early + chord + E + B := by
  omega

/-- **The `r_π` split of a residual target defect** on `insert r D`: either one of the
two separated coordinates is `r_π` (then the witness carrier contains `X_π`), or both are
determiners. -/
theorem defect_split {α : Type*} [DecidableEq α] (r a b : α) (D : Finset α)
    (ha : a ∈ insert r D) (hb : b ∈ insert r D) :
    a = r ∨ b = r ∨ (a ∈ D ∧ b ∈ D) := by
  rw [mem_insert] at ha hb
  tauto

/-! ## 13. The local algebra in graph form, and the position of a carrier `Z` -/

/-- **Local algebra, gap 2.**  A vertex off a window cannot attach at two coordinates at
distance 2 (it would close a `C4`). -/
theorem attach_no_gap_two (hC4 : C4Free G) {g : ℕ → V} (hg : InducedSeq G 12 g) {v : V}
    (hv : ∀ t ≤ 12, g t ≠ v) {a : ℕ} (ha : a + 2 ≤ 12)
    (h1 : G.Adj v (g a)) (h2 : G.Adj v (g (a + 2))) : False := by
  have hne : g a ≠ g (a + 2) := fun e => by
    have := hg.1 a (by omega) (a + 2) ha e; omega
  have hm1 : G.Adj (g a) (g (a + 1)) := (hg.2 a (by omega) (a + 1) (by omega)).2 (Or.inl rfl)
  have hm2 : G.Adj (g (a + 2)) (g (a + 1)) :=
    (hg.2 (a + 2) ha (a + 1) (by omega)).2 (Or.inr rfl)
  exact hv (a + 1) (by omega) (hC4 (g a) (g (a + 2)) (g (a + 1)) v hne hm1 hm2 h1.symm h2.symm)

/-- **Local algebra: at most 7 attachments per window** (the census: every legal label
has size `≤ 7`).  Injection `t ↦ (⌊t/4⌋, t mod 2)` into 7 slots. -/
theorem attach_le_seven (hC4 : C4Free G) {g : ℕ → V} (hg : InducedSeq G 12 g) {v : V}
    (hv : ∀ t ≤ 12, g t ≠ v) :
    ((range 13).filter (fun t => G.Adj v (g t))).card ≤ 7 := by
  have hinj : Set.InjOn (fun t : ℕ => (t / 4, t % 2))
      ((range 13).filter (fun t => G.Adj v (g t)) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, Prod.mk.injEq] at ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact attach_no_gap_two G hC4 hg hv (a := a) (by omega) ha.2 (by
        have : b = a + 2 := by omega
        rw [← this]; exact hb.2)
    · exact attach_no_gap_two G hC4 hg hv (a := b) (by omega) hb.2 (by
        have : a = b + 2 := by omega
        rw [← this]; exact ha.2)
  rw [← card_image_of_injOn hinj]
  calc _ ≤ (((range 3) ×ˢ (range 2)) ∪ {(3, 0)} : Finset (ℕ × ℕ)).card := by
        apply card_le_card
        intro x hx
        simp only [mem_image, mem_filter, mem_range] at hx
        obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hx
        simp only [mem_union, mem_product, mem_range, mem_singleton, Prod.mk.injEq]
        omega
    _ = 7 := by decide

/-- **A vertex of degree `≥ 3` cannot have all its neighbours on one window.**  Hence a
carrier `Z` with an interior tight vertex `y` (all neighbours of `y` in `Z`,
`deg y = 3`) is never contained in a single
window. -/
theorem interior_not_in_window {g : ℕ → V} (hg : InducedSeq G 12 g) {i : ℕ} (hi : i ≤ 12)
    (hN : ∀ w, G.Adj (g i) w → ∃ t ≤ 12, w = g t) : G.degree (g i) ≤ 2 := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  refine (card_le_card (t := ({g (i - 1), g (i + 1)} : Finset V)) ?_).trans card_le_two
  intro w hw
  have hadj : G.Adj (g i) w := by simpa using hw
  obtain ⟨t, ht, rfl⟩ := hN w hadj
  have := (hg.2 i hi t ht).1 hadj
  simp only [mem_insert, mem_singleton]
  rcases this with h | h
  · right; rw [← h]
  · left; rw [← h]; congr 1

/-- A walk from outside `W` into `W` has a crossing step. -/
theorem seq_crossing (W : Set V) {k : ℕ} {g : ℕ → V} (hw : ∀ t < k, G.Adj (g t) (g (t + 1)))
    (h0 : g 0 ∉ W) (hk : g k ∈ W) :
    ∃ t < k, g t ∉ W ∧ g (t + 1) ∈ W ∧ G.Adj (g t) (g (t + 1)) := by
  induction k with
  | zero => exact absurd hk h0
  | succ k ih =>
    by_cases hmid : g k ∈ W
    · obtain ⟨t, ht, h⟩ := ih (fun t ht => hw t (by omega)) hmid
      exact ⟨t, by omega, h⟩
    · exact ⟨k, by omega, hmid, hk, hw k (by omega)⟩

/-- **Position of a connected carrier `Z` against the windows.**  Either `Z` misses
`W` — and then (window maximality) any two vertices of `Z` are joined inside `Z` by an
induced path of length `≤ 11`, i.e. `diam G[Z] ≤ 11` — or `Z` contains an `R`–`W`
edge, or `Z ⊆ W`. -/
theorem carrier_position (W : Set V) (hmax : ∀ g, InducedSeq G 12 g → ∃ t ≤ 12, g t ∈ W)
    (Z : Set V) (hconn : ∀ u ∈ Z, ∀ v ∈ Z, ∃ k, Reach G Z u v k) :
    (∀ u ∈ Z, ∀ v ∈ Z, ∃ k ≤ 11, ∃ g, SWalk G Z k g ∧ g 0 = u ∧ g k = v ∧ InducedSeq G k g) ∨
      (∃ a b, a ∈ Z ∧ b ∈ Z ∧ a ∉ W ∧ b ∈ W ∧ G.Adj a b) ∨ (∀ v ∈ Z, v ∈ W) := by
  by_cases hR : ∀ v ∈ Z, v ∉ W
  · left
    intro u hu v hv
    obtain ⟨k, g, hk, hw, h0, hkv, hind, _⟩ :=
      short_walk G (noP13_of_disjoint G W hmax Z hR) (hconn u hu v hv)
    exact ⟨k, hk, g, hw, h0, hkv, hind⟩
  · push Not at hR
    obtain ⟨w, hwZ, hwW⟩ := hR
    by_cases hall : ∀ v ∈ Z, v ∈ W
    · exact Or.inr (Or.inr hall)
    · push Not at hall
      obtain ⟨r, hrZ, hrW⟩ := hall
      obtain ⟨k, g, hw, h0, hk⟩ := hconn r hrZ w hwZ
      obtain ⟨t, ht, h1, h2, h3⟩ := seq_crossing G W hw.1 (h0 ▸ hrW) (hk ▸ hwW)
      exact Or.inr (Or.inl ⟨g t, g (t + 1), hw.2 t (by omega), hw.2 (t + 1) (by omega),
        h1, h2, h3⟩)

/-! ## 14. `Z ⊆ W` forces a cross-window edge at an interior vertex -/

/-- If a vertex `g i` of a window has degree `≥ 3` and all its neighbours lie in `W`,
one neighbour lies in `W` off this window: a cross-window edge. -/
theorem interior_in_W_cross (W : Set V) {g : ℕ → V} (hg : InducedSeq G 12 g) {i : ℕ}
    (hi : i ≤ 12) (hdeg : 3 ≤ G.degree (g i)) (hW : ∀ w, G.Adj (g i) w → w ∈ W) :
    ∃ w, G.Adj (g i) w ∧ w ∈ W ∧ ∀ t ≤ 12, w ≠ g t := by
  by_contra hno
  push Not at hno
  have := interior_not_in_window G hg hi (fun w hw => by
    obtain ⟨t, ht, e⟩ := hno w hw (hW w hw); exact ⟨t, ht, e⟩)
  omega

/-! ## 15. a long window-free path closed by an outside path -/

def catFn (g q : ℕ → V) (L t : ℕ) : V := if t ≤ L then g t else q (t - L)

/-- **Concatenation cycle.**  An injective path `g : a → b` (length `L`) and a path
`q : b → a` (length `T`) whose interior avoids `g` close a cycle of length `L + T`. -/
theorem concat_cycle {S : Set V} {L T : ℕ} {g q : ℕ → V} (hw : SWalk G S L g)
    (hinj : ∀ a ≤ L, ∀ b ≤ L, g a = g b → a = b)
    (hq : ∀ t < T, G.Adj (q t) (q (t + 1)))
    (hqinj : ∀ a b, 0 < a → a < T → 0 < b → b < T → q a = q b → a = b)
    (hqd : ∀ t, 0 < t → t < T → ∀ s ≤ L, q t ≠ g s)
    (h0 : q 0 = g L) (hT : q T = g 0) (hT1 : 1 ≤ T) :
    CycleSeq G (L + T) (catFn g q L) := by
  refine ⟨fun a ha b hb hab => ?_, fun t ht => ?_, ?_⟩
  · unfold catFn at hab
    by_cases h1 : a ≤ L <;> by_cases h2 : b ≤ L
    · rw [if_pos h1, if_pos h2] at hab; exact hinj a h1 b h2 hab
    · rw [if_pos h1, if_neg h2] at hab
      exact absurd hab.symm (hqd (b - L) (by omega) (by omega) a h1)
    · rw [if_neg h1, if_pos h2] at hab
      exact absurd hab (hqd (a - L) (by omega) (by omega) b h2)
    · rw [if_neg h1, if_neg h2] at hab
      have := hqinj (a - L) (b - L) (by omega) (by omega) (by omega) (by omega) hab; omega
  · unfold catFn
    by_cases h1 : t + 1 ≤ L
    · rw [if_pos (by omega), if_pos h1]; exact hw.1 t (by omega)
    · by_cases h2 : t ≤ L
      · have e : t = L := by omega
        rw [if_pos h2, if_neg h1, e, ← h0, show L + 1 - L = 0 + 1 by omega]
        exact hq 0 (by omega)
      · rw [if_neg h2, if_neg h1, show t + 1 - L = t - L + 1 by omega]
        exact hq _ (by omega)
  · unfold catFn
    rw [if_pos (Nat.zero_le _), ← hT]
    by_cases h1 : L + T - 1 ≤ L
    · rw [if_pos h1]
      have e1 : L + T - 1 = L := by omega
      have e2 : T = 0 + 1 := by omega
      rw [e1, ← h0, e2]; exact hq 0 (by omega)
    · rw [if_neg h1]
      have e : T = L + T - 1 - L + 1 := by omega
      conv => rhs; rw [e]
      exact hq _ (by omega)

theorem spliceFn_range {g : ℕ → V} {i c L : ℕ} (hc : i + c ≤ L) :
    ∀ s ≤ L - c, ∃ s' ≤ L, spliceFn g i c s = g s' := by
  intro s hs
  unfold spliceFn
  by_cases h : s ≤ i
  · exact ⟨s, by omega, by rw [if_pos h]⟩
  · exact ⟨s + c, by omega, by rw [if_neg h]⟩

/-- **Closed long path.**  A window-free injective path `g` of length `L ≥ 12` closed by an
outside path `q` of length `T` (interior avoiding `g`) carries a chord `(i, j)` in its first
13 vertices whose span `s = j − i` satisfies, for all `m ≥ 2`:
`s + 1 ≠ 2^m` and `L − s + 1 + T ≠ 2^m`.  (`π` closed by `τ`; `τ` closed by `π`;
the forced path of `deletedSupportEdgeRestoration` closed through `S`.) -/
theorem closed_path_chord {S : Set V} (hno : NoInducedP13In G S) (hcyc : NoPow2Cycles G)
    {L T : ℕ} {g q : ℕ → V} (hw : SWalk G S L g)
    (hinj : ∀ a ≤ L, ∀ b ≤ L, g a = g b → a = b)
    (hq : ∀ t < T, G.Adj (q t) (q (t + 1)))
    (hqinj : ∀ a b, 0 < a → a < T → 0 < b → b < T → q a = q b → a = b)
    (hqd : ∀ t, 0 < t → t < T → ∀ s ≤ L, q t ≠ g s)
    (h0 : q 0 = g L) (hT : q T = g 0) (hT1 : 1 ≤ T) (hL : 12 ≤ L) :
    ∃ i j, i + 2 ≤ j ∧ j ≤ 12 ∧ G.Adj (g i) (g j) ∧
      ∀ m, 2 ≤ m → j - i + 1 ≠ 2 ^ m ∧ L - (j - i) + 1 + T ≠ 2 ^ m := by
  obtain ⟨i, j, _, hij, hj, hadj⟩ := block_has_chord G hno hw hinj (a := 0) (by omega)
  refine ⟨i, j, hij, by omega, hadj, fun m hm => ⟨fun he => ?_, fun he => ?_⟩⟩
  · have hc := chord_cycle G hw hinj hij (by omega) hadj
    rw [he] at hc; exact hcyc m hm _ hc
  · obtain ⟨hw', h0', hk'⟩ := splice_chord G hw hij (by omega) hadj
    have hinj' := splice_chord_inj hinj hij (by omega)
    have hqd' : ∀ t, 0 < t → t < T → ∀ s ≤ L - (j - i - 1),
        q t ≠ spliceFn g i (j - i - 1) s := by
      intro t ht1 ht2 s hs
      obtain ⟨s', hs', e⟩ := spliceFn_range (g := g) (i := i) (c := j - i - 1) (L := L)
        (by omega) s hs
      rw [e]; exact hqd t ht1 ht2 s' hs'
    have hc := concat_cycle G hw' hinj' hq hqinj hqd' (h0.trans hk'.symm) (hT.trans h0'.symm) hT1
    have e : L - (j - i - 1) + T = 2 ^ m := by omega
    rw [e] at hc; exact hcyc m hm _ hc

/-- **Outside-return dichotomy.**  For two boundary labels `a, b` and the
window-free outside set `S` (e.g. `(V ∖ Z) ∪ {a,b}` minus `W`): either `a, b` are joined
inside `S` by an induced path of length `≤ 11` (a short outside return), or every
`b → a` walk leaves `S`, i.e. meets `W` or `Z ∖ {a,b}`. -/
theorem outside_return_dichotomy {S : Set V} (hno : NoInducedP13In G S) (a b : V) :
    (∃ k ≤ 11, ∃ g, SWalk G S k g ∧ g 0 = b ∧ g k = a ∧ InducedSeq G k g) ∨
      (∀ k (g : ℕ → V), (∀ t < k, G.Adj (g t) (g (t + 1))) → g 0 = b → g k = a →
        ∃ t ≤ k, g t ∉ S) := by
  by_cases hc : ∃ k, Reach G S b a k
  · obtain ⟨k, g, hk, hw, h0, hka, hind, _⟩ := short_walk G hno hc
    exact Or.inl ⟨k, hk, g, hw, h0, hka, hind⟩
  · right
    intro k g hadj h0 hk
    by_contra hall
    push Not at hall
    exact hc ⟨k, g, ⟨hadj, hall⟩, h0, hk⟩

/-! ## 16. the other forbidden gaps -/

/-- **Local algebra, gap 6** (an 8-cycle through the window). -/
theorem attach_no_gap_six (hcyc : NoPow2Cycles G) {g : ℕ → V} (hg : InducedSeq G 12 g)
    {v : V} (hv : ∀ t ≤ 12, g t ≠ v) {a : ℕ} (ha : a + 6 ≤ 12)
    (h1 : G.Adj v (g a)) (h2 : G.Adj v (g (a + 6))) : False := by
  have hw : SWalk G {w | w ≠ v} 6 (shiftFn g a) := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · unfold shiftFn
      rw [← Nat.add_assoc]
      exact (hg.2 (a + t) (by omega) (a + t + 1) (by omega)).2 (Or.inl rfl)
    · exact hv (a + t) (by omega)
  have hinj : ∀ p ≤ 6, ∀ q ≤ 6, shiftFn g a p = shiftFn g a q → p = q := by
    intro p hp q hq e
    unfold shiftFn at e
    have := hg.1 (a + p) (by omega) (a + q) (by omega) e; omega
  have hc := cycle_through_hub G (S := {w | w ≠ v}) (fun h => h rfl) hw hinj
    (by unfold shiftFn; simpa using h1) (by unfold shiftFn; exact h2)
  rw [show (6 : ℕ) + 2 = 2 ^ 3 by norm_num] at hc
  exact hcyc 3 (by norm_num) _ hc

/-- **Local algebra, outside edge (`C₁` safety)**: adjacent outside vertices `u ~ w`
attaching at coordinates `i, j` have `|i − j| ∉ {1, 5}` (cycles of length 4 and 8).
Stated for `j = i + d`. -/
theorem attach_edge_gap (hcyc : NoPow2Cycles G) {g : ℕ → V} (hg : InducedSeq G 12 g)
    {u w : V} (hu : ∀ t ≤ 12, g t ≠ u) (hw' : ∀ t ≤ 12, g t ≠ w) (huw : G.Adj u w)
    {i d : ℕ} (hd : d = 1 ∨ d = 5) (hid : i + d ≤ 12)
    (h1 : G.Adj w (g i)) (h2 : G.Adj u (g (i + d))) : False := by
  -- the path g i .. g (i+d), closed by g(i+d) - u - w - g i (length 3)
  let q : ℕ → V := fun t => if t = 0 then g (i + d) else if t = 1 then u else if t = 2 then w
    else g i
  have hs : SWalk G {x | x ≠ u ∧ x ≠ w} d (shiftFn g i) := by
    refine ⟨fun t ht => ?_, fun t ht => ⟨hu _ (by omega), hw' _ (by omega)⟩⟩
    unfold shiftFn; rw [← Nat.add_assoc]
    exact (hg.2 (i + t) (by omega) (i + t + 1) (by omega)).2 (Or.inl rfl)
  have hinj : ∀ p ≤ d, ∀ r ≤ d, shiftFn g i p = shiftFn g i r → p = r := by
    intro p hp r hr e; unfold shiftFn at e
    have := hg.1 (i + p) (by omega) (i + r) (by omega) e; omega
  have hq : ∀ t < 3, G.Adj (q t) (q (t + 1)) := by
    intro t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl
    · change G.Adj (g (i + d)) u; exact h2.symm
    · change G.Adj u w; exact huw
    · change G.Adj w (g i); exact h1
  have hqinj : ∀ a b, 0 < a → a < 3 → 0 < b → b < 3 → q a = q b → a = b := by
    intro a b ha1 ha2 hb1 hb2 e
    have hA : a = 1 ∨ a = 2 := by omega
    have hB : b = 1 ∨ b = 2 := by omega
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · rfl
    · change u = w at e; exact absurd e (G.ne_of_adj huw)
    · change w = u at e; exact absurd e.symm (G.ne_of_adj huw)
    · rfl
  have hqd : ∀ t, 0 < t → t < 3 → ∀ s ≤ d, q t ≠ shiftFn g i s := by
    intro t ht1 ht2 s hs e
    have hT : t = 1 ∨ t = 2 := by omega
    rcases hT with rfl | rfl
    · change u = g (i + s) at e; exact hu _ (by omega) e.symm
    · change w = g (i + s) at e; exact hw' _ (by omega) e.symm
  have hc := concat_cycle G (T := 3) (q := q) hs hinj hq hqinj hqd
    (by change g (i + d) = g (i + d); rfl) (by change g i = g (i + 0); rfl) (by norm_num)
  rcases hd with rfl | rfl
  · rw [show (1 : ℕ) + 3 = 2 ^ 2 by norm_num] at hc; exact hcyc 2 le_rfl _ hc
  · rw [show (5 : ℕ) + 3 = 2 ^ 3 by norm_num] at hc; exact hcyc 3 (by norm_num) _ hc

/-! ## 17. Remainder components with few hubs -/

/-- **Hub degree needed by a remainder component.** -/
theorem component_hub_degree (K Hk : Finset V) (hno : NoInducedP13In G (↑K : Set V)) (r : V)
    (hr : r ∈ K) (hconn : ∀ v ∈ K, ∃ k, Reach G (↑K : Set V) r v k)
    (hdeg : ∀ v ∈ K, 3 ≤ G.degree v) (hHK : Hk ⊆ K)
    (hcub : ∀ v ∈ K, v ∉ Hk → G.degree v = 3) (Δ : ℕ) (hΔ : ∀ v ∈ Hk, G.degree v ≤ Δ) :
    K.card ≤ 1 + (3 + Hk.card * (Δ - 3)) * 2047 := by
  have h := component_card_le G K hno r hr hconn hdeg
  have hs : ∑ v ∈ K, (G.degree v - 3) ≤ Hk.card * (Δ - 3) := by
    have e : ∑ v ∈ K, (G.degree v - 3) = ∑ v ∈ Hk, (G.degree v - 3) := by
      rw [← sum_sdiff hHK]
      have : ∑ v ∈ K \ Hk, (G.degree v - 3) = 0 := by
        apply sum_eq_zero; intro v hv
        rw [mem_sdiff] at hv; rw [hcub v hv.1 hv.2]; rfl
      rw [this, zero_add]
    rw [e]
    calc ∑ v ∈ Hk, (G.degree v - 3) ≤ ∑ v ∈ Hk, (Δ - 3) :=
          sum_le_sum (fun v hv => by have := hΔ v hv; omega)
      _ = Hk.card * (Δ - 3) := by rw [sum_const, smul_eq_mul]
  have e2 : (2 : ℕ) ^ 11 - 1 = 2047 := by norm_num
  rw [e2] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_left hs 3)) 1)

/-- **Single hub**: a remainder component whose only non-cubic vertex is one hub of degree
`d` has `|K| ≤ 1 + 2047 d`, i.e. `d ≥ (|K| − 1)/2047` (`≈ |K|/(2·2^10)`). -/
theorem component_single_hub (K : Finset V) (hno : NoInducedP13In G (↑K : Set V)) (r : V)
    (hr : r ∈ K) (hconn : ∀ v ∈ K, ∃ k, Reach G (↑K : Set V) r v k)
    (hdeg : ∀ v ∈ K, 3 ≤ G.degree v) (b : V) (hb : b ∈ K)
    (hcub : ∀ v ∈ K, v ≠ b → G.degree v = 3) :
    K.card ≤ 1 + 2047 * G.degree b := by
  have h := component_hub_degree G K {b} hno r hr hconn hdeg (by simpa using hb)
    (fun v hv hvb => hcub v hv (by simpa using hvb)) (G.degree b) (by simp)
  have := hdeg b hb
  rw [card_singleton, one_mul] at h
  omega

end Hypostructure.Graph.WindowCombination
