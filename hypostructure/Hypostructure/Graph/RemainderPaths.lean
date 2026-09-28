import Hypostructure.Graph.WindowCombination

/-!
# Long paths versus induced paths

Vocabulary-free.

Sequences `ℕ → V` as in `WindowCombination`.  `PathSeq S m g`: `g 0, …, g m` is a path with
`m` edges inside `S`.

* **Furthest-jump extraction** (`greedy_induced`): from `g 0`, jump each time to the
  furthest later path vertex adjacent to the current one.  The jump sequence is an
  *induced* path from `g 0` to `g m`.
* **Span form** (`span_induced`): if every adjacency `g a ∼ g b` (`a < b`) has span
  `b − a ≤ s`, there is an induced path on `J + 1` vertices inside `S` with `m ≤ J s`.
  Hence with no induced path on `N + 1` vertices in `S`: `m ≤ (N − 1) s`.
* **Long chord / long cycle** (`long_chord`, `long_cycle`): with no induced `P13` in `S`,
  a path with `m ≥ 1` edges carries an adjacency of span `≥ m/11`; if `m ≥ 12` that
  adjacency is a chord closing a cycle of length `≥ m/11 + 1` inside `S`.  So the longest
  path and the circumference control each other: `m ≤ 11 (L − 1)` when every cycle in `S`
  has length `≤ L`.
* **Bag bound** (`bag_path_bound`): if every `H`-free `S`-connected set ("bag") has at most
  `M` vertices, a path in `S` through `k` vertices of `H` has at most `(M+1)k + M` vertices.


## C4-free graphs without long induced paths are degenerate

**Greedy induced path.**  In a C4-free graph, an induced path `x₀ … xᵢ` inside `X` can be
extended at `xᵢ` by any `X`-neighbour outside `{x_{i−1}} ∪ ⋃_{j<i} (N(xᵢ) ∩ N(xⱼ))`, a set
of at most `i + 1` vertices (codegree `≤ 1`).  Hence if every vertex of `X` has at least
`N + 1` neighbours in `X`, then `X` carries an induced path on `N + 1` vertices.

Contrapositive (`low_vertex`): with no induced path on `N + 1` vertices inside `S`, every
nonempty `X ⊆ S` has a vertex with at most `N` neighbours in `X` (`S` is `N`-degenerate).
For `N = 12` (no induced `P13`): `12`-degenerate.
-/

open Finset Hypostructure.Graph.WindowCombination

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.RemainderPaths

section Generic


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `g 0, …, g m` is a path with `m` edges inside `S`. -/
abbrev PathSeq (S : Set V) (m : ℕ) (g : ℕ → V) : Prop :=
  (∀ a ≤ m, ∀ b ≤ m, g a = g b → a = b) ∧ SWalk G S m g

/-- The furthest path position (`≤ m`) adjacent to position `a`. -/
noncomputable def jump (g : ℕ → V) (m a : ℕ) : ℕ :=
  Nat.findGreatest (fun b => G.Adj (g a) (g b)) m

/-- The jump iteration from position `0` (frozen at `m`). -/
noncomputable def idx (g : ℕ → V) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if idx g m k < m then jump G g m (idx g m k) else m

variable {G}

theorem jump_spec {S : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) {a : ℕ} (ha : a < m) :
    a + 1 ≤ jump G g m a ∧ jump G g m a ≤ m ∧ G.Adj (g a) (g (jump G g m a)) ∧
      ∀ b, jump G g m a < b → b ≤ m → ¬ G.Adj (g a) (g b) := by
  have hadj : G.Adj (g a) (g (a + 1)) := hp.2.1 a ha
  refine ⟨Nat.le_findGreatest (by omega) hadj, Nat.findGreatest_le m,
    Nat.findGreatest_spec (P := fun b => G.Adj (g a) (g b)) (by omega : a + 1 ≤ m) hadj,
    fun b hb hbm => Nat.findGreatest_is_greatest hb hbm⟩

theorem idx_le {S : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) : ∀ k, idx G g m k ≤ m
  | 0 => Nat.zero_le _
  | k + 1 => by
    show (if idx G g m k < m then jump G g m (idx G g m k) else m) ≤ m
    split_ifs with h
    · exact (jump_spec hp h).2.1
    · exact le_rfl

theorem idx_succ_of_lt {m : ℕ} {g : ℕ → V} {k : ℕ} (h : idx G g m k < m) :
    idx G g m (k + 1) = jump G g m (idx G g m k) := by
  show (if idx G g m k < m then jump G g m (idx G g m k) else m) = _
  rw [if_pos h]

theorem idx_ge {S : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) :
    ∀ k, min k m ≤ idx G g m k
  | 0 => by simp
  | k + 1 => by
    have ih := idx_ge hp k
    by_cases h : idx G g m k < m
    · rw [idx_succ_of_lt h]
      have := (jump_spec hp h).1
      omega
    · show min (k + 1) m ≤ (if idx G g m k < m then jump G g m (idx G g m k) else m)
      rw [if_neg h]; omega

/-- **Furthest-jump extraction.**  The jump sequence `g (idx 0), …, g (idx J)` runs from
`g 0` to `g m`, each step is an edge of `G`, and it is an induced path. -/
theorem greedy_induced {S : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) :
    ∃ J, idx G g m J = m ∧ (∀ k < J, idx G g m k < idx G g m (k + 1)) ∧
      InducedSeq G J (fun k => g (idx G g m k)) ∧ ∀ k ≤ J, g (idx G g m k) ∈ S := by
  classical
  have hex : ∃ k, idx G g m k = m := ⟨m, le_antisymm (idx_le hp m) (by simpa using idx_ge hp m)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_, ?_⟩
  · intro k hk
    have hlt : idx G g m k < m := lt_of_le_of_ne (idx_le hp k) (Nat.find_min hex hk)
    rw [idx_succ_of_lt hlt]; have := (jump_spec hp hlt).1; omega
  · set J := Nat.find hex
    have hlt : ∀ k < J, idx G g m k < m := fun k hk =>
      lt_of_le_of_ne (idx_le hp k) (Nat.find_min hex hk)
    have hmono : ∀ a b, a < b → b ≤ J → idx G g m a < idx G g m b := by
      intro a b hab hbJ
      induction b with
      | zero => omega
      | succ b ih =>
        have hb : idx G g m b < m := hlt b (by omega)
        rw [idx_succ_of_lt hb]
        have := (jump_spec hp hb).1
        rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
        · have := ih h (by omega); omega
        · subst h; omega
    refine ⟨fun a ha b hb hab => ?_, fun a ha b hb => ⟨fun hadj => ?_, fun hc => ?_⟩⟩
    · by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hmono a b h hb
        have := hp.1 _ (idx_le hp a) _ (idx_le hp b) hab; omega
      · have := hmono b a h ha
        have := hp.1 _ (idx_le hp a) _ (idx_le hp b) hab; omega
    · by_contra hc
      push Not at hc
      have hne : a ≠ b := fun e => by subst e; exact G.irrefl hadj
      rcases lt_or_gt_of_ne hne with h | h
      · have ha' := hlt a (by omega)
        have hj := jump_spec hp ha'
        have hgt : jump G g m (idx G g m a) < idx G g m b := by
          rw [← idx_succ_of_lt ha']; exact hmono (a + 1) b (by omega) hb
        exact hj.2.2.2 _ hgt (idx_le hp b) hadj
      · have hb' := hlt b (by omega)
        have hj := jump_spec hp hb'
        have hgt : jump G g m (idx G g m b) < idx G g m a := by
          rw [← idx_succ_of_lt hb']; exact hmono (b + 1) a (by omega) ha
        exact hj.2.2.2 _ hgt (idx_le hp a) hadj.symm
    · rcases hc with h | h
      · subst h
        have ha' := hlt a (by omega)
        show G.Adj (g (idx G g m a)) (g (idx G g m (a + 1)))
        rw [idx_succ_of_lt ha']; exact (jump_spec hp ha').2.2.1
      · subst h
        have hb' := hlt b (by omega)
        show G.Adj (g (idx G g m (b + 1))) (g (idx G g m b))
        rw [idx_succ_of_lt hb']; exact (jump_spec hp hb').2.2.1.symm
  · intro k hk; exact hp.2.2 _ (idx_le hp k)

/-- **Span form.**  If every adjacency along the path has span `≤ s`, then `S` contains an
induced path on `J + 1` vertices with `m ≤ J s`. -/
theorem span_induced {S : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) (s : ℕ)
    (hs : ∀ a b, a < b → b ≤ m → G.Adj (g a) (g b) → b - a ≤ s) :
    ∃ J h, InducedSeq G J h ∧ (∀ k ≤ J, h k ∈ S) ∧ m ≤ J * s := by
  classical
  obtain ⟨J, hJ, hinc, hind, hS⟩ := greedy_induced hp
  refine ⟨J, _, hind, hS, ?_⟩
  have hlt : ∀ k < J, idx G g m k < m := fun k hk =>
    lt_of_lt_of_le (hinc k hk) (idx_le hp (k + 1))
  have hstep : ∀ k ≤ J, idx G g m k ≤ k * s := by
    intro k hk
    induction k with
    | zero => simp [idx]
    | succ k ih =>
      have hk' := hlt k (by omega)
      have hj := jump_spec hp hk'
      have := hs _ _ (by omega) hj.2.1 hj.2.2.1
      rw [idx_succ_of_lt hk']
      have := ih (by omega)
      rw [Nat.succ_mul]; omega
  have := hstep J le_rfl
  omega

/-- No induced path on `N + 1` vertices inside `S`. -/
abbrev NoInducedPathIn (G : SimpleGraph V) (N : ℕ) (S : Set V) : Prop :=
  ∀ h : ℕ → V, InducedSeq G N h → ∃ t ≤ N, h t ∉ S

/-- **Explicit `f` for bounded spans.**  With no induced path on `N + 1` vertices in `S`
(`N ≥ 1`) and all spans `≤ s`: every path in `S` has at most `(N − 1)s` edges. -/
theorem span_path_bound {S : Set V} {N m : ℕ} {g : ℕ → V} (hno : NoInducedPathIn G N S)
    (hp : PathSeq G S m g) (s : ℕ)
    (hs : ∀ a b, a < b → b ≤ m → G.Adj (g a) (g b) → b - a ≤ s) :
    m ≤ (N - 1) * s := by
  obtain ⟨J, h, hind, hS, hm⟩ := span_induced hp s hs
  have hJ : J < N := by
    by_contra hJ
    obtain ⟨t, ht, hts⟩ := hno h (induced_prefix G hind (by omega))
    exact hts (hS t (by omega))
  exact hm.trans (Nat.mul_le_mul_right _ (by omega))

theorem noInducedPath_of_P13 {S : Set V} (hno : NoInducedP13In G S) : NoInducedPathIn G 12 S :=
  hno

/-- **Long adjacency.**  With no induced `P13` in `S`, a path with `m ≥ 1` edges in `S`
has an adjacency `g a ∼ g b`, `a < b`, of span `11(b − a) ≥ m`. -/
theorem long_chord {S : Set V} (hno : NoInducedP13In G S) {m : ℕ} {g : ℕ → V}
    (hp : PathSeq G S m g) (hm : 1 ≤ m) :
    ∃ a b, a < b ∧ b ≤ m ∧ G.Adj (g a) (g b) ∧ m ≤ 11 * (b - a) := by
  by_contra hcon
  push Not at hcon
  have hs : ∀ a b, a < b → b ≤ m → G.Adj (g a) (g b) → b - a ≤ (m - 1) / 11 := by
    intro a b hab hb hadj
    have := hcon a b hab hb hadj
    omega
  have := span_path_bound hno hp ((m - 1) / 11) hs
  omega

/-- **Long cycle.**  With no induced `P13` in `S`, a path with `m ≥ 12` edges in `S`
carries a cycle inside `S` of length `L` with `m + 11 ≤ 11 L` (i.e. `L ≥ m/11 + 1`),
made of a chord and the path segment it spans. -/
theorem long_cycle {S : Set V} (hno : NoInducedP13In G S) {m : ℕ} {g : ℕ → V}
    (hp : PathSeq G S m g) (hm : 12 ≤ m) :
    ∃ L c, 3 ≤ L ∧ m + 11 ≤ 11 * L ∧ CycleSeq G L c ∧ ∀ t < L, c t ∈ S := by
  obtain ⟨a, b, hab, hb, hadj, hspan⟩ := long_chord hno hp (by omega)
  have h2 : a + 2 ≤ b := by omega
  refine ⟨b - a + 1, shiftFn g a, by omega, by omega, chord_cycle G hp.2 hp.1 h2 hb hadj,
    fun t ht => ?_⟩
  unfold shiftFn; exact hp.2.2 (a + t) (by omega)

/-- **Longest path versus circumference.**  If every cycle inside `S` has length `≤ L`
(and there is no induced `P13` in `S`), every path in `S` has at most
`max 11 (11(L − 1))` edges. -/
theorem path_le_of_circumference {S : Set V} (hno : NoInducedP13In G S) (L : ℕ)
    (hcirc : ∀ n c, CycleSeq G n c → (∀ t < n, c t ∈ S) → 3 ≤ n → n ≤ L)
    {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) : m ≤ 11 ∨ m ≤ 11 * (L - 1) := by
  by_cases hm : 12 ≤ m
  · obtain ⟨n, c, h3, hmn, hc, hcS⟩ := long_cycle hno hp hm
    have := hcirc n c hc hcS h3
    right; omega
  · left; omega

/-! ## The bag bound -/

/-- Every vertex of an `H`-free run of the path is reached from the run's first vertex
inside `S ∖ H`. -/
theorem run_reach {S : Set V} {H : Set V} {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g)
    {a b : ℕ} (hb : b ≤ m) (hrun : ∀ t, a ≤ t → t ≤ b → g t ∉ H) :
    ∀ t, a ≤ t → t ≤ b → Reach G (S \ H) (g a) (g t) (t - a) := by
  intro t hat htb
  refine ⟨shiftFn g a, ⟨fun i hi => ?_, fun i hi => ?_⟩, by simp [shiftFn], ?_⟩
  · unfold shiftFn; rw [← Nat.add_assoc]; exact hp.2.1 (a + i) (by omega)
  · unfold shiftFn
    exact ⟨hp.2.2 (a + i) (by omega), hrun (a + i) (by omega) (by omega)⟩
  · unfold shiftFn; congr 1; omega

/-- An `H`-free run has at most `M` vertices. -/
theorem run_card {S : Set V} {H : Set V} (M : ℕ)
    (hbag : ∀ v ∈ S, v ∉ H → ∀ T : Finset V, (∀ w ∈ T, ∃ k, Reach G (S \ H) v w k) →
      T.card ≤ M)
    {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m)
    (hrun : ∀ t, a ≤ t → t ≤ b → g t ∉ H) : b - a + 1 ≤ M := by
  have hR := run_reach hp hb hrun
  have hT := hbag (g a) (hp.2.2 a (by omega)) (hrun a le_rfl hab) ((Icc a b).image g)
    (by
      intro w hw
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hw
      rw [mem_Icc] at ht
      exact ⟨_, hR t ht.1 ht.2⟩)
  rw [card_image_of_injOn (fun x hx y hy e => hp.1 x (by simp at hx; omega) y
    (by simp at hy; omega) e), Nat.card_Icc] at hT
  omega

/-- **Bag bound.**  If every `H`-free `S`-connected set has at most `M` vertices, a path
in `S` with `m` edges through `k` vertices of `H` satisfies `m + 1 ≤ (M + 1) k + M`. -/
theorem bag_path_bound {S : Set V} {H : Set V} [DecidablePred (· ∈ H)] (M : ℕ)
    (hbag : ∀ v ∈ S, v ∉ H → ∀ T : Finset V, (∀ w ∈ T, ∃ k, Reach G (S \ H) v w k) →
      T.card ≤ M)
    {m : ℕ} {g : ℕ → V} (hp : PathSeq G S m g) :
    m + 1 ≤ (M + 1) * ((range (m + 1)).filter (fun t => g t ∈ H)).card + M := by
  classical
  have key : ∀ m', m' ≤ m →
      m' + 1 ≤ (M + 1) * ((range (m' + 1)).filter (fun t => g t ∈ H)).card + M := by
    intro m'
    induction m' using Nat.strong_induction_on with
    | _ m' ih =>
      intro hm'
      by_cases hex : ∃ p ≤ m', g p ∈ H
      · set p := Nat.findGreatest (fun p => g p ∈ H) m' with hpdef
        obtain ⟨p0, hp0, hp0H⟩ := hex
        have hpH : g p ∈ H := Nat.findGreatest_spec (P := fun p => g p ∈ H) hp0 hp0H
        have hpm : p ≤ m' := Nat.findGreatest_le m'
        have hafter : ∀ t, p + 1 ≤ t → t ≤ m' → g t ∉ H :=
          fun t ht htm => Nat.findGreatest_is_greatest (P := fun p => g p ∈ H) (by omega) htm
        have hrun : m' - p ≤ M := by
          by_cases hpm' : p = m'
          · omega
          · have := run_card M hbag hp (a := p + 1) (b := m') (by omega) hm' hafter
            omega
        have hsplit : ((range (m' + 1)).filter (fun t => g t ∈ H)).card
            = ((range p).filter (fun t => g t ∈ H)).card + 1 := by
          have e : (range (m' + 1)).filter (fun t => g t ∈ H)
              = insert p ((range p).filter (fun t => g t ∈ H)) := by
            ext t
            simp only [mem_filter, mem_range, mem_insert]
            constructor
            · rintro ⟨ht, htH⟩
              by_cases htp : t = p
              · left; exact htp
              · right
                refine ⟨?_, htH⟩
                by_contra hge
                exact hafter t (by omega) (by omega) htH
            · rintro (rfl | ⟨ht, htH⟩)
              · exact ⟨by omega, hpH⟩
              · exact ⟨by omega, htH⟩
          rw [e, card_insert_of_notMem (by simp)]
        rw [hsplit]
        rw [Nat.mul_add, Nat.mul_one]
        rcases Nat.eq_zero_or_pos p with hp0' | hp0'
        · omega
        · have := ih (p - 1) (by omega) (by omega)
          rw [show p - 1 + 1 = p by omega] at this
          omega
      · push Not at hex
        have := run_card M hbag hp (a := 0) (b := m') (Nat.zero_le _) hm'
          (fun t _ ht => hex t ht)
        omega
  exact key m le_rfl


end Generic

section Degenerate


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem induced_zero (x : V) : InducedSeq G 0 (fun _ => x) :=
  ⟨fun a ha b hb _ => by omega, fun a ha b hb => by
    simp only [show a = 0 by omega, show b = 0 by omega]
    exact ⟨fun h => absurd h (G.irrefl), fun h => by omega⟩⟩

/-- **One greedy step.** -/
theorem induced_extend (hC4 : C4Free G) (X : Finset V) {i : ℕ} {g : ℕ → V}
    (hg : InducedSeq G i g) (hX : ∀ t ≤ i, g t ∈ X)
    (hdeg : i + 2 ≤ (G.neighborFinset (g i) ∩ X).card) :
    ∃ g' : ℕ → V, InducedSeq G (i + 1) g' ∧ ∀ t ≤ i + 1, g' t ∈ X := by
  classical
  set B : Finset V := insert (g (i - 1))
    ((range i).biUnion (fun j => G.neighborFinset (g i) ∩ G.neighborFinset (g j))) with hB
  have hBc : B.card ≤ i + 1 := by
    refine (card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
    refine card_biUnion_le.trans ?_
    calc ∑ j ∈ range i, (G.neighborFinset (g i) ∩ G.neighborFinset (g j)).card
        ≤ ∑ j ∈ range i, 1 := by
          apply sum_le_sum
          intro j hj
          have hji : j < i := mem_range.1 hj
          have hne : g i ≠ g j := fun e => by have := hg.1 i le_rfl j (by omega) e; omega
          apply card_le_one.2
          intro c hc c' hc'
          simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hc hc'
          exact hC4 (g i) (g j) c c' hne hc.1 hc.2 hc'.1 hc'.2
      _ = i := by simp
  obtain ⟨y, hy, hyB⟩ : ∃ y ∈ G.neighborFinset (g i) ∩ X, y ∉ B := by
    by_contra hno
    push Not at hno
    have := card_le_card (show G.neighborFinset (g i) ∩ X ⊆ B from fun y hy => hno y hy)
    omega
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hy
  obtain ⟨hyadj, hyX⟩ := hy
  have hyB' : ∀ j < i, ¬ G.Adj (g j) y := by
    intro j hj hadj
    apply hyB
    rw [hB]
    apply mem_insert_of_mem
    rw [mem_biUnion]
    exact ⟨j, mem_range.2 hj, by simp [hyadj, hadj]⟩
  have hyne : ∀ t ≤ i, g t ≠ y := by
    intro t ht e
    rcases Nat.lt_or_ge t i with h | h
    · by_cases h1 : t + 1 = i
      · apply hyB; rw [hB, ← e, show i - 1 = t by omega]; exact mem_insert_self _ _
      · have hna : ¬ G.Adj (g t) (g i) := fun hadj => by
          have := (hg.2 t (by omega) i le_rfl).1 hadj; omega
        exact hna (e ▸ hyadj.symm)
    · have : t = i := by omega
      subst this
      exact G.irrefl (e ▸ hyadj)
  refine ⟨fun t => if t ≤ i then g t else y, ⟨?_, ?_⟩, ?_⟩
  · intro a ha b hb hab
    by_cases h1 : a ≤ i <;> by_cases h2 : b ≤ i <;> simp only [h1, h2, if_true, if_false] at hab
    · exact hg.1 a h1 b h2 hab
    · exact absurd hab (hyne a h1)
    · exact absurd hab.symm (hyne b h2)
    · omega
  · intro a ha b hb
    by_cases h1 : a ≤ i <;> by_cases h2 : b ≤ i <;> simp only [h1, h2, if_true, if_false]
    · exact hg.2 a h1 b h2
    · have hb' : b = i + 1 := by omega
      subst hb'
      constructor
      · intro hadj
        by_contra hc
        exact hyB' a (by omega) hadj
      · intro hc
        have : a = i := by omega
        subst this; exact hyadj
    · have ha' : a = i + 1 := by omega
      subst ha'
      constructor
      · intro hadj
        by_contra hc
        exact hyB' b (by omega) hadj.symm
      · intro hc
        have : b = i := by omega
        subst this; exact hyadj.symm
    · have : a = b := by omega
      subst this
      exact ⟨fun h => absurd h (G.irrefl), fun h => by omega⟩
  · intro t ht
    by_cases h1 : t ≤ i
    · simp only [h1, if_true]; exact hX t h1
    · simp only [h1, if_false]; exact hyX

/-- **High minimum degree forces an induced path.**  In a C4-free graph, if every vertex of
a nonempty `X` has at least `N + 1` neighbours in `X`, then `X` carries an induced path on
`N + 1` vertices. -/
theorem induced_of_mindeg (hC4 : C4Free G) (X : Finset V) (hne : X.Nonempty) (N : ℕ)
    (hdeg : ∀ v ∈ X, N + 1 ≤ (G.neighborFinset v ∩ X).card) :
    ∃ g : ℕ → V, InducedSeq G N g ∧ ∀ t ≤ N, g t ∈ X := by
  obtain ⟨x, hx⟩ := hne
  have key : ∀ i ≤ N, ∃ g : ℕ → V, InducedSeq G i g ∧ ∀ t ≤ i, g t ∈ X := by
    intro i hi
    induction i with
    | zero => exact ⟨fun _ => x, induced_zero x, fun _ _ => hx⟩
    | succ i ih =>
      obtain ⟨g, hg, hgX⟩ := ih (by omega)
      exact induced_extend hC4 X hg hgX ((hdeg (g i) (hgX i le_rfl)).trans' (by omega))
  exact key N le_rfl

/-- **Degeneracy (explicit).**  C4-free, and no induced path on `N + 1` vertices inside
`S`: every nonempty `X ⊆ S` has a vertex with at most `N` neighbours in `X`. -/
theorem low_vertex (hC4 : C4Free G) {S : Set V} {N : ℕ} (hno : NoInducedPathIn G N S)
    (X : Finset V) (hXS : ∀ v ∈ X, v ∈ S) (hne : X.Nonempty) :
    ∃ v ∈ X, (G.neighborFinset v ∩ X).card ≤ N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg, hgX⟩ := induced_of_mindeg hC4 X hne N (fun v hv => hcon v hv)
  obtain ⟨t, ht, hts⟩ := hno g hg
  exact hts (hXS _ (hgX t ht))


end Degenerate

end Hypostructure.Graph.RemainderPaths
