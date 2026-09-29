import Hypostructure.Graph.PathChords
import Hypostructure.Core.DyadicLength

/-!
# Cycle-space interaction: thetas, shared segments, chords of cycles, path fans

Vocabulary-free (register coordinate C07).  Every statement is about paths and
cycles of one given graph `H`; the target is passed as the hypothesis
`avoids : ¬ ∃ c (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length`, the form
already used by `PathChords` (`avoids_of_not_hasCycle` produces it from G's
`¬ HasCycleWithLength LengthOK object`).

* `pair_isCycle`: two internally disjoint `u`–`v` paths, not both the same
  edge, close the explicit cycle `p ++ q⁻¹` of length `|p| + |q|`
  (`pair_not_ok`: that length is not accepted).
* `theta_cycles` / `theta_not_ok`: a theta (three pairwise internally disjoint,
  pairwise distinct `u`–`v` paths of lengths `a, b, c`) carries the three cycles
  of lengths `a + b`, `b + c`, `a + c`; none is accepted.
* `shared_segment_cycles` / `shared_segment_not_ok`: two cycles
  `C₁ = P ++ Q₁⁻¹`, `C₂ = P ++ Q₂⁻¹` sharing exactly the segment `P` have the
  symmetric-difference cycle `D = Q₁ ++ Q₂⁻¹` with
  `|D| + 2|P| = |C₁| + |C₂|`; none of `C₁, C₂, D` is accepted.
* `cycle_chord_cycles` / `cycle_chord_not_ok`: a cycle `c = p₁ ++ p₂ ++ p₃`
  (`|p₁| = i`, `|p₂| = j - i`) with a chord between the ends of `p₂` splits into
  the two explicit cycles `p₂ ++ chord` of length `(j - i) + 1` and
  `chord ++ p₃ ++ p₁` of length `|c| - (j - i) + 1`; neither is accepted.
* `fan_cycles` / `fan_not_ok` / `fan_pairSums`: `k` pairwise internally disjoint,
  pairwise distinct `u`–`v` paths `P i`: every pair `i ≠ j` closes
  `P i ++ (P j)⁻¹` of length `L i + L j`, none accepted; the set `pairSums L` of
  distinct cycle lengths so obtained has `2 m ≤ |pairSums L| + 3`, where `m` is
  the number of distinct path lengths (`pairSums_card`).
* Dyadic instantiation (`LengthOK = Core.DyadicLength.PowerOfTwoLength`):
  `not_pow2_iff_mod3` is the exact residue split of the exclusion, `pow2_mod_four`
  / `pow2_mod_three` the classes it never touches, `theta_dyadic`,
  `fan_equal_length_dyadic`, and `dyadic_filter_mod3_blind` (the exclusion,
  alone, restricts no residue triple `(a, b, c)` mod 3).
-/

namespace Hypostructure.Graph.ThetaCycles

open Hypostructure
open Hypostructure.Graph

universe u

/-! ## Two internally disjoint paths -/

section Pair

variable {V : Type u} {H : SimpleGraph V}

/-- `p` and `q` (both `u ⇝ v`) meet only at their ends. -/
def InternallyDisjoint {u v : V} (p q : H.Walk u v) : Prop :=
  ∀ y, y ∈ p.support → y ∈ q.support → y = u ∨ y = v

theorem InternallyDisjoint.symm {u v : V} {p q : H.Walk u v} (h : InternallyDisjoint p q) :
    InternallyDisjoint q p := fun y hq hp => h y hp hq

theorem one_le_length_of_ne {u v : V} (p : H.Walk u v) (h : u ≠ v) : 1 ≤ p.length := by
  cases p with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- Two distinct `u`–`v` walks are not both single edges. -/
theorem not_both_one_of_ne {u v : V} {p q : H.Walk u v} (hpq : p ≠ q) :
    ¬ (p.length = 1 ∧ q.length = 1) := by
  rintro ⟨hp, hq⟩
  apply hpq
  cases p with
  | nil => simp at hp
  | cons h p' =>
    cases q with
    | nil => simp at hq
    | cons h' q' =>
      simp only [SimpleGraph.Walk.length_cons, Nat.add_eq_right] at hp hq
      obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero hp
      obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero hq
      rw [SimpleGraph.Walk.length_eq_zero_iff] at hp hq
      obtain rfl := hp.eq_nil
      obtain rfl := hq.eq_nil
      rfl

/-- **Two internally disjoint `u`–`v` paths, not both single edges, close the
cycle `p ++ q⁻¹`** of length `|p| + |q|. -/
theorem pair_isCycle {u v : V} (hne : u ≠ v) {p q : H.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (disj : InternallyDisjoint p q) (nd : ¬ (p.length = 1 ∧ q.length = 1)) :
    (p.append q.reverse).IsCycle ∧ (p.append q.reverse).length = p.length + q.length := by
  refine ⟨?_, by simp⟩
  have hqr : q.reverse.IsPath := hq.reverse
  refine hp.isCycle_append hqr ?_ ?_
  · intro y yp yq
    have yp' : y ∈ p.support := List.mem_of_mem_tail yp
    have yq' : y ∈ q.support := by
      have := List.mem_of_mem_tail yq
      simpa [SimpleGraph.Walk.support_reverse] using this
    rcases disj y yp' yq' with rfl | rfl
    · have nd := hp.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support p] at nd
      exact (List.nodup_cons.mp nd).1 yp
    · have nd := hqr.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support q.reverse] at nd
      exact (List.nodup_cons.mp nd).1 yq
  · have h1 := one_le_length_of_ne p hne
    have h2 := one_le_length_of_ne q hne
    simp only [SimpleGraph.Walk.length_reverse]
    omega

/-- **The sum of the lengths of two internally disjoint `u`–`v` paths (not both
single edges) is not accepted.** -/
theorem pair_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} (hne : u ≠ v) {p q : H.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (disj : InternallyDisjoint p q) (nd : ¬ (p.length = 1 ∧ q.length = 1)) :
    ¬ LengthOK (p.length + q.length) := by
  intro ok
  obtain ⟨hc, hl⟩ := pair_isCycle hne hp hq disj nd
  exact avoids ⟨u, _, hc, hl ▸ ok⟩

end Pair

/-! ## The theta -/

section Theta

variable {V : Type u} {H : SimpleGraph V}

/-- **Theta.**  Three pairwise internally disjoint, pairwise distinct `u`–`v`
paths close the three explicit cycles `pᵢ ++ pⱼ⁻¹` of lengths `a + b`, `b + c`,
`a + c`. -/
theorem theta_cycles {u v : V} (hne : u ≠ v) {p₁ p₂ p₃ : H.Walk u v}
    (h₁ : p₁.IsPath) (h₂ : p₂.IsPath) (h₃ : p₃.IsPath)
    (d₁₂ : InternallyDisjoint p₁ p₂) (d₂₃ : InternallyDisjoint p₂ p₃)
    (d₁₃ : InternallyDisjoint p₁ p₃)
    (n₁₂ : p₁ ≠ p₂) (n₂₃ : p₂ ≠ p₃) (n₁₃ : p₁ ≠ p₃) :
    ((p₁.append p₂.reverse).IsCycle ∧
        (p₁.append p₂.reverse).length = p₁.length + p₂.length) ∧
      ((p₂.append p₃.reverse).IsCycle ∧
        (p₂.append p₃.reverse).length = p₂.length + p₃.length) ∧
      ((p₁.append p₃.reverse).IsCycle ∧
        (p₁.append p₃.reverse).length = p₁.length + p₃.length) :=
  ⟨pair_isCycle hne h₁ h₂ d₁₂ (not_both_one_of_ne n₁₂),
    pair_isCycle hne h₂ h₃ d₂₃ (not_both_one_of_ne n₂₃),
    pair_isCycle hne h₁ h₃ d₁₃ (not_both_one_of_ne n₁₃)⟩

/-- **Theta, target form.**  With `a = |p₁|, b = |p₂|, c = |p₃|`: none of
`a + b`, `b + c`, `a + c` is accepted. -/
theorem theta_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} (hne : u ≠ v) {p₁ p₂ p₃ : H.Walk u v}
    (h₁ : p₁.IsPath) (h₂ : p₂.IsPath) (h₃ : p₃.IsPath)
    (d₁₂ : InternallyDisjoint p₁ p₂) (d₂₃ : InternallyDisjoint p₂ p₃)
    (d₁₃ : InternallyDisjoint p₁ p₃)
    (n₁₂ : p₁ ≠ p₂) (n₂₃ : p₂ ≠ p₃) (n₁₃ : p₁ ≠ p₃) :
    ¬ LengthOK (p₁.length + p₂.length) ∧ ¬ LengthOK (p₂.length + p₃.length) ∧
      ¬ LengthOK (p₁.length + p₃.length) :=
  ⟨pair_not_ok avoids hne h₁ h₂ d₁₂ (not_both_one_of_ne n₁₂),
    pair_not_ok avoids hne h₂ h₃ d₂₃ (not_both_one_of_ne n₂₃),
    pair_not_ok avoids hne h₁ h₃ d₁₃ (not_both_one_of_ne n₁₃)⟩

end Theta

/-! ## Two cycles sharing exactly one segment -/

section SharedSegment

variable {V : Type u} {H : SimpleGraph V}

/-- **Two cycles sharing exactly one segment.**  `C₁ = P ++ Q₁⁻¹` and
`C₂ = P ++ Q₂⁻¹`, where `P, Q₁, Q₂` are pairwise internally disjoint, pairwise
distinct `u`–`v` paths (so `C₁ ∩ C₂ = P`), are cycles, and their symmetric
difference `D = Q₁ ++ Q₂⁻¹` is a cycle with `|D| + 2|P| = |C₁| + |C₂|`. -/
theorem shared_segment_cycles {u v : V} (hne : u ≠ v) {P Q₁ Q₂ : H.Walk u v}
    (hP : P.IsPath) (hQ₁ : Q₁.IsPath) (hQ₂ : Q₂.IsPath)
    (d₁ : InternallyDisjoint P Q₁) (d₂ : InternallyDisjoint P Q₂)
    (d₁₂ : InternallyDisjoint Q₁ Q₂)
    (n₁ : P ≠ Q₁) (n₂ : P ≠ Q₂) (n₁₂ : Q₁ ≠ Q₂) :
    (P.append Q₁.reverse).IsCycle ∧ (P.append Q₂.reverse).IsCycle ∧
      (Q₁.append Q₂.reverse).IsCycle ∧
      (Q₁.append Q₂.reverse).length + 2 * P.length =
        (P.append Q₁.reverse).length + (P.append Q₂.reverse).length := by
  obtain ⟨c₁, -⟩ := pair_isCycle hne hP hQ₁ d₁ (not_both_one_of_ne n₁)
  obtain ⟨c₂, -⟩ := pair_isCycle hne hP hQ₂ d₂ (not_both_one_of_ne n₂)
  obtain ⟨d, -⟩ := pair_isCycle hne hQ₁ hQ₂ d₁₂ (not_both_one_of_ne n₁₂)
  refine ⟨c₁, c₂, d, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-- **Shared segment, target form.**  None of `|C₁| = |P| + |Q₁|`,
`|C₂| = |P| + |Q₂|`, `|D| = |C₁| + |C₂| - 2|P| = |Q₁| + |Q₂|` is accepted. -/
theorem shared_segment_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} (hne : u ≠ v) {P Q₁ Q₂ : H.Walk u v}
    (hP : P.IsPath) (hQ₁ : Q₁.IsPath) (hQ₂ : Q₂.IsPath)
    (d₁ : InternallyDisjoint P Q₁) (d₂ : InternallyDisjoint P Q₂)
    (d₁₂ : InternallyDisjoint Q₁ Q₂)
    (n₁ : P ≠ Q₁) (n₂ : P ≠ Q₂) (n₁₂ : Q₁ ≠ Q₂) :
    ¬ LengthOK (P.length + Q₁.length) ∧ ¬ LengthOK (P.length + Q₂.length) ∧
      ¬ LengthOK ((P.length + Q₁.length) + (P.length + Q₂.length) - 2 * P.length) := by
  refine ⟨pair_not_ok avoids hne hP hQ₁ d₁ (not_both_one_of_ne n₁),
    pair_not_ok avoids hne hP hQ₂ d₂ (not_both_one_of_ne n₂), ?_⟩
  have e : (P.length + Q₁.length) + (P.length + Q₂.length) - 2 * P.length =
      Q₁.length + Q₂.length := by omega
  rw [e]
  exact pair_not_ok avoids hne hQ₁ hQ₂ d₁₂ (not_both_one_of_ne n₁₂)

end SharedSegment

/-! ## A chord of a cycle -/

section CycleChord

variable {V : Type u} {H : SimpleGraph V}

/-- Rotating a cycle `p₁ ++ p₂ ++ p₃` to `p₂ ++ p₃ ++ p₁` keeps it a cycle. -/
theorem rotate_decomp_isCycle {x u w : V} {p₁ : H.Walk x u} {p₂ : H.Walk u w}
    {p₃ : H.Walk w x} (hc : (p₁.append (p₂.append p₃)).IsCycle) :
    (p₂.append (p₃.append p₁)).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def] at hc ⊢
  obtain ⟨ht, hnil, hnd⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def] at ht ⊢
    simp only [SimpleGraph.Walk.edges_append] at ht ⊢
    refine (List.Perm.nodup_iff ?_).1 ht
    have := (List.perm_append_comm (l₁ := p₁.edges) (l₂ := p₂.edges ++ p₃.edges))
    simpa [List.append_assoc] using this
  · intro h
    apply hnil
    have hl := congrArg SimpleGraph.Walk.length h
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_nil] at hl
    refine (SimpleGraph.Walk.length_eq_zero_iff.1 ?_).eq_nil
    simp only [SimpleGraph.Walk.length_append]
    omega
  · simp only [SimpleGraph.Walk.tail_support_append] at hnd ⊢
    refine (List.Perm.nodup_iff ?_).1 hnd
    have := (List.perm_append_comm (l₁ := p₁.support.tail)
      (l₂ := p₂.support.tail ++ p₃.support.tail))
    simpa [List.append_assoc] using this

/-- **A chord of a cycle.**  A cycle `c = p₁ ++ p₂ ++ p₃` (chord positions
`i = |p₁| < j = |p₁| + |p₂|`) with a chord `uw` between the ends of `p₂`, where
`2 ≤ |p₂|` and `2 ≤ |p₁| + |p₃|` (the chord is not an edge of `c`), splits into
the two explicit cycles `p₂ ++ (w u)` of length `(j - i) + 1` and
`(u w) ++ p₃ ++ p₁` of length `|c| - (j - i) + 1`. -/
theorem cycle_chord_cycles {x u w : V} {c : H.Walk x x} (hc : c.IsCycle)
    {p₁ : H.Walk x u} {p₂ : H.Walk u w} {p₃ : H.Walk w x}
    (heq : c = p₁.append (p₂.append p₃)) (adj : H.Adj u w)
    (h₂ : 2 ≤ p₂.length) (h₁₃ : 2 ≤ p₁.length + p₃.length) :
    (p₂.append (SimpleGraph.Walk.cons adj.symm SimpleGraph.Walk.nil)).IsCycle ∧
      (p₂.append (SimpleGraph.Walk.cons adj.symm SimpleGraph.Walk.nil)).length =
        p₂.length + 1 ∧
      (SimpleGraph.Walk.cons adj (p₃.append p₁)).IsCycle ∧
      (SimpleGraph.Walk.cons adj (p₃.append p₁)).length = c.length - p₂.length + 1 := by
  subst heq
  have hq := rotate_decomp_isCycle hc
  have hp₂ : p₂.IsPath := hq.isPath_of_append_left (by
    rw [← SimpleGraph.Walk.length_eq_zero_iff, SimpleGraph.Walk.length_append]; omega)
  have hr : (p₃.append p₁).IsPath := hq.isPath_of_append_right (by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega)
  have hne : u ≠ w := adj.ne
  have edge_wu : (SimpleGraph.Walk.cons adj.symm (SimpleGraph.Walk.nil : H.Walk u u)).IsPath := by
    simp [hne.symm]
  have edge_uw : (SimpleGraph.Walk.cons adj (SimpleGraph.Walk.nil : H.Walk w w)).IsPath := by
    simp [hne]
  refine ⟨?_, by simp, ?_, by simp; omega⟩
  · refine hp₂.isCycle_append edge_wu ?_ (Or.inl (by omega))
    intro y yp yq
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.mem_singleton] at yq
    subst yq
    have nd := hp₂.support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support p₂] at nd
    exact (List.nodup_cons.mp nd).1 yp
  · have e : SimpleGraph.Walk.cons adj (p₃.append p₁) =
        (SimpleGraph.Walk.cons adj SimpleGraph.Walk.nil).append (p₃.append p₁) := by simp
    rw [e]
    refine edge_uw.isCycle_append hr ?_ (Or.inr (by simp; omega))
    intro y yp yq
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.mem_singleton] at yp
    subst yp
    have nd := hr.support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support (p₃.append p₁)] at nd
    exact (List.nodup_cons.mp nd).1 yq

/-- **A chord of a cycle, target form.**  Neither `(j - i) + 1 = |p₂| + 1` nor
`L - (j - i) + 1 = |c| - |p₂| + 1` is accepted. -/
theorem cycle_chord_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {x u w : V} {c : H.Walk x x} (hc : c.IsCycle)
    {p₁ : H.Walk x u} {p₂ : H.Walk u w} {p₃ : H.Walk w x}
    (heq : c = p₁.append (p₂.append p₃)) (adj : H.Adj u w)
    (h₂ : 2 ≤ p₂.length) (h₁₃ : 2 ≤ p₁.length + p₃.length) :
    ¬ LengthOK (p₂.length + 1) ∧ ¬ LengthOK (c.length - p₂.length + 1) := by
  obtain ⟨c₁, l₁, c₂, l₂⟩ := cycle_chord_cycles hc heq adj h₂ h₁₃
  exact ⟨fun ok => avoids ⟨u, _, c₁, by rw [l₁]; exact ok⟩,
    fun ok => avoids ⟨u, _, c₂, by rw [l₂]; exact ok⟩⟩

end CycleChord

/-! ## A fan of `k` internally disjoint paths -/

section Fan

variable {V : Type u} {H : SimpleGraph V}

/-- The set of pairwise sums `L i + L j`, `i ≠ j`: the distinct cycle lengths
closed by a fan of paths of lengths `L`. -/
def pairSums {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ℕ) : Finset ℕ :=
  (Finset.univ.offDiag).image (fun ij : ι × ι => L ij.1 + L ij.2)

theorem mem_pairSums {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ℕ) (s : ℕ) :
    s ∈ pairSums L ↔ ∃ i j, i ≠ j ∧ L i + L j = s := by
  simp [pairSums, Finset.mem_offDiag]

/-- The number of ordered index pairs of a fan of `k` paths is `2 · C(k, 2)`. -/
theorem offDiag_card_fin (k : ℕ) :
    ((Finset.univ : Finset (Fin k)).offDiag).card = 2 * k.choose 2 := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]
  have h2 : 2 ∣ k * (k - 1) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (m + m - 1), by ring⟩
    · exact ⟨(2 * m + 1) * m, by simp; ring⟩
  rw [Nat.mul_div_cancel' h2, Nat.mul_sub, mul_one]

/-- **Distinct pair sums.**  If the lengths take `m` distinct values, the fan
closes at least `2m - 3` distinct cycle lengths: `2m ≤ |pairSums L| + 3`. -/
theorem pairSums_card {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ℕ) :
    2 * (Finset.univ.image L).card ≤ (pairSums L).card + 3 := by
  set A := Finset.univ.image L with hA
  by_cases small : A.card ≤ 1
  · omega
  have ne : A.Nonempty := Finset.card_pos.1 (by omega)
  set a := A.min' ne
  set b := A.max' ne
  have ha : a ∈ A := A.min'_mem ne
  have hb : b ∈ A := A.max'_mem ne
  have hab : a < b := A.min'_lt_max'_of_card (by omega)
  set S₁ := (A.erase a).image (fun x => a + x)
  set S₂ := ((A.erase a).erase b).image (fun x => x + b)
  have c₁ : S₁.card = A.card - 1 := by
    rw [Finset.card_image_of_injective _ (add_right_injective a), Finset.card_erase_of_mem ha]
  have c₂ : S₂.card = A.card - 2 := by
    rw [Finset.card_image_of_injective _ (add_left_injective b),
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab.ne', hb⟩), Finset.card_erase_of_mem ha]
    omega
  have disj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro s h₁ h₂
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 h₂
    have hxb : x ≤ b := A.le_max' x (Finset.mem_of_mem_erase hx)
    have hy' := Finset.mem_erase.1 hy
    have hya : y ≠ a := (Finset.mem_erase.1 hy'.2).1
    have hay : a ≤ y := A.min'_le y (Finset.mem_of_mem_erase hy'.2)
    omega
  have sub : S₁ ∪ S₂ ⊆ pairSums L := by
    intro s hs
    rw [mem_pairSums]
    rcases Finset.mem_union.1 hs with h | h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hxa, hxA⟩ := Finset.mem_erase.1 hx
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 ha
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hxA
      refine ⟨i, j, ?_, by rw [hi, hj]⟩
      rintro rfl; exact hxa (hj ▸ hi)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hyb, hyA⟩ := Finset.mem_erase.1 hy
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hyA)
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hb
      refine ⟨i, j, ?_, by rw [hi, hj]⟩
      rintro rfl; exact hyb (hi ▸ hj)
  have := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint disj, c₁, c₂] at this
  omega

/-- **Fan.**  `k` pairwise internally disjoint, pairwise distinct `u`–`v` paths:
every pair `i ≠ j` closes the explicit cycle `P i ++ (P j)⁻¹` of length
`|P i| + |P j|`. -/
theorem fan_cycles {ι : Type*} {u v : V} (hne : u ≠ v) (P : ι → H.Walk u v)
    (hP : ∀ i, (P i).IsPath) (disj : ∀ i j, i ≠ j → InternallyDisjoint (P i) (P j))
    (inj : Function.Injective P) {i j : ι} (hij : i ≠ j) :
    ((P i).append (P j).reverse).IsCycle ∧
      ((P i).append (P j).reverse).length = (P i).length + (P j).length :=
  pair_isCycle hne (hP i) (hP j) (disj i j hij) (not_both_one_of_ne (inj.ne hij))

/-- **Fan, target form.**  No pairwise sum `L i + L j` (`i ≠ j`) is accepted. -/
theorem fan_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {ι : Type*} {u v : V} (hne : u ≠ v) (P : ι → H.Walk u v)
    (hP : ∀ i, (P i).IsPath) (disj : ∀ i j, i ≠ j → InternallyDisjoint (P i) (P j))
    (inj : Function.Injective P) {i j : ι} (hij : i ≠ j) :
    ¬ LengthOK ((P i).length + (P j).length) :=
  pair_not_ok avoids hne (hP i) (hP j) (disj i j hij) (not_both_one_of_ne (inj.ne hij))

/-- **Fan, all distinct cycle lengths.**  Every element of
`pairSums (|P ·|)` is the length of a cycle of `H` and is not accepted; there are
at least `2m - 3` of them, `m` the number of distinct path lengths. -/
theorem fan_pairSums {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : V} (hne : u ≠ v) (P : ι → H.Walk u v)
    (hP : ∀ i, (P i).IsPath) (disj : ∀ i j, i ≠ j → InternallyDisjoint (P i) (P j))
    (inj : Function.Injective P) :
    (∀ s ∈ pairSums (fun i => (P i).length),
      (∃ cy : H.Walk u u, cy.IsCycle ∧ cy.length = s) ∧ ¬ LengthOK s) ∧
      2 * (Finset.univ.image (fun i => (P i).length)).card ≤
        (pairSums (fun i => (P i).length)).card + 3 := by
  refine ⟨fun s hs => ?_, pairSums_card _⟩
  obtain ⟨i, j, hij, rfl⟩ := (mem_pairSums _ s).1 hs
  obtain ⟨hc, hl⟩ := fan_cycles hne P hP disj inj hij
  exact ⟨⟨_, hc, hl⟩, fan_not_ok avoids hne P hP disj inj hij⟩

/-- **Two equal-length strands of a fan.**  `i ≠ j` with `|P i| = |P j| = ℓ`:
`2ℓ` is not accepted. -/
theorem fan_equal_length_not_ok {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {ι : Type*} {u v : V} (hne : u ≠ v) (P : ι → H.Walk u v)
    (hP : ∀ i, (P i).IsPath) (disj : ∀ i j, i ≠ j → InternallyDisjoint (P i) (P j))
    (inj : Function.Injective P) {i j : ι} (hij : i ≠ j) (eq : (P i).length = (P j).length) :
    ¬ LengthOK (2 * (P i).length) := by
  have := fan_not_ok avoids hne P hP disj inj hij
  rwa [← eq, ← two_mul] at this

end Fan

/-! ## Bridge from G's target hypothesis -/

/-- G's published target avoidance gives the `avoids` form used above. -/
theorem avoids_of_not_hasCycle {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    (h : ¬ HasCycleWithLength LengthOK object) :
    ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length :=
  fun ⟨c, cy, hc, ok⟩ => h ⟨⟨c, cy, hc, ok⟩⟩

/-! ## Dyadic instantiation -/

section Dyadic

open Core.DyadicLength

/-- The dyadic exclusion in exponent form: `s ∉ {4, 8, 16, …}`. -/
theorem not_pow2_iff (s : ℕ) :
    ¬ PowerOfTwoLength s ↔ ∀ e, 2 ≤ e → s ≠ 2 ^ e := by
  rw [powerOfTwoLength_iff]
  exact ⟨fun h e he eq => h ⟨e, he, eq⟩, fun h ⟨e, he, eq⟩ => h e he eq⟩

theorem four_pow_mod_three (m : ℕ) : 4 ^ m % 3 = 1 := by
  rw [Nat.pow_mod]; simp

/-- Accepted dyadic lengths are `≡ 0 (mod 4)`. -/
theorem pow2_mod_four {s : ℕ} (h : PowerOfTwoLength s) : s % 4 = 0 := by
  obtain ⟨e, he, rfl⟩ := (powerOfTwoLength_iff s).1 h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add]; simp

/-- Accepted dyadic lengths are never `≡ 0 (mod 3)`: `2^e ≡ (-1)^e`. -/
theorem pow2_mod_three {s : ℕ} (h : PowerOfTwoLength s) : s % 3 ≠ 0 := by
  obtain ⟨e, -, rfl⟩ := (powerOfTwoLength_iff s).1 h
  rcases Nat.even_or_odd e with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul, pow_mul]; norm_num [four_pow_mod_three]
  · rw [pow_succ, pow_mul]; norm_num [Nat.mul_mod, four_pow_mod_three]

/-- **Exact residue split of the dyadic exclusion.**  `s` is not an accepted
dyadic length iff `s ≡ 0 (mod 3)`, or `s ≡ 1` and `s` is no power `4^e` (`e ≥ 1`),
or `s ≡ 2` and `s` is no `2·4^e` (`e ≥ 1`). -/
theorem not_pow2_iff_mod3 (s : ℕ) :
    ¬ PowerOfTwoLength s ↔
      s % 3 = 0 ∨ (s % 3 = 1 ∧ ∀ e, 1 ≤ e → s ≠ 4 ^ e) ∨
        (s % 3 = 2 ∧ ∀ e, 1 ≤ e → s ≠ 2 * 4 ^ e) := by
  rw [not_pow2_iff]
  constructor
  · intro h
    have : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2) with h0 | h1 | h2
    · exact Or.inl h0
    · refine Or.inr (Or.inl ⟨h1, fun e he eq => h (2 * e) (by omega) ?_⟩)
      rw [eq, pow_mul]; norm_num
    · refine Or.inr (Or.inr ⟨h2, fun e he eq => h (2 * e + 1) (by omega) ?_⟩)
      rw [eq, pow_succ, pow_mul]; norm_num; ring
  · rintro h e he rfl
    rcases Nat.even_or_odd e with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : 4 ^ m % 3 = 1 := four_pow_mod_three m
      have e4 : (2 : ℕ) ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
      rw [e4] at h
      rcases h with h | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h m (by omega) rfl
      · omega
    · have hm : 4 ^ m % 3 = 1 := four_pow_mod_three m
      have e4 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
      rw [e4] at h
      rcases h with h | ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · omega
      · exact h m (by omega) rfl

/-- **Theta, dyadic form.**  With `a = |p₁|, b = |p₂|, c = |p₃|`: for every
`e ≥ 2`, `a + b ≠ 2^e`, `b + c ≠ 2^e`, `a + c ≠ 2^e`; and each of the three sums
satisfies the exact residue split `not_pow2_iff_mod3`. -/
theorem theta_dyadic {V : Type u} {H : SimpleGraph V}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ PowerOfTwoLength cy.length)
    {u v : V} (hne : u ≠ v) {p₁ p₂ p₃ : H.Walk u v}
    (h₁ : p₁.IsPath) (h₂ : p₂.IsPath) (h₃ : p₃.IsPath)
    (d₁₂ : InternallyDisjoint p₁ p₂) (d₂₃ : InternallyDisjoint p₂ p₃)
    (d₁₃ : InternallyDisjoint p₁ p₃)
    (n₁₂ : p₁ ≠ p₂) (n₂₃ : p₂ ≠ p₃) (n₁₃ : p₁ ≠ p₃) :
    (∀ e, 2 ≤ e → p₁.length + p₂.length ≠ 2 ^ e ∧ p₂.length + p₃.length ≠ 2 ^ e ∧
        p₁.length + p₃.length ≠ 2 ^ e) ∧
      (∀ s ∈ [p₁.length + p₂.length, p₂.length + p₃.length, p₁.length + p₃.length],
        s % 3 = 0 ∨ (s % 3 = 1 ∧ ∀ e, 1 ≤ e → s ≠ 4 ^ e) ∨
          (s % 3 = 2 ∧ ∀ e, 1 ≤ e → s ≠ 2 * 4 ^ e)) := by
  obtain ⟨t₁, t₂, t₃⟩ := theta_not_ok avoids hne h₁ h₂ h₃ d₁₂ d₂₃ d₁₃ n₁₂ n₂₃ n₁₃
  refine ⟨fun e he => ⟨(not_pow2_iff _).1 t₁ e he, (not_pow2_iff _).1 t₂ e he,
    (not_pow2_iff _).1 t₃ e he⟩, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (not_pow2_iff_mod3 _).1 t₁
  · exact (not_pow2_iff_mod3 _).1 t₂
  · exact (not_pow2_iff_mod3 _).1 t₃

/-- **Two equal-length strands, dyadic form.**  `i ≠ j`, `|P i| = |P j| = ℓ`:
`ℓ ∉ {2, 4, 8, …}` (`2ℓ` is no `2^e`, `e ≥ 2`). -/
theorem fan_equal_length_dyadic {V : Type u} {H : SimpleGraph V}
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ PowerOfTwoLength cy.length)
    {ι : Type*} {u v : V} (hne : u ≠ v) (P : ι → H.Walk u v)
    (hP : ∀ i, (P i).IsPath) (disj : ∀ i j, i ≠ j → InternallyDisjoint (P i) (P j))
    (inj : Function.Injective P) {i j : ι} (hij : i ≠ j) (eq : (P i).length = (P j).length) :
    ∀ e, 1 ≤ e → (P i).length ≠ 2 ^ e := by
  intro e he h
  have := (not_pow2_iff _).1 (fan_equal_length_not_ok avoids hne P hP disj inj hij eq) (e + 1)
    (by omega)
  rw [h, pow_succ] at this
  exact this (by ring)

/-- **The dyadic exclusion alone carries no mod-3 information on a triple.**
A statement about the predicate, not about `G`: for every residue triple
`(r₁, r₂, r₃)` mod 3 there are `a, b, c` with those residues and none of
`a + b, b + c, a + c` an accepted dyadic length (take `a, b, c ∈ {1, 5, 9}`, all
`≡ 1 (mod 4)`, so every pair sum is `≡ 2 (mod 4)`).  So `theta_not_ok` at `G`
restricts `(a, b, c)` mod 3 not at all; its whole content is `theta_dyadic`. -/
theorem dyadic_filter_mod3_blind (r₁ r₂ r₃ : Fin 3) :
    ∃ a b c : ℕ, a % 3 = r₁ ∧ b % 3 = r₂ ∧ c % 3 = r₃ ∧
      ¬ PowerOfTwoLength (a + b) ∧ ¬ PowerOfTwoLength (b + c) ∧
      ¬ PowerOfTwoLength (a + c) := by
  let f : Fin 3 → ℕ := fun r => if r.1 = 0 then 9 else if r.1 = 1 then 1 else 5
  have hf : ∀ r, f r % 3 = r.1 ∧ f r % 4 = 1 := by decide
  have np : ∀ x y : Fin 3, ¬ PowerOfTwoLength (f x + f y) := by
    intro x y h
    have := pow2_mod_four h
    have hx := (hf x).2
    have hy := (hf y).2
    omega
  exact ⟨f r₁, f r₂, f r₃, (hf r₁).1, (hf r₂).1, (hf r₃).1, np _ _, np _ _, np _ _⟩

end Dyadic

end Hypostructure.Graph.ThetaCycles
