import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# The window lemma of the ladder analysis (`[144a]`, G audit S144a)

Vocabulary-free, pure integer combinatorics.  A *window* is eight consecutive rungs
`σ 0, …, σ 7` (the positions on the second path of the partners of eight consecutive
vertices of the first path).  If

* consecutive displacements are in `{−3, −2, 2, 3}`,
* the positions are pairwise distinct,
* no two rungs `i < j` have `(j − i) + |σ j − σ i| ∈ {2, 6, 14}` (a cycle of length 4, 8, 16),
* the neighbours `σ i ± 1` of the two deep rungs `i = 3, 4` are again positions of rungs
  whose index differs from `i` by 2 or 3,

then we have a contradiction.  So a run of eight rungs always has a free position next
to a deep rung.
-/

namespace Hypostructure.Graph.LadderWindow

/-- the partial sums of seven steps -/
def part (a b c d e f g : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => a
  | 2 => a + b
  | 3 => a + b + c
  | 4 => a + b + c + d
  | 5 => a + b + c + d + e
  | 6 => a + b + c + d + e + f
  | _ => a + b + c + d + e + f + g

def OkInj (s : ℕ → ℤ) : Prop :=
  ∀ i ∈ List.range 8, ∀ j ∈ List.range 8, i < j → s i ≠ s j
def OkPair (s : ℕ → ℤ) : Prop :=
  ∀ i ∈ List.range 8, ∀ j ∈ List.range 8, i < j →
    ((j : ℤ) - (i : ℤ)) + |s j - s i| ≠ 2 ∧
      ((j : ℤ) - (i : ℤ)) + |s j - s i| ≠ 6 ∧ ((j : ℤ) - (i : ℤ)) + |s j - s i| ≠ 14
def OkClosed (s : ℕ → ℤ) : Prop :=
  ∀ i ∈ List.range 8, 3 ≤ i → i ≤ 4 → ∀ e ∈ ([1, -1] : List ℤ),
      ∃ k ∈ List.range 8, s k = s i + e ∧ (k = i + 2 ∨ k = i + 3 ∨ i = k + 2 ∨ i = k + 3)

instance (s : ℕ → ℤ) : Decidable (OkInj s) := by unfold OkInj; infer_instance
instance (s : ℕ → ℤ) : Decidable (OkPair s) := by unfold OkPair; infer_instance
instance (s : ℕ → ℤ) : Decidable (OkClosed s) := by unfold OkClosed; infer_instance

/-- the constraints on eight rungs -/
def Ok (s : ℕ → ℤ) : Prop := OkInj s ∧ OkPair s ∧ OkClosed s

instance (s : ℕ → ℤ) : Decidable (Ok s) := by unfold Ok; infer_instance

theorem finite_check :
    ∀ a ∈ ([-3, -2, 2, 3] : List ℤ), ∀ b ∈ ([-3, -2, 2, 3] : List ℤ),
    ∀ c ∈ ([-3, -2, 2, 3] : List ℤ), ∀ d ∈ ([-3, -2, 2, 3] : List ℤ),
    ∀ e ∈ ([-3, -2, 2, 3] : List ℤ), ∀ f ∈ ([-3, -2, 2, 3] : List ℤ),
    ∀ g ∈ ([-3, -2, 2, 3] : List ℤ), ¬ Ok (part a b c d e f g) := by
  decide +kernel


theorem ok_shift (t : ℕ → ℤ) (c : ℤ) (h : Ok (fun i => t i + c)) : Ok t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hij heq
    exact h1 i hi j hj hij (by simp [heq])
  · intro i hi j hj hij
    have := h2 i hi j hj hij
    simpa using this
  · intro i hi h3i h4i e he
    obtain ⟨k, hk, hkeq, hkidx⟩ := h3 i hi h3i h4i e he
    exact ⟨k, hk, by simpa [add_assoc, add_comm, add_left_comm] using hkeq, hkidx⟩

theorem ok_congr (s t : ℕ → ℤ) (h : ∀ i < 8, s i = t i) (hs : Ok s) : Ok t := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hm : ∀ i ∈ List.range 8, s i = t i := fun i hi => h i (List.mem_range.1 hi)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hij heq
    exact h1 i hi j hj hij (by rw [hm i hi, hm j hj]; exact heq)
  · intro i hi j hj hij
    have := h2 i hi j hj hij
    rwa [hm i hi, hm j hj] at this
  · intro i hi h3i h4i e he
    obtain ⟨k, hk, hkeq, hkidx⟩ := h3 i hi h3i h4i e he
    exact ⟨k, hk, by rw [← hm k hk, ← hm i hi]; exact hkeq, hkidx⟩

/-- **The window lemma.**  Eight rungs `σ 0, …, σ 7` with displacements in `{−3, −2, 2, 3}`,
pairwise distinct positions, no pair at `(j − i) + |σ j − σ i| ∈ {2, 6, 14}`, and with the two
deep rungs `i = 3, 4` having both neighbours `σ i ± 1` among the rung positions at index
distance 2 or 3, do not exist. -/
theorem window8 (σ : ℕ → ℤ)
    (step : ∀ i < 7, σ (i + 1) - σ i = -3 ∨ σ (i + 1) - σ i = -2 ∨ σ (i + 1) - σ i = 2 ∨
      σ (i + 1) - σ i = 3)
    (ok : Ok σ) : False := by
  have hmem : ∀ i < 7, σ (i + 1) - σ i ∈ ([-3, -2, 2, 3] : List ℤ) := by
    intro i hi
    have := step i hi
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    exact this
  have key := finite_check (σ 1 - σ 0) (hmem 0 (by norm_num)) (σ 2 - σ 1) (hmem 1 (by norm_num))
    (σ 3 - σ 2) (hmem 2 (by norm_num)) (σ 4 - σ 3) (hmem 3 (by norm_num))
    (σ 5 - σ 4) (hmem 4 (by norm_num)) (σ 6 - σ 5) (hmem 5 (by norm_num))
    (σ 7 - σ 6) (hmem 6 (by norm_num))
  apply key
  apply ok_shift _ (σ 0)
  refine ok_congr σ _ ?_ ok
  intro i hi
  interval_cases i <;> simp [part] <;> ring

end Hypostructure.Graph.LadderWindow
