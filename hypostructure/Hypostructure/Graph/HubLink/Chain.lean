import Hypostructure.Graph.WindowCombination

/-!
# Hub chains are induced paths

Vocabulary-free.

`m` pairwise non-adjacent "hubs" `h 0, …, h (m-1)` joined consecutively by segments of `ℓ`
"connectors" `c i 0, …, c i (ℓ-1)` (segment `i` joins `h i` to `h (i+1)`).  If

* each segment is an induced path on `ℓ` vertices,
* a connector sees a chain hub only as the entry (`c i 0 ∼ h i`) or exit (`c i (ℓ-1) ∼ h (i+1)`),
* connectors of different segments are distinct and non-adjacent,

the chain `h 0, c 0 0, …, c 0 (ℓ-1), h 1, …, h (m-1)` is an induced path on
`(ℓ+1)(m-1) + 1` vertices (`chain_induced`).  For `ℓ = 2`, `m = 5` this is the 13-vertex path
`h₁ x₁ y₁ h₂ … x₄ y₄ h₅`; `ℓ = 3, m = 4`, `ℓ = 5, m = 3`, `ℓ = 11, m = 2` also give 13.
-/

open Finset Hypostructure.Graph.WindowCombination

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

theorem decode {p i a j b : ℕ} (ha : a < p) (hb : b < p) (h : p * i + a = p * j + b) :
    i = j ∧ a = b := by
  have hp : 0 < p := by omega
  have h1 : (p * i + a) / p = (p * j + b) / p := by rw [h]
  have h2 : (p * i + a) % p = (p * j + b) % p := by rw [h]
  rw [Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb] at h1
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact ⟨by simpa using h1, h2⟩

variable {V : Type*} (G : SimpleGraph V)

/-- The chain sequence: hub `h i` at position `(ℓ+1) i`, connector `c i a` at
`(ℓ+1) i + a + 1`. -/
def chainSeq (ℓ : ℕ) (h : ℕ → V) (c : ℕ → ℕ → V) (t : ℕ) : V :=
  if t % (ℓ + 1) = 0 then h (t / (ℓ + 1)) else c (t / (ℓ + 1)) (t % (ℓ + 1) - 1)

theorem chainSeq_view (ℓ m : ℕ) (h : ℕ → V) (c : ℕ → ℕ → V) (hm : 1 ≤ m) {s : ℕ}
    (hs : s ≤ (ℓ + 1) * (m - 1)) :
    (∃ i < m, s = (ℓ + 1) * i ∧ chainSeq ℓ h c s = h i) ∨
      (∃ i a, i + 1 < m ∧ a < ℓ ∧ s = (ℓ + 1) * i + (a + 1) ∧ chainSeq ℓ h c s = c i a) := by
  have hp : 0 < ℓ + 1 := by omega
  have hdm := Nat.div_add_mod s (ℓ + 1)
  have hmod := Nat.mod_lt s hp
  have hdiv : s / (ℓ + 1) ≤ m - 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hp]; nlinarith
  by_cases hr : s % (ℓ + 1) = 0
  · left
    refine ⟨s / (ℓ + 1), by omega, by omega, ?_⟩
    simp [chainSeq, hr]
  · right
    have hlt : s / (ℓ + 1) < m - 1 := by
      by_contra hge
      have he : s / (ℓ + 1) = m - 1 := by omega
      rw [he] at hdm
      omega
    refine ⟨s / (ℓ + 1), s % (ℓ + 1) - 1, by omega, by omega, by omega, ?_⟩
    simp [chainSeq, hr]

/-- **Hub chains are induced paths.** -/
theorem chain_induced (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) (h : ℕ → V) (c : ℕ → ℕ → V)
    (hH : ∀ i < m, ∀ j < m, i ≠ j → ¬ G.Adj (h i) (h j) ∧ h i ≠ h j)
    (hseg : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ b < ℓ,
      (G.Adj (c i a) (c i b) ↔ (a + 1 = b ∨ b + 1 = a)) ∧ (c i a = c i b → a = b))
    (hhc : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ j < m,
      (G.Adj (c i a) (h j) ↔ ((j = i ∧ a = 0) ∨ (j = i + 1 ∧ a + 1 = ℓ))) ∧ c i a ≠ h j)
    (hcross : ∀ i, i + 1 < m → ∀ j, j + 1 < m → i ≠ j → ∀ a < ℓ, ∀ b < ℓ,
      ¬ G.Adj (c i a) (c j b) ∧ c i a ≠ c j b) :
    InducedSeq G ((ℓ + 1) * (m - 1)) (chainSeq ℓ h c) := by
  set p := ℓ + 1 with hpdef
  have hp2 : 2 ≤ p := by omega
  -- hub / hub
  have hh : ∀ i < m, ∀ j < m,
      (G.Adj (h i) (h j) ↔ (p * i + 1 = p * j ∨ p * j + 1 = p * i)) := by
    intro i hi j hj
    constructor
    · intro hadj
      by_cases hij : i = j
      · subst hij; exact absurd hadj (G.irrefl)
      · exact absurd hadj (hH i hi j hj hij).1
    · rintro (e | e)
      · have := decode (p := p) (a := 1) (b := 0) (by omega) (by omega) (by simpa using e)
        omega
      · have := decode (p := p) (a := 1) (b := 0) (by omega) (by omega) (by simpa using e)
        omega
  -- connector / hub
  have ch : ∀ j a, j + 1 < m → a < ℓ → ∀ i < m,
      (G.Adj (c j a) (h i) ↔ (p * j + (a + 1) + 1 = p * i ∨ p * i + 1 = p * j + (a + 1))) := by
    intro j a hj ha i hi
    rw [(hhc j hj a ha i hi).1]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, ha'⟩)
      · right; ring
      · left; rw [mul_add, mul_one, hpdef]; omega
    · rintro (e | e)
      · right
        by_cases hlast : a + 1 = ℓ
        · refine ⟨?_, hlast⟩
          have e' : p * (j + 1) = p * i := by rw [mul_add, mul_one]; omega
          have := Nat.eq_of_mul_eq_mul_left (by omega) e'
          omega
        · have := decode (p := p) (a := a + 2) (b := 0) (by omega) (by omega)
            (by rw [add_zero]; omega)
          omega
      · left
        have := decode (p := p) (a := 1) (b := a + 1) (by omega) (by omega) e
        omega
  -- connector / connector
  have cc : ∀ i a, i + 1 < m → a < ℓ → ∀ j b, j + 1 < m → b < ℓ →
      (G.Adj (c i a) (c j b) ↔
        (p * i + (a + 1) + 1 = p * j + (b + 1) ∨ p * j + (b + 1) + 1 = p * i + (a + 1))) := by
    intro i a hi ha j b hj hb
    by_cases hij : i = j
    · subst hij
      rw [(hseg i hi a ha b hb).1]
      omega
    · have hn := (hcross i hi j hj hij a ha b hb).1
      simp only [hn, false_iff]
      rintro (e | e)
      · by_cases hlast : a + 1 = ℓ
        · have := decode (p := p) (a := 0) (b := b + 1) (by omega) (by omega)
            (show p * (i + 1) + 0 = p * j + (b + 1) by rw [mul_add, mul_one]; omega)
          omega
        · have := decode (p := p) (a := a + 2) (b := b + 1) (by omega) (by omega)
            (by omega)
          exact hij this.1
      · by_cases hlast : b + 1 = ℓ
        · have := decode (p := p) (a := 0) (b := a + 1) (by omega) (by omega)
            (show p * (j + 1) + 0 = p * i + (a + 1) by rw [mul_add, mul_one]; omega)
          omega
        · have := decode (p := p) (a := b + 2) (b := a + 1) (by omega) (by omega)
            (by omega)
          exact hij this.1.symm
  refine ⟨?_, ?_⟩
  · intro s hs t ht e
    rcases chainSeq_view ℓ m h c hm hs with ⟨i, hi, rfl, es⟩ | ⟨i, a, hi, ha, rfl, es⟩ <;>
    rcases chainSeq_view ℓ m h c hm ht with ⟨j, hj, rfl, et⟩ | ⟨j, b, hj, hb, rfl, et⟩ <;>
    rw [es, et] at e
    · by_cases hij : i = j
      · rw [hij]
      · exact absurd e (hH i hi j hj hij).2
    · exact absurd e.symm (hhc j hj b hb i hi).2
    · exact absurd e (hhc i hi a ha j hj).2
    · by_cases hij : i = j
      · subst hij; rw [(hseg i hi a ha b hb).2 e]
      · exact absurd e (hcross i hi j hj hij a ha b hb).2
  · intro s hs t ht
    rcases chainSeq_view ℓ m h c hm hs with ⟨i, hi, rfl, es⟩ | ⟨i, a, hi, ha, rfl, es⟩ <;>
    rcases chainSeq_view ℓ m h c hm ht with ⟨j, hj, rfl, et⟩ | ⟨j, b, hj, hb, rfl, et⟩ <;>
    rw [es, et]
    · exact hh i hi j hj
    · rw [G.adj_comm, ch j b hj hb i hi]; tauto
    · exact ch i a hi ha j hj
    · exact cc i a hi ha j b hj hb

/-- **Every 13 consecutive chain vertices form an induced `P13`** once the chain has at least
13 vertices. -/
theorem chain_P13 (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) (hlen : 12 ≤ (ℓ + 1) * (m - 1))
    (h : ℕ → V) (c : ℕ → ℕ → V)
    (hH : ∀ i < m, ∀ j < m, i ≠ j → ¬ G.Adj (h i) (h j) ∧ h i ≠ h j)
    (hseg : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ b < ℓ,
      (G.Adj (c i a) (c i b) ↔ (a + 1 = b ∨ b + 1 = a)) ∧ (c i a = c i b → a = b))
    (hhc : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ j < m,
      (G.Adj (c i a) (h j) ↔ ((j = i ∧ a = 0) ∨ (j = i + 1 ∧ a + 1 = ℓ))) ∧ c i a ≠ h j)
    (hcross : ∀ i, i + 1 < m → ∀ j, j + 1 < m → i ≠ j → ∀ a < ℓ, ∀ b < ℓ,
      ¬ G.Adj (c i a) (c j b) ∧ c i a ≠ c j b) :
    InducedSeq G 12 (chainSeq ℓ h c) := by
  have hi := chain_induced G ℓ m hℓ hm h c hH hseg hhc hcross
  exact ⟨fun a ha b hb e => hi.1 a (by omega) b (by omega) e,
    fun a ha b hb => hi.2 a (by omega) b (by omega)⟩

end Hypostructure.Graph.HubLink
