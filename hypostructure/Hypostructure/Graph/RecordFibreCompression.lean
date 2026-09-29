import Mathlib

/-!
# Record fibres bound every exposure compression (generic; `[170]`, `[171]`, `[172a]`)

Generic and vocabulary-free.  A finite a-priori class `α` carries a *record* `record : α → ρ`
(the outside edges of `lem:blocked-graphs-compress`) and a sequence of *states*
`state : α → ℕ → σ` (the barrier states in exposure order).  For a finite subclass `B`
(the blocked class) the reached sets are

  `A_k = {x | ∃ b ∈ B, record x = record b ∧ ∀ i < k, state x i = state b i}`,

exactly the sets of the proof of `lem:blocked-graphs-compress`.

* `telescope`: the aggregate tests `W_k·|A_{k+1}| ≤ F_k·|A_k|` (`k < N`) give
  `|A_N|·∏W ≤ |A_0|·∏F` -- the product step of `[171]`.
* `card_reached_zero_le`: if every record fibre over a record of `B` has at most `K` members,
  `|A_0| ≤ K·|B|`.
* `chain_iff_empty`: when `K·∏F < ∏W`, the aggregate tests all hold **iff `B = ∅`**.  The
  positive arm of `[170]` is then a restatement of emptiness of the class, whatever further
  properties (bridgeless, connected, globally target-free) the class imposes.
* `first_failure_of_nonempty`: under the same gap, a nonempty class has a first failing
  aggregate test with all earlier tests holding.  It names no member.
* `card_fibre_le_choose`: the fibre of the record "`E \ inside`" among `m`-sets has at most
  `C(|inside|, m - |d|)` members -- the record fixes everything except `E ∩ inside`.
* `card_group_le_card_mul_card_stabilizer`: an invariant finite set containing `x` has at least
  `|Γ| / |Stab x|` members (orbit lower bound; the relabelling count of a class closed under
  permutations fixing the windows pointwise).
-/

namespace Hypostructure.Graph.RecordFibreCompression

open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## The telescoping product step of `[171]` -/

/-- **The product step.**  Aggregate tests at `k < N` give `A_N·∏W ≤ A_0·∏F`. -/
theorem telescope (A W F : ℕ → ℕ) :
    ∀ N : ℕ, (∀ k < N, W k * A (k + 1) ≤ F k * A k) →
      A N * ∏ k ∈ Finset.range N, W k ≤ A 0 * ∏ k ∈ Finset.range N, F k
  | 0, _ => by simp
  | N + 1, h => by
    have ih := telescope A W F N fun k hk => h k (Nat.lt_succ_of_lt hk)
    have step := h N (Nat.lt_succ_self N)
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc A (N + 1) * ((∏ k ∈ Finset.range N, W k) * W N)
        = (W N * A (N + 1)) * ∏ k ∈ Finset.range N, W k := by ring
      _ ≤ (F N * A N) * ∏ k ∈ Finset.range N, W k := Nat.mul_le_mul_right _ step
      _ = F N * (A N * ∏ k ∈ Finset.range N, W k) := by ring
      _ ≤ F N * (A 0 * ∏ k ∈ Finset.range N, F k) := Nat.mul_le_mul_left _ ih
      _ = A 0 * ((∏ k ∈ Finset.range N, F k) * F N) := by ring

/-! ## Reached sets -/

variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [DecidableEq ρ] [DecidableEq σ]

/-- The reached set `A_k`: a-priori members whose record and first `k` states agree with those
of one member of `B`. -/
def reached (record : α → ρ) (state : α → ℕ → σ) (B : Finset α) (k : ℕ) : Finset α :=
  Finset.univ.filter fun x => ∃ b ∈ B, record x = record b ∧ ∀ i < k, state x i = state b i

theorem subset_reached (record : α → ρ) (state : α → ℕ → σ) (B : Finset α) (k : ℕ) :
    B ⊆ reached record state B k := by
  intro b hb
  simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b, hb, rfl, fun _ _ => rfl⟩

theorem reached_succ_subset (record : α → ρ) (state : α → ℕ → σ) (B : Finset α) (k : ℕ) :
    reached record state B (k + 1) ⊆ reached record state B k := by
  intro x hx
  simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨b, hb, hr, hs⟩ := hx
  exact ⟨b, hb, hr, fun i hi => hs i (Nat.lt_succ_of_lt hi)⟩

theorem reached_empty (record : α → ρ) (state : α → ℕ → σ) (k : ℕ) :
    reached record state (∅ : Finset α) k = ∅ := by
  ext x
  simp [reached]

/-- **Record-fibre bound.**  If each record fibre over a record of `B` has at most `K`
members, then `|A_0| ≤ K·|B|`. -/
theorem card_reached_zero_le (record : α → ρ) (state : α → ℕ → σ) (B : Finset α) (K : ℕ)
    (hK : ∀ b ∈ B, (Finset.univ.filter fun x => record x = record b).card ≤ K) :
    (reached record state B 0).card ≤ K * B.card := by
  have sub : reached record state B 0 ⊆
      B.biUnion fun b => Finset.univ.filter fun x => record x = record b := by
    intro x hx
    simp only [reached, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨b, hb, hr, _⟩ := hx
    exact Finset.mem_biUnion.2 ⟨b, hb, by simp [hr]⟩
  calc (reached record state B 0).card
      ≤ (B.biUnion fun b => Finset.univ.filter fun x => record x = record b).card :=
        Finset.card_le_card sub
    _ ≤ ∑ b ∈ B, (Finset.univ.filter fun x => record x = record b).card :=
        Finset.card_biUnion_le
    _ ≤ B.card * K := by
        simpa [smul_eq_mul] using Finset.sum_le_card_nsmul B _ K hK
    _ = K * B.card := Nat.mul_comm _ _

/-- The aggregate test at coordinate `k`. -/
def AggregateTest (record : α → ρ) (state : α → ℕ → σ) (B : Finset α) (W F : ℕ → ℕ)
    (k : ℕ) : Prop :=
  W k * (reached record state B (k + 1)).card ≤ F k * (reached record state B k).card

/-- **Compression of the class from the aggregate tests** (the `[171]` inequality, with the
record-fibre bound in place of the ambient class). -/
theorem class_compression (record : α → ρ) (state : α → ℕ → σ) (B : Finset α)
    (W F : ℕ → ℕ) (N K : ℕ)
    (hK : ∀ b ∈ B, (Finset.univ.filter fun x => record x = record b).card ≤ K)
    (chain : ∀ k < N, AggregateTest record state B W F k) :
    B.card * ∏ k ∈ Finset.range N, W k ≤ (K * B.card) * ∏ k ∈ Finset.range N, F k := by
  have tele := telescope (fun k => (reached record state B k).card) W F N chain
  calc B.card * ∏ k ∈ Finset.range N, W k
      ≤ (reached record state B N).card * ∏ k ∈ Finset.range N, W k :=
        Nat.mul_le_mul_right _ (Finset.card_le_card (subset_reached record state B N))
    _ ≤ (reached record state B 0).card * ∏ k ∈ Finset.range N, F k := tele
    _ ≤ (K * B.card) * ∏ k ∈ Finset.range N, F k :=
        Nat.mul_le_mul_right _ (card_reached_zero_le record state B K hK)

/-- **The positive arm is emptiness.**  If the record fibres have at most `K` members and
`K·∏F < ∏W`, then all aggregate tests hold iff the class is empty. -/
theorem chain_iff_empty (record : α → ρ) (state : α → ℕ → σ) (B : Finset α)
    (W F : ℕ → ℕ) (N K : ℕ)
    (hK : ∀ b ∈ B, (Finset.univ.filter fun x => record x = record b).card ≤ K)
    (gap : K * ∏ k ∈ Finset.range N, F k < ∏ k ∈ Finset.range N, W k) :
    (∀ k < N, AggregateTest record state B W F k) ↔ B = ∅ := by
  constructor
  · intro chain
    by_contra hne
    have pos : 0 < B.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne)
    have comp := class_compression record state B W F N K hK chain
    have : B.card * ∏ k ∈ Finset.range N, W k ≤
        B.card * (K * ∏ k ∈ Finset.range N, F k) := by
      calc B.card * ∏ k ∈ Finset.range N, W k
          ≤ (K * B.card) * ∏ k ∈ Finset.range N, F k := comp
        _ = B.card * (K * ∏ k ∈ Finset.range N, F k) := by ring
    exact absurd (Nat.le_of_mul_le_mul_left this pos) (Nat.not_le.2 gap)
  · rintro rfl k _
    simp [AggregateTest, reached_empty]

/-- **First aggregate failure of a nonempty class.**  Under the record-fibre gap, a nonempty
class has a first coordinate `k < N` whose aggregate test fails, all earlier tests holding. -/
theorem first_failure_of_nonempty (record : α → ρ) (state : α → ℕ → σ) (B : Finset α)
    (W F : ℕ → ℕ) (N K : ℕ)
    (hK : ∀ b ∈ B, (Finset.univ.filter fun x => record x = record b).card ≤ K)
    (gap : K * ∏ k ∈ Finset.range N, F k < ∏ k ∈ Finset.range N, W k)
    (nonempty : B.Nonempty) :
    ∃ k < N, (∀ i < k, AggregateTest record state B W F i) ∧
      F k * (reached record state B k).card <
        W k * (reached record state B (k + 1)).card := by
  classical
  have notAll : ¬ ∀ k < N, AggregateTest record state B W F k := fun chain =>
    (Finset.nonempty_iff_ne_empty.1 nonempty)
      ((chain_iff_empty record state B W F N K hK gap).1 chain)
  have ex : ∃ k, k < N ∧ ¬ AggregateTest record state B W F k := by
    by_contra hno
    exact notAll fun k hk => by
      by_contra h
      exact hno ⟨k, hk, h⟩
  refine ⟨Nat.find ex, (Nat.find_spec ex).1, ?_, ?_⟩
  · intro i hi
    by_contra hfail
    exact Nat.find_min ex hi ⟨lt_trans hi (Nat.find_spec ex).1, hfail⟩
  · exact Nat.lt_of_not_le (Nat.find_spec ex).2

/-! ## The fibre of an "outside edges" record -/

/-- **Record fibre of `E ↦ E \ inside`.**  Among the `m`-sets of a family, those with
`E \ inside = d` number at most `C(|inside|, m - |d|)`. -/
theorem card_fibre_le_choose {β : Type*} [DecidableEq β] (family : Finset (Finset β))
    (inside d : Finset β) (m : ℕ) :
    (family.filter fun E => E.card = m ∧ E \ inside = d).card ≤
      inside.card.choose (m - d.card) := by
  rw [← Finset.card_powersetCard]
  refine Finset.card_le_card_of_injOn (fun E => E ∩ inside) ?_ ?_
  · intro E hE
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hE
    obtain ⟨_, hcard, hd⟩ := hE
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.inter_subset_right, ?_⟩
    have split := Finset.card_sdiff_add_card_inter E inside
    rw [hd, hcard] at split
    omega
  · intro E hE E' hE' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hE hE'
    have h1 : E = (E \ inside) ∪ (E ∩ inside) := (Finset.sdiff_union_inter E inside).symm
    have h2 : E' = (E' \ inside) ∪ (E' ∩ inside) := (Finset.sdiff_union_inter E' inside).symm
    have heq' : E ∩ inside = E' ∩ inside := heq
    rw [h1, h2, hE.2.2, hE'.2.2, heq']

/-! ## Orbit lower bound -/

/-- **Orbit lower bound.**  A finite set invariant under a finite group and containing `x`
has at least `|Γ|/|Stab x|` members: `|Γ| ≤ |C|·|Stab x|`. -/
theorem card_group_le_card_mul_card_stabilizer {Γ β : Type*} [Group Γ] [MulAction Γ β]
    [Finite Γ] (C : Finset β) (invariant : ∀ g : Γ, ∀ y ∈ C, g • y ∈ C) (x : β)
    (hx : x ∈ C) :
    Nat.card Γ ≤ C.card * Nat.card (MulAction.stabilizer Γ x) := by
  have orbitSub : MulAction.orbit Γ x ⊆ (C : Set β) := by
    rintro _ ⟨g, rfl⟩
    exact invariant g x hx
  have orbitLe : Nat.card (MulAction.orbit Γ x) ≤ C.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset C]
    exact Set.ncard_le_ncard orbitSub (Finset.finite_toSet C)
  have key : Nat.card (MulAction.stabilizer Γ x) * (MulAction.stabilizer Γ x).index =
      Nat.card Γ := Subgroup.card_mul_index _
  rw [MulAction.index_stabilizer] at key
  rw [← key, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ orbitLe

end Hypostructure.Graph.RecordFibreCompression
