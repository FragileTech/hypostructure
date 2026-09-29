import Mathlib

/-!
# The exposure step under independence: an exact reduction to a local share test

Generic and vocabulary-free.  Suppose the labelled `(n,m)` class splits, layer by layer of the
number `i` of edges in a region `R`, as configurations `x ∈ X i` of `R` times configurations
`y ∈ Y i` of everything else (the fixed edge count `m` couples the two factors only through the
layer `i`), that the earlier data (outside record and earlier barrier states) depend on `y`
only (`e i y`), and that the state at the coordinate depends on `x` only (`s i x`).  The reached
class of `lem:blocked-graphs-compress` before the coordinate is then the set of triples with
`e i y` realized by a blocked member, and through the coordinate the set of triples whose pair
`(e i y, s i x)` is realized.

`aggregate_of_local_share`: if in every layer the fraction of `R`-configurations with a
surviving state is at most `F/W`, the aggregate test `W·A_{k+1} ≤ F·A_k` holds.  There is no
binomial approximation: the coupling by `m` is exactly the layering.

`local_share_not_forced`: independence alone does not give the aggregate; the local share test
is a separate hypothesis (a non-uniform distribution of configurations over states violates it).
-/

namespace Hypostructure.Graph.LayeredFactorization

open scoped BigOperators
open Classical

/-- The number of triples `(i, x, y)` whose pair `(e i y, s i x)` is in `realized`. -/
noncomputable def reachedThrough {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {E S : Type}
    (e : ∀ i, Y i → E) (s : ∀ i, X i → S) (realized : Set (E × S)) : Nat :=
  ∑ i, ∑ y : Y i, ∑ x : X i, if (e i y, s i x) ∈ realized then 1 else 0

/-- The number of triples `(i, x, y)` whose earlier data `e i y` is in `earlier`. -/
noncomputable def reachedBefore {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {E : Type}
    (e : ∀ i, Y i → E) (earlier : Set E) : Nat :=
  ∑ i, ∑ y : Y i, ∑ _x : X i, if e i y ∈ earlier then 1 else 0

/-- **Reduction of the aggregate test to a local share test.** -/
theorem aggregate_of_local_share {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {E S : Type}
    (e : ∀ i, Y i → E) (s : ∀ i, X i → S)
    (earlier : Set E) (surviving : Set S) (realized : Set (E × S))
    (realized_earlier : ∀ p ∈ realized, p.1 ∈ earlier)
    (realized_surviving : ∀ p ∈ realized, p.2 ∈ surviving)
    (F W : Nat)
    (localShare : ∀ i, W * (Finset.univ.filter fun x : X i => s i x ∈ surviving).card ≤
      F * Fintype.card (X i)) :
    W * reachedThrough e s realized ≤ F * reachedBefore (X := X) e earlier := by
  unfold reachedThrough reachedBefore
  have pointwise : ∀ i (y : Y i),
      W * (∑ x : X i, if (e i y, s i x) ∈ realized then 1 else 0) ≤
        F * (∑ _x : X i, if e i y ∈ earlier then 1 else 0) := by
    intro i y
    by_cases inEarlier : e i y ∈ earlier
    · have le : (∑ x : X i, if (e i y, s i x) ∈ realized then 1 else 0) ≤
          (Finset.univ.filter fun x : X i => s i x ∈ surviving).card := by
        rw [Finset.card_filter]
        refine Finset.sum_le_sum fun x _ ↦ ?_
        by_cases mem : (e i y, s i x) ∈ realized
        · simp [mem, realized_surviving _ mem]
        · simp [mem]
      calc W * (∑ x : X i, if (e i y, s i x) ∈ realized then 1 else 0)
          ≤ W * (Finset.univ.filter fun x : X i => s i x ∈ surviving).card :=
            Nat.mul_le_mul_left _ le
        _ ≤ F * Fintype.card (X i) := localShare i
        _ = F * (∑ _x : X i, if e i y ∈ earlier then 1 else 0) := by simp [inEarlier]
    · have zero : (∑ x : X i, if (e i y, s i x) ∈ realized then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun x _ ↦ ?_
        have : (e i y, s i x) ∉ realized := fun mem ↦ inEarlier (realized_earlier _ mem)
        simp [this]
      simp [zero]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun y _ ↦ pointwise i y

/-- **Independence alone does not give the aggregate test.**  One layer, one `y`; three
`R`-configurations, two of them in the surviving state (`W = 2`, `F = 1`, so the local share is
`2/3 > F/W = 1/2`): `W·A_{k+1} = 4 > 3 = F·A_k`. -/
theorem local_share_not_forced :
    ∃ (e : Unit → Unit → Unit) (s : Unit → Fin 3 → Bool)
      (earlier : Set Unit) (realized : Set (Unit × Bool)),
      2 * reachedThrough (X := fun _ : Unit ↦ Fin 3) (Y := fun _ : Unit ↦ Unit) e s realized >
        1 * reachedBefore (X := fun _ : Unit ↦ Fin 3) (Y := fun _ : Unit ↦ Unit) e earlier := by
  refine ⟨fun _ _ ↦ (), fun _ x ↦ decide (x.1 < 2), Set.univ, {((), true)}, ?_⟩
  unfold reachedThrough reachedBefore
  simp
  decide


/-- **A failed local share test is a repetition.**  If a layer has more surviving
configurations than the share `F/W` allows, and at most `F + 1` states survive, then some
surviving state `t` is shared by many configurations:
`F·|X| < W·(F+1)·#{x : s x = t}`; and once the surviving configurations outnumber `F + 1`, two
distinct configurations share a surviving state. -/
theorem repetition_of_failed_share {X S : Type} [Fintype X] (s : X → S)
    (survStates : Finset S) (F W : Nat) (hcard : survStates.card ≤ F + 1)
    (failed : F * Fintype.card X <
      W * (Finset.univ.filter fun x : X ↦ s x ∈ survStates).card) :
    ∃ t ∈ survStates,
      F * Fintype.card X < W * ((F + 1) * (Finset.univ.filter fun x : X ↦ s x = t).card) ∧
      ((F + 1) < (Finset.univ.filter fun x : X ↦ s x ∈ survStates).card →
        ∃ x x' : X, x ≠ x' ∧ s x = s x') := by
  classical
  set survivors := Finset.univ.filter fun x : X ↦ s x ∈ survStates with hsurv
  have positive : 0 < survivors.card := by
    by_contra zero
    have : survivors.card = 0 := Nat.eq_zero_of_not_pos zero
    rw [this, Nat.mul_zero] at failed
    exact Nat.not_lt_zero _ failed
  obtain ⟨witness, witnessMem⟩ := Finset.card_pos.1 positive
  have statesNonempty : survStates.Nonempty :=
    ⟨s witness, (Finset.mem_filter.1 witnessMem).2⟩
  have maps : ∀ x ∈ survivors, s x ∈ survStates := fun x mem ↦ (Finset.mem_filter.1 mem).2
  let fibre : S → Nat := fun t ↦ (survivors.filter fun x ↦ s x = t).card
  obtain ⟨best, bestMem, bestMax⟩ := Finset.exists_max_image survStates fibre statesNonempty
  have partition : survivors.card = ∑ t ∈ survStates, fibre t :=
    Finset.card_eq_sum_card_fiberwise maps
  have sumLe : ∑ t ∈ survStates, fibre t ≤ survStates.card * fibre best := by
    have := Finset.sum_le_card_nsmul survStates fibre (fibre best) bestMax
    simpa [smul_eq_mul] using this
  have survivorsLe : survivors.card ≤ (F + 1) * fibre best :=
    partition.le.trans (sumLe.trans (Nat.mul_le_mul_right _ hcard))
  have fibreEq : fibre best = (Finset.univ.filter fun x : X ↦ s x = best).card := by
    have same : survivors.filter (fun x ↦ s x = best) =
        Finset.univ.filter fun x : X ↦ s x = best := by
      ext x
      simp only [hsurv, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · intro h
        exact ⟨h ▸ bestMem, h⟩
    exact congrArg Finset.card same
  refine ⟨best, bestMem, ?_, ?_⟩
  · rw [← fibreEq]
    exact failed.trans_le (Nat.mul_le_mul_left _ survivorsLe)
  · intro many
    obtain ⟨x, _, x', _, differ, same⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := survivors) (t := survStates)
        (f := s) (lt_of_le_of_lt hcard many) maps
    exact ⟨x, x', differ, same⟩

end Hypostructure.Graph.LayeredFactorization
