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

end Hypostructure.Graph.LayeredFactorization
