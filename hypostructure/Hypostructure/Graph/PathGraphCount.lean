import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The degree sum of a path

Mathlib fixes `SimpleGraph.pathGraph n` and its adjacency but records neither
its edge count nor its degree sum.  Both are needed to spend the internal
degree mass of a packed window: an induced copy of the window on `order`
vertices has `order − 1` internal edges, so `2(order − 1)` of the degree mass
carried by its vertices never leaves it.

A vertex of the path is adjacent exactly to its successor, when it has one, and
to its predecessor, when it has one.  Each indicator misses exactly one
endpoint, so the two families contribute `n − 1` apiece.

Nothing here is specific to any manuscript.
-/

namespace Hypostructure.Graph

open SimpleGraph
open scoped BigOperators

/-- The path's adjacency is a decidable arithmetic condition. -/
instance pathGraphDecidableAdj (n : Nat) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-- A vertex of `Fin n` is determined by its value, so a value equation cuts out
one vertex when the value is in range and none otherwise. -/
private theorem card_filter_val_eq (n value : Nat) :
    (Finset.univ.filter (fun index : Fin n => (index : ℕ) = value)).card =
      if value < n then 1 else 0 := by
  classical
  by_cases inRange : value < n
  · rw [if_pos inRange]
    refine Finset.card_eq_one.mpr ⟨⟨value, inRange⟩, ?_⟩
    ext index
    simp [Fin.ext_iff]
  · rw [if_neg inRange]
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
    intro index _
    have := index.isLt
    omega

/-- **The degree of a path vertex.**  One for the successor when it exists, one
for the predecessor when it exists. -/
theorem degree_pathGraph {n : Nat} (index : Fin n) :
    (pathGraph n).degree index =
      (if (index : ℕ) + 1 < n then 1 else 0) +
        (if 0 < (index : ℕ) then 1 else 0) := by
  classical
  have neighbours :
      (pathGraph n).neighborFinset index =
        (Finset.univ.filter (fun other : Fin n => (other : ℕ) = (index : ℕ) + 1))
          ∪ Finset.univ.filter
            (fun other : Fin n => (other : ℕ) + 1 = (index : ℕ)) := by
    ext other
    simp only [mem_neighborFinset, pathGraph_adj, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (forward | backward)
      · exact Or.inl forward.symm
      · exact Or.inr backward
    · rintro (forward | backward)
      · exact Or.inl forward.symm
      · exact Or.inr backward
  have disjointSides :
      Disjoint
        (Finset.univ.filter (fun other : Fin n => (other : ℕ) = (index : ℕ) + 1))
        (Finset.univ.filter
          (fun other : Fin n => (other : ℕ) + 1 = (index : ℕ))) := by
    refine Finset.disjoint_left.mpr fun other left right => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at left right
    omega
  have backwardCard :
      (Finset.univ.filter
          (fun other : Fin n => (other : ℕ) + 1 = (index : ℕ))).card =
        if 0 < (index : ℕ) then 1 else 0 := by
    rcases Nat.eq_zero_or_pos (index : ℕ) with zero | positive
    · rw [if_neg (by omega)]
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
      intro other _
      omega
    · rw [if_pos positive]
      have rewritten :
          (Finset.univ.filter
              (fun other : Fin n => (other : ℕ) + 1 = (index : ℕ))) =
            Finset.univ.filter
              (fun other : Fin n => (other : ℕ) = (index : ℕ) - 1) := by
        apply Finset.filter_congr
        intro other _
        constructor <;> intro h <;> omega
      rw [rewritten, card_filter_val_eq, if_pos (by omega : (index : ℕ) - 1 < n)]
  show ((pathGraph n).neighborFinset index).card = _
  rw [neighbours, Finset.card_union_of_disjoint disjointSides,
    card_filter_val_eq, backwardCard]

private theorem card_filter_succ_lt (m : Nat) :
    (Finset.univ.filter
      (fun index : Fin (m + 1) => (index : ℕ) + 1 < m + 1)).card = m := by
  classical
  have rewritten :
      (Finset.univ.filter (fun index : Fin (m + 1) => (index : ℕ) + 1 < m + 1)) =
        Finset.univ.erase (Fin.last m) := by
    ext index
    have bound := index.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true,
      Finset.mem_erase, ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  rw [rewritten, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

private theorem card_filter_pos (m : Nat) :
    (Finset.univ.filter (fun index : Fin (m + 1) => 0 < (index : ℕ))).card = m := by
  classical
  have rewritten :
      (Finset.univ.filter (fun index : Fin (m + 1) => 0 < (index : ℕ))) =
        Finset.univ.erase (0 : Fin (m + 1)) := by
    ext index
    have bound := index.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true,
      Finset.mem_erase, ne_eq, Fin.ext_iff, Fin.val_zero]
    omega
  rw [rewritten, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- **The degree sum of a path is `2(n − 1)`.** -/
theorem sum_degree_pathGraph (n : Nat) :
    ∑ index : Fin n, (pathGraph n).degree index = 2 * (n - 1) := by
  classical
  cases n with
  | zero => simp
  | succ m =>
      have expand : ∑ index : Fin (m + 1), (pathGraph (m + 1)).degree index =
          (∑ index : Fin (m + 1),
              if (index : ℕ) + 1 < m + 1 then 1 else 0) +
            ∑ index : Fin (m + 1), if 0 < (index : ℕ) then 1 else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun index _ => degree_pathGraph index
      rw [expand, ← Finset.card_filter, ← Finset.card_filter,
        card_filter_succ_lt, card_filter_pos]
      omega

end Hypostructure.Graph
