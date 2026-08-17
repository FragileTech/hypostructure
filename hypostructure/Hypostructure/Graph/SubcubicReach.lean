import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The subcubic ball count

`lem:cold-germ-extraction`: *"In a subcubic graph the ball of radius `r` around
a vertex has at most `1 + 3(2^r − 1)` vertices."*  Stated for paths whose
interior vertices lie in a set of vertices of degree at most three, which is
how the manuscript uses it: the paths of a first-failure exchange run through
the ambient-cubic part.
-/

namespace Hypostructure.Graph.SubcubicReach

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- The vertices reachable from `x` by a path of length at most `j` whose
interior vertices (all but the last) lie in `S` and whose first step avoids
`a`. -/
noncomputable def reach (S : Finset V) (x : V) (j : Nat) (a : V) : Finset V := by
  classical
  exact univ.filter fun w =>
    ∃ p : G.Walk x w, p.IsPath ∧ p.length ≤ j ∧
      (∀ z ∈ p.support.dropLast, z ∈ S) ∧ (∀ hp : ¬ p.Nil, p.getVert 1 ≠ a)

theorem mem_reach {S : Finset V} {x : V} {j : Nat} {a w : V} :
    w ∈ reach G S x j a ↔
      ∃ p : G.Walk x w, p.IsPath ∧ p.length ≤ j ∧
        (∀ z ∈ p.support.dropLast, z ∈ S) ∧ (∀ hp : ¬ p.Nil, p.getVert 1 ≠ a) := by
  classical
  simp [reach]

/-- One step of the recursion: a path of length `≤ j+1` from `x` avoiding `a` is
`x` itself or a step to a neighbour `y ≠ a` followed by a path of length `≤ j`
from `y` avoiding `x`; and if `x ∉ S` only the trivial path qualifies. -/
theorem reach_subset (S : Finset V) (x : V) (j : Nat) (a : V) :
    reach G S x (j + 1) a ⊆
      insert x ((G.neighborFinset x).erase a |>.biUnion fun y => reach G S y j x) := by
  classical
  intro w member
  obtain ⟨p, isPath, lengthLe, interior, avoid⟩ := (mem_reach G).1 member
  cases p with
  | nil => exact mem_insert_self _ _
  | @cons _ y _ adjacent q =>
      refine mem_insert_of_mem (mem_biUnion.2 ⟨y, ?_, ?_⟩)
      · refine mem_erase.2 ⟨?_, (SimpleGraph.mem_neighborFinset G x y).2 adjacent⟩
        have := avoid (by simp)
        simpa using this
      · refine (mem_reach G).2 ⟨q, ?_, ?_, ?_, ?_⟩
        · exact (SimpleGraph.Walk.cons_isPath_iff adjacent q).1 isPath |>.1
        · simpa using lengthLe
        · intro z zMem
          apply interior
          simp only [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
            (SimpleGraph.Walk.support_ne_nil q), List.mem_cons]
          exact Or.inr zMem
        · intro hq
          intro same
          have xNot : x ∉ q.support :=
            ((SimpleGraph.Walk.cons_isPath_iff adjacent q).1 isPath).2
          apply xNot
          rw [← same]
          exact SimpleGraph.Walk.getVert_mem_support q 1

/-- The trivial reach when `x ∉ S`: no non-trivial good path starts at `x`. -/
theorem reach_subset_singleton_of_not_mem (S : Finset V) (x : V) (j : Nat) (a : V)
    (outside : x ∉ S) : reach G S x j a ⊆ {x} := by
  classical
  intro w member
  obtain ⟨p, _, _, interior, _⟩ := (mem_reach G).1 member
  cases p with
  | nil => exact mem_singleton_self _
  | @cons _ y _ adjacent q =>
      exact absurd (interior x (by
        simp [SimpleGraph.Walk.support_cons,
          List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil q)])) outside

/-- **The avoiding count**: from a vertex of degree at most three, avoiding one
neighbour, at most `2^(j+1) − 1` vertices are reached within `j` steps. -/
theorem card_reach_avoid_le (S : Finset V) (cubic : ∀ z ∈ S, G.degree z ≤ 3)
    (j : Nat) :
    ∀ (x a : V), G.Adj x a → (reach G S x j a).card ≤ 2 ^ (j + 1) - 1 := by
  classical
  induction j with
  | zero =>
      intro x a _
      calc (reach G S x 0 a).card ≤ ({x} : Finset V).card := by
            apply card_le_card
            intro w member
            obtain ⟨p, _, lengthLe, _, _⟩ := (mem_reach G).1 member
            have : p.length = 0 := Nat.le_zero.mp lengthLe
            rw [SimpleGraph.Walk.length_eq_zero_iff] at this
            have := this.eq
            subst this
            exact mem_singleton_self _
        _ = 2 ^ (0 + 1) - 1 := by simp
  | succ j ih =>
      intro x a adjacent
      by_cases inside : x ∈ S
      · have step := reach_subset G S x j a
        refine le_trans (card_le_card step) ?_
        refine le_trans (card_insert_le _ _) ?_
        refine le_trans (Nat.succ_le_succ (card_biUnion_le)) ?_
        have neighbours : ((G.neighborFinset x).erase a).card ≤ 2 := by
          have := card_erase_of_mem ((SimpleGraph.mem_neighborFinset G x a).2 adjacent)
          rw [this, SimpleGraph.card_neighborFinset_eq_degree]
          have := cubic x inside
          omega
        have each : ∀ y ∈ (G.neighborFinset x).erase a,
            (reach G S y j x).card ≤ 2 ^ (j + 1) - 1 := by
          intro y yMem
          exact ih y x ((SimpleGraph.mem_neighborFinset G x y).1 (mem_of_mem_erase yMem)).symm
        calc (∑ y ∈ (G.neighborFinset x).erase a, (reach G S y j x).card) + 1
            ≤ (∑ _y ∈ (G.neighborFinset x).erase a, (2 ^ (j + 1) - 1)) + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum each) 1
          _ = ((G.neighborFinset x).erase a).card * (2 ^ (j + 1) - 1) + 1 := by
              rw [sum_const, smul_eq_mul]
          _ ≤ 2 * (2 ^ (j + 1) - 1) + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul_right _ neighbours) 1
          _ ≤ 2 ^ (j + 1 + 1) - 1 := by
              have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
              rw [pow_succ]
              omega
      · refine le_trans (card_le_card (reach_subset_singleton_of_not_mem G S x _ a inside)) ?_
        simp only [card_singleton]
        have : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_two_pow
        omega

/-- **The subcubic ball**: from any vertex, at most `1 + 3(2^r − 1)` vertices are
reached by paths of length at most `r` whose interior lies in the subcubic set. -/
theorem card_reach_le (S : Finset V) (cubic : ∀ z ∈ S, G.degree z ≤ 3)
    (x : V) (r : Nat) :
    (reach G S x r x).card ≤ 1 + 3 * (2 ^ r - 1) := by
  classical
  cases r with
  | zero =>
      calc (reach G S x 0 x).card ≤ ({x} : Finset V).card := by
            apply card_le_card
            intro w member
            obtain ⟨p, _, lengthLe, _, _⟩ := (mem_reach G).1 member
            have : p.length = 0 := Nat.le_zero.mp lengthLe
            rw [SimpleGraph.Walk.length_eq_zero_iff] at this
            have := this.eq
            subst this
            exact mem_singleton_self _
        _ = 1 + 3 * (2 ^ 0 - 1) := by simp
  | succ r =>
      by_cases inside : x ∈ S
      · have step := reach_subset G S x r x
        refine le_trans (card_le_card step) ?_
        refine le_trans (card_insert_le _ _) ?_
        refine le_trans (Nat.succ_le_succ (card_biUnion_le)) ?_
        have neighbours : ((G.neighborFinset x).erase x).card ≤ 3 := by
          refine le_trans (card_erase_le) ?_
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact cubic x inside
        have each : ∀ y ∈ (G.neighborFinset x).erase x,
            (reach G S y r x).card ≤ 2 ^ (r + 1) - 1 := by
          intro y yMem
          exact card_reach_avoid_le G S cubic r y x
            ((SimpleGraph.mem_neighborFinset G x y).1 (mem_of_mem_erase yMem)).symm
        calc (∑ y ∈ (G.neighborFinset x).erase x, (reach G S y r x).card) + 1
            ≤ (∑ _y ∈ (G.neighborFinset x).erase x, (2 ^ (r + 1) - 1)) + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum each) 1
          _ = ((G.neighborFinset x).erase x).card * (2 ^ (r + 1) - 1) + 1 := by
              rw [sum_const, smul_eq_mul]
          _ ≤ 3 * (2 ^ (r + 1) - 1) + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul_right _ neighbours) 1
          _ = 1 + 3 * (2 ^ (r + 1) - 1) := by omega
      · refine le_trans (card_le_card (reach_subset_singleton_of_not_mem G S x _ x inside)) ?_
        simp only [card_singleton]
        omega

end Hypostructure.Graph.SubcubicReach
