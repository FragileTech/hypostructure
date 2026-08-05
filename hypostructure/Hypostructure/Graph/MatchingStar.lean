import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Matching--star accounting for a family of unordered pairs

`lem:same-token-matching-star`.  For a finite simple graph `H`,

  `e(H) ≤ ν(H)(2Δ(H) − 1)`,

and consequently, if `K ≥ 1` and `H` contains neither a matching of size `K`
nor a star of size `K`, then `e(H) ≤ (K−1)(2K−3)`.

The manuscript reads this at the token-fibre graphs `H_t` and the role-fibre
graphs `H_{t,r}`, whose vertices are active demands and whose edges are the
pairs charged to one token.  Nothing about that reading is used here: the
statement is about an arbitrary finite family of unordered pairs, and the
proof is the manuscript's own — a maximum matching covers every edge, the
degree sum over the covered vertices counts each matching edge twice and every
other edge at least once.

The two bounds are stated against *parameters* `ν` and `Δ` rather than against
defined extremal invariants.  A caller that has the extremal values passes
them; a caller that only knows "no `K`-matching, no `K`-star" -- which is
exactly the hypothesis shape of `cor:homogeneous-same-token-caps-close` and
`cor:same-token-pattern-caps-close` -- passes `K − 1` for both and gets the
manuscript's second display.  No maximum is computed and none is needed.
-/

namespace Hypostructure.Graph.PatternFamily

open scoped BigOperators

universe u

variable {V : Type u} [DecidableEq V]

/-- **The degree of a vertex in a pattern family**: the pairs of the family
that contain it.  A star of size `K` centred at a vertex is exactly `K` such
pairs, so this number *is* the largest star at the vertex. -/
def degree (family : Finset (Sym2 V)) (vertex : V) : Nat :=
  (family.filter fun edge => vertex ∈ edge).card

/-- **The vertices a family covers.** -/
def support (family : Finset (Sym2 V)) : Finset V :=
  family.biUnion Sym2.toFinset

/-- **A matching**: distinct members of the family share no vertex. -/
def IsMatching (family : Finset (Sym2 V)) : Prop :=
  ∀ edge ∈ family, ∀ other ∈ family, edge ≠ other →
    ∀ vertex : V, vertex ∈ edge → vertex ∉ other

/-- **A star with a given centre**: every member of the family contains it. -/
def IsStar (family : Finset (Sym2 V)) (centre : V) : Prop :=
  ∀ edge ∈ family, centre ∈ edge

theorem mem_support {family : Finset (Sym2 V)} {vertex : V} :
    vertex ∈ support family ↔ ∃ edge ∈ family, vertex ∈ edge := by
  simp [support]

omit [DecidableEq V] in
/-- A subfamily of a matching is a matching. -/
theorem IsMatching.subset {family sub : Finset (Sym2 V)} (matching : IsMatching family)
    (inside : sub ⊆ family) : IsMatching sub :=
  fun edge edgeMem other otherMem distinct =>
    matching edge (inside edgeMem) other (inside otherMem) distinct

/-- A matching covers at most two vertices per member. -/
theorem card_support_le_two_mul (family : Finset (Sym2 V)) :
    (support family).card ≤ 2 * family.card := by
  classical
  calc (support family).card
      ≤ ∑ edge ∈ family, edge.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _edge ∈ family, 2 := by
        refine Finset.sum_le_sum fun edge _ => ?_
        rw [Sym2.card_toFinset]
        split <;> omega
    _ = 2 * family.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The incidence count, read along both indices.**  Summing the family
degree over a set of vertices is the same as summing, over the family, how many
of those vertices each member contains. -/
theorem sum_degree_eq_sum_card_filter (family : Finset (Sym2 V))
    (cover : Finset V) :
    ∑ vertex ∈ cover, degree family vertex =
      ∑ edge ∈ family, (cover.filter fun vertex => vertex ∈ edge).card := by
  classical
  calc ∑ vertex ∈ cover, degree family vertex
      = ∑ vertex ∈ cover, ∑ edge ∈ family, (if vertex ∈ edge then 1 else 0) :=
        Finset.sum_congr rfl fun vertex _ => by simp [degree]
    _ = ∑ edge ∈ family, ∑ vertex ∈ cover, (if vertex ∈ edge then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ edge ∈ family, (cover.filter fun vertex => vertex ∈ edge).card :=
        Finset.sum_congr rfl fun edge _ => by simp

/-- The arithmetic step of the accounting: `e + ν ≤ 2νΔ` gives
`e ≤ ν(2Δ − 1)`, with `Nat` truncation on the right handled at `Δ = 0`. -/
private theorem card_le_of_add_le (edges matching degreeBound : Nat)
    (counted : edges + matching ≤ 2 * matching * degreeBound) :
    edges ≤ matching * (2 * degreeBound - 1) := by
  match degreeBound with
  | 0 => omega
  | (k + 1) =>
    have expand : 2 * matching * (k + 1) = 2 * (matching * k) + 2 * matching := by ring
    have target : matching * (2 * (k + 1) - 1) = 2 * (matching * k) + matching := by
      have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [this]; ring
    omega

/-- **`lem:same-token-matching-star`, first display.**

  `e(H) ≤ ν(H)(2Δ(H) − 1)`,

stated against any pair of bounds `ν` and `Δ` the caller can supply: `ν` bounds
every matching inside the family and `Δ` bounds every vertex degree.

The proof is the manuscript's.  Choose a matching of maximum size; maximality
makes its covered vertices a vertex cover, so summing the family degree over
that cover counts every member at least once and every matching member exactly
twice, while the same sum is at most `|cover|·Δ ≤ 2ν·Δ`. -/
theorem card_le_matching_mul_two_mul_degree_sub_one
    (family : Finset (Sym2 V)) (matchingBound degreeBound : Nat)
    (nondiagonal : ∀ edge ∈ family, ¬ edge.IsDiag)
    (matchings : ∀ sub ⊆ family, IsMatching sub → sub.card ≤ matchingBound)
    (degrees : ∀ vertex : V, degree family vertex ≤ degreeBound) :
    family.card ≤ matchingBound * (2 * degreeBound - 1) := by
  classical
  -- A maximum-size matching inside the family.
  set candidates := family.powerset.filter fun sub => IsMatching sub with candidatesDef
  have emptyMem : (∅ : Finset (Sym2 V)) ∈ candidates := by
    simp [candidatesDef, IsMatching]
  obtain ⟨best, bestMem, bestMax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, emptyMem⟩
  have bestInside : best ⊆ family := by
    have := Finset.mem_filter.mp bestMem
    exact Finset.mem_powerset.mp this.1
  have bestMatching : IsMatching best := (Finset.mem_filter.mp bestMem).2
  -- Maximality: every member of the family meets the covered set.
  have covers : ∀ edge ∈ family, ∃ vertex ∈ support best, vertex ∈ edge := by
    intro edge edgeMem
    by_contra missing
    push_neg at missing
    have fresh : ∀ vertex : V, vertex ∈ edge → vertex ∉ support best := by
      intro vertex inEdge
      by_contra covered
      exact missing vertex covered inEdge
    have notMem : edge ∉ best := by
      intro inBest
      exact fresh _ (Sym2.out_fst_mem edge)
        (mem_support.mpr ⟨edge, inBest, Sym2.out_fst_mem edge⟩)
    have larger : insert edge best ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · exact Finset.insert_subset edgeMem bestInside
      · intro first firstMem second secondMem distinct vertex inFirst
        rcases Finset.mem_insert.mp firstMem with rfl | firstBest
        · rcases Finset.mem_insert.mp secondMem with rfl | secondBest
          · exact absurd rfl distinct
          · intro inSecond
            exact fresh vertex inFirst
              (mem_support.mpr ⟨second, secondBest, inSecond⟩)
        · rcases Finset.mem_insert.mp secondMem with rfl | secondBest
          · intro inSecond
            exact fresh vertex inSecond
              (mem_support.mpr ⟨first, firstBest, inFirst⟩)
          · exact bestMatching first firstBest second secondBest distinct vertex inFirst
    have := bestMax _ larger
    rw [Finset.card_insert_of_notMem notMem] at this
    omega
  -- Every member is counted once, every matching member twice.
  have lower : family.card + best.card ≤
      ∑ edge ∈ family, ((support best).filter fun vertex => vertex ∈ edge).card := by
    have pointwise : ∀ edge ∈ family,
        (1 + if edge ∈ best then 1 else 0) ≤
          ((support best).filter fun vertex => vertex ∈ edge).card := by
      intro edge edgeMem
      by_cases inBest : edge ∈ best
      · have equality :
            ((support best).filter fun vertex => vertex ∈ edge) = edge.toFinset := by
          ext vertex
          simp only [Finset.mem_filter, Sym2.mem_toFinset]
          exact ⟨fun both => both.2, fun inEdge =>
            ⟨mem_support.mpr ⟨edge, inBest, inEdge⟩, inEdge⟩⟩
        rw [equality, Sym2.card_toFinset_of_not_isDiag _ (nondiagonal edge edgeMem),
          if_pos inBest]
      · obtain ⟨vertex, covered, inEdge⟩ := covers edge edgeMem
        rw [if_neg inBest]
        have : vertex ∈ (support best).filter fun vertex => vertex ∈ edge :=
          Finset.mem_filter.mpr ⟨covered, inEdge⟩
        have := Finset.card_pos.mpr ⟨vertex, this⟩
        omega
    calc family.card + best.card
        = ∑ edge ∈ family, (1 + if edge ∈ best then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one,
            Finset.sum_ite_mem, Finset.inter_eq_right.mpr bestInside,
            Finset.sum_const, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum pointwise
  -- The same sum is at most the cover size times the degree bound.
  have upper : ∑ edge ∈ family,
      ((support best).filter fun vertex => vertex ∈ edge).card ≤
        2 * best.card * degreeBound := by
    rw [← sum_degree_eq_sum_card_filter]
    calc ∑ vertex ∈ support best, degree family vertex
        ≤ ∑ _vertex ∈ support best, degreeBound :=
          Finset.sum_le_sum fun vertex _ => degrees vertex
      _ = (support best).card * degreeBound := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 * best.card * degreeBound :=
          Nat.mul_le_mul_right _ (card_support_le_two_mul best)
  have counted : family.card + best.card ≤ 2 * best.card * degreeBound :=
    le_trans lower upper
  calc family.card
      ≤ best.card * (2 * degreeBound - 1) :=
        card_le_of_add_le _ _ _ counted
    _ ≤ matchingBound * (2 * degreeBound - 1) :=
        Nat.mul_le_mul_right _ (matchings best bestInside bestMatching)

/-- A star of size `K` at a vertex is exactly `K` members containing it, so the
family degree at that vertex decides whether one exists. -/
theorem exists_star_iff (family : Finset (Sym2 V)) (centre : V) (size : Nat) :
    (∃ sub ⊆ family, IsStar sub centre ∧ size ≤ sub.card) ↔
      size ≤ degree family centre := by
  classical
  constructor
  · rintro ⟨sub, inside, star, large⟩
    refine le_trans large (Finset.card_le_card ?_)
    intro edge edgeMem
    exact Finset.mem_filter.mpr ⟨inside edgeMem, star edge edgeMem⟩
  · intro large
    exact ⟨family.filter fun edge => centre ∈ edge, Finset.filter_subset _ _,
      fun edge edgeMem => (Finset.mem_filter.mp edgeMem).2, large⟩

/-- **`lem:same-token-matching-star`, second display.**

If `K ≥ 1` and the family contains neither a matching of size `K` nor a star of
size `K`, then it has at most `(K−1)(2K−3)` members.  This is the first display
at `ν = Δ = K − 1`. -/
theorem card_le_of_no_matching_no_star
    (family : Finset (Sym2 V)) (size : Nat) (positive : 1 ≤ size)
    (nondiagonal : ∀ edge ∈ family, ¬ edge.IsDiag)
    (noMatching : ¬ ∃ sub ⊆ family, IsMatching sub ∧ size ≤ sub.card)
    (noStar : ¬ ∃ centre : V, ∃ sub ⊆ family, IsStar sub centre ∧ size ≤ sub.card) :
    family.card ≤ (size - 1) * (2 * size - 3) := by
  have matchings : ∀ sub ⊆ family, IsMatching sub → sub.card ≤ size - 1 := by
    intro sub inside matching
    by_contra big
    exact noMatching ⟨sub, inside, matching, by omega⟩
  have degrees : ∀ vertex : V, degree family vertex ≤ size - 1 := by
    intro vertex
    by_contra big
    exact noStar ⟨vertex, ((exists_star_iff family vertex size).mpr (by omega))⟩
  have := card_le_matching_mul_two_mul_degree_sub_one family (size - 1) (size - 1)
    nondiagonal matchings degrees
  have rewrite : 2 * (size - 1) - 1 = 2 * size - 3 := by omega
  rwa [rewrite] at this

/-- **`lem:same-token-matching-star`, contrapositive.**  A family with more than
`(K−1)(2K−3)` members contains a matching of size `K` or a star of size `K`.
This is the form the geometric audits consume. -/
theorem exists_matching_or_star_of_lt_card
    (family : Finset (Sym2 V)) (size : Nat) (positive : 1 ≤ size)
    (nondiagonal : ∀ edge ∈ family, ¬ edge.IsDiag)
    (large : (size - 1) * (2 * size - 3) < family.card) :
    (∃ sub ⊆ family, IsMatching sub ∧ size ≤ sub.card) ∨
      (∃ centre : V, ∃ sub ⊆ family, IsStar sub centre ∧ size ≤ sub.card) := by
  by_contra none
  push_neg at none
  obtain ⟨noMatching, noStar⟩ := none
  have := card_le_of_no_matching_no_star family size positive nondiagonal
    (by rintro ⟨sub, inside, matching, big⟩; exact absurd big (by
      have := noMatching sub inside matching; omega))
    (by rintro ⟨centre, sub, inside, star, big⟩; exact absurd big (by
      have := noStar centre sub inside star; omega))
  omega

end Hypostructure.Graph.PatternFamily
