import Hypostructure.Graph.CapacityTokenLedger

/-!
# Fixture: the matching--star bound and the homogeneous bottleneck closure

Three checks on the mathematics nodes `[137]`--`[144]` commit, at a presentation
small enough that every quantity is computed rather than assumed.

* **`lem:same-token-matching-star` is sharp.**  The triangle has `ν = 1`,
  `Δ = 2` and `e = 3`, and the bound `e(H) ≤ ν(2Δ − 1)` reads `3 ≤ 3` with
  equality.  A bound that were true but loose would be worthless to
  `cor:homogeneous-same-token-caps-close`, whose content is that the cap it
  produces is the right one; this pins that the coefficients carry no slack.
* **`ψ` is the least covering scale.**  `ψ(3) = 2`, because `3 ≤ 2(2·2−1)` and
  neither `0` nor `1` covers `3`.  That is the defining minimality of
  `def:homogeneous-token-charge`, evaluated.
* **The ledger closes.**  A presented `CapacityTokenLedger` over three active
  demands whose pair schedule is the triangle, with one capacity token eligible
  for every pair and therefore no free pairs, satisfies clauses (a), (b), (c) of
  `cor:homogeneous-same-token-caps-close` at `L = 3`; the corollary's three
  conclusions -- the uniform load bound, `|Π_blk| ≤ M₀|𝔗_cap|`, and the
  square-root bound on the active family -- then hold at computed values.

The pair representation is the branch's own: a pair is a two-element `Finset` of
demands, which is what `CanonicalFibreLedger.pairs` and
`FiniteObject.portPairSchedule` produce.  Nothing here is specific to one
manuscript.
-/

namespace Hypostructure.Fixtures.HomogeneousTokenBottleneck

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.SameTokenBlockerRoles

/-! ## The triangle -/

/-- The triangle, as a family of pairs on three active demands. -/
def triangle : Finset (Finset (Fin 3)) :=
  {{0, 1}, {1, 2}, {0, 2}}

theorem card_triangle : triangle.card = 3 := by decide

theorem pairs_triangle : ∀ pair ∈ triangle, pair.card = 2 := by decide

set_option maxRecDepth 8000 in
/-- `ν(triangle) = 1`: any two of its pairs meet.  The quantifier is over the
powerset, which is where the decision procedure can reach it. -/
theorem matchings_triangle :
    ∀ sub ⊆ triangle, PatternFamily.IsMatching sub → sub.card ≤ 1 := by
  have bounded : ∀ sub ∈ triangle.powerset,
      PatternFamily.IsMatching sub → sub.card ≤ 1 := by decide
  intro sub inside matching
  exact bounded sub (Finset.mem_powerset.mpr inside) matching

/-- `Δ(triangle) = 2`. -/
theorem degrees_triangle :
    ∀ vertex : Fin 3, PatternFamily.degree triangle vertex ≤ 2 := by decide

/-- The triangle is not a star: every demand misses one of its three pairs. -/
theorem not_star_triangle :
    ∀ centre : Fin 3, ¬ PatternFamily.IsStar triangle centre := by decide

/-- **`lem:same-token-matching-star` is attained at the triangle**: the bound
`e(H) ≤ ν(2Δ − 1)` reads `3 ≤ 1 · 3`, with equality. -/
theorem matching_star_sharp :
    triangle.card ≤ 1 * (2 * 2 - 1) ∧ triangle.card = 1 * (2 * 2 - 1) :=
  ⟨PatternFamily.card_le_matching_mul_two_mul_degree_sub_one triangle 1 2
      pairs_triangle matchings_triangle degrees_triangle,
    card_triangle⟩

/-- **`ψ(3) = 2`**, by the two halves of its defining minimality. -/
theorem patternThreshold_three : PatternFamily.patternThreshold 3 = 2 := by
  have upper : PatternFamily.patternThreshold 3 ≤ 2 :=
    PatternFamily.patternThreshold_le 3 2 (by decide)
  have covers := PatternFamily.le_patternThreshold_mul 3
  match remaining : PatternFamily.patternThreshold 3 with
  | 0 => rw [remaining] at covers; omega
  | 1 => rw [remaining] at covers; omega
  | 2 => rfl
  | (k + 3) => omega

/-! ## The presented ledger -/

/-- A presented capacity-token ledger over three active demands: the pair
schedule is the triangle, one capacity token is eligible for every pair, and
therefore no pair is free. -/
def ledger : CapacityTokenLedger.{0} 3 where
  Demand := Fin 3
  demandDecidable := inferInstance
  Token := Fin 1
  tokenDecidable := inferInstance
  order := [0]
  orderNonempty := by decide
  subtype := fun _ => .primitiveVertex
  schedule := triangle
  scheduleCard := by decide
  schedulePairs := pairs_triangle
  Eligible := fun _ _ => True
  eligibleDecidable := fun _ _ => inferInstance
  role := fun _ => default
  entropyBudget := 0
  sandwich := by decide

/-- The triangle facts, restated at the ledger's own demand type so that later
proofs stay inside one type.  Each is the corresponding triangle theorem: the
ledger's schedule *is* the triangle. -/
theorem card_schedule : ledger.schedule.card = 3 := card_triangle

theorem matchings_schedule :
    ∀ sub ⊆ ledger.schedule, PatternFamily.IsMatching sub → sub.card ≤ 1 :=
  matchings_triangle

theorem not_star_schedule :
    ∀ centre : ledger.Demand, ¬ PatternFamily.IsStar ledger.schedule centre :=
  not_star_triangle

/-- **`lem:token-ledger-no-overcount`, at this presentation**: the single token's
load accounts for the whole charged family.  The identity is the canonical
ledger's own; only the instance is new. -/
theorem ledger_no_overcount :
    ledger.blocked.card = ∑ token ∈ ledger.tokens, ledger.load token :=
  ledger.blocked_card_eq_sum_load

/-- **The split**: `|Π_blk| + |Π_free| = C(3,2)`. -/
theorem ledger_split :
    ledger.blocked.card + ledger.free.card = Nat.choose 3 2 :=
  ledger.blocked_card_add_free_card

/-- Clauses (a), (b), (c) of `cor:homogeneous-same-token-caps-close` at `L = 3`,
matching half: no role fibre carries a `3`-matching, because no subfamily of the
triangle does. -/
theorem ledger_no_homogeneous_matching :
    ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsMatching pattern ∧ 3 ≤ pattern.card := by
  rintro token _ value ⟨pattern, inside, matching, large⟩
  have reaches : pattern ⊆ ledger.schedule :=
    subset_trans inside
      (subset_trans (PatternFamily.roleFibre_subset _ _ _)
        (ledger.fibre_subset token))
  have := matchings_schedule pattern reaches matching
  omega

/-- The same clauses, star half: a `3`-star inside the schedule would have to be
all of it, and the triangle is not a star. -/
theorem ledger_no_homogeneous_star :
    ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsStar pattern centre ∧ 3 ≤ pattern.card := by
  rintro token _ value ⟨centre, pattern, inside, star, large⟩
  have reaches : pattern ⊆ ledger.schedule :=
    subset_trans inside
      (subset_trans (PatternFamily.roleFibre_subset _ _ _)
        (ledger.fibre_subset token))
  have whole : pattern = ledger.schedule :=
    Finset.eq_of_subset_of_card_le reaches (by rw [card_schedule]; omega)
  subst whole
  exact not_star_schedule centre star

/-- **`cor:homogeneous-same-token-caps-close`, at this presentation.**

With `L_W = L_R = L_P = 3` the uniform cap is `M₀ = Cap_hom(3)`, the token supply
is `|𝔗_cap| = 1 ≤ 0 + 3`, and the corollary's three conclusions hold. -/
theorem ledger_caps_close :
    (∀ token ∈ ledger.tokens, ledger.load token ≤ homogeneousCapCharge 3) ∧
      ledger.blocked.card ≤ homogeneousCapCharge 3 * ledger.tokens.card ∧
      (3 : Nat) ≤ 1 + 2 * homogeneousCapCharge 3 +
        Nat.sqrt (2 * ledger.entropyBudget + 2 * (homogeneousCapCharge 3 * 0)) :=
  ledger.caps_close (fun _ => 3) (homogeneousCapCharge 3) 0
    (fun _ => by omega) (fun _ => Nat.le_refl _) (by decide)
    ledger_no_homogeneous_matching ledger_no_homogeneous_star

end Hypostructure.Fixtures.HomogeneousTokenBottleneck
