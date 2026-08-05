import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Token loads, the high-load alternative, and the tokenized closure

Three accounting statements about a finite charge map from a set of blocked
demand pairs onto a finite token universe, and the arithmetic that turns a
uniform load bound into a square-root bound on the demand family.

`lem:token-ledger-no-overcount`:

  `|Π_blk| = Σ_{t ∈ 𝔗_cap} ℓ_cap(t)`,

which is the fibre partition of the charge map and nothing more -- the
manuscript's "no disjointness loss" is exactly the statement that the fibres
partition, so it is a `card_eq_sum_card_fiberwise` and not an estimate.

`lem:capacity-token-high-load`:

  `C(s,2) ≤ E_spine(n) + ((1/2)σ + 1)log₂ n + L_max|𝔗_cap|`,

from the free/blocked split of the pair set, the entropy sandwich bound on the
free part, and the fibre partition on the blocked part.  The entropy budget
enters as a parameter: this file does not know how the free pairs were charged,
and does not need to.

`thm:tokenized-surplus-accounting-closure`:  a uniform load bound `M₀` turns
that display into `σ(G) = O(√n)`.  The manuscript argues asymptotically,
absorbing the terms linear in `σ` into `σ²/2`; the exact finite form below does
the absorption explicitly and keeps the constant visible:

  `s(s−1) ≤ A + B·s` gives `s ≤ 1 + B + ⌊√A⌋`,

with `A` the part of the budget that does not scale with the demand family and
`B` the part that does.  At `A = 2C_E n + 16M₀ n` and `B = 2M₀` -- the values
`|𝔗_cap| ≤ 8n + σ(G)` and `E_spine(n) ≤ C_E n` produce -- this is the
manuscript's `σ(G) = O(√n)` with the implicit constant written out.

Nothing here is about graphs.  The token universe, the pattern set and the
charge map are arbitrary.
-/

namespace Hypostructure.Graph.TokenLoad

open scoped BigOperators

universe u v

variable {Token : Type u} {Pattern : Type v} [DecidableEq Token]

/-- **`Θ_cap^{-1}(t)`**: the patterns the charge map sends to a token.  This is
the edge set of the token-fibre graph `H_t` of `def:same-token-patterns`. -/
def fibre (blocked : Finset Pattern) (charge : Pattern → Token) (token : Token) :
    Finset Pattern :=
  blocked.filter fun pattern => charge pattern = token

theorem fibre_subset (blocked : Finset Pattern) (charge : Pattern → Token)
    (token : Token) : fibre blocked charge token ⊆ blocked :=
  Finset.filter_subset _ _

/-- **`ℓ_cap(t) = |Θ_cap^{-1}(t)| = e(H_t)`**. -/
def load (blocked : Finset Pattern) (charge : Pattern → Token) (token : Token) : Nat :=
  (fibre blocked charge token).card

theorem load_eq_card_fibre (blocked : Finset Pattern) (charge : Pattern → Token)
    (token : Token) : load blocked charge token = (fibre blocked charge token).card :=
  rfl

/-- **`lem:token-ledger-no-overcount`.**

  `|Π_blk| = Σ_{t ∈ 𝔗_cap} ℓ_cap(t)`.

The fibres of the charge map partition the blocked set, so the ledger has no
double counting and no loss.  This is the identity, not a bound. -/
theorem card_eq_sum_load (blocked : Finset Pattern) (tokens : Finset Token)
    (charge : Pattern → Token) (declared : ∀ pattern ∈ blocked, charge pattern ∈ tokens) :
    blocked.card = ∑ token ∈ tokens, load blocked charge token :=
  Finset.card_eq_sum_card_fiberwise declared

/-- **`|Π_blk| ≤ M₀|𝔗_cap|`**: the ledger under a uniform load bound. -/
theorem card_le_mul_of_load_le (blocked : Finset Pattern) (tokens : Finset Token)
    (charge : Pattern → Token) (bound : Nat)
    (declared : ∀ pattern ∈ blocked, charge pattern ∈ tokens)
    (loads : ∀ token ∈ tokens, load blocked charge token ≤ bound) :
    blocked.card ≤ bound * tokens.card := by
  calc blocked.card
      = ∑ token ∈ tokens, load blocked charge token :=
        card_eq_sum_load blocked tokens charge declared
    _ ≤ ∑ _token ∈ tokens, bound := Finset.sum_le_sum loads
    _ = bound * tokens.card := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Nat.mul_comm]

/-- **`L_max`, realized.**  Some token carries a load large enough that the
whole blocked set fits inside `|𝔗_cap|` copies of it.  This is the maximum the
manuscript writes as `L_max := max_t ℓ_cap(t)`, produced as a witness rather
than as a defined extremum. -/
theorem exists_load_ge (blocked : Finset Pattern) (tokens : Finset Token)
    (charge : Pattern → Token) (nonempty : tokens.Nonempty)
    (declared : ∀ pattern ∈ blocked, charge pattern ∈ tokens) :
    ∃ token ∈ tokens, blocked.card ≤ tokens.card * load blocked charge token := by
  classical
  obtain ⟨best, bestMem, bestMax⟩ :=
    Finset.exists_max_image tokens (fun token => load blocked charge token) nonempty
  refine ⟨best, bestMem, ?_⟩
  calc blocked.card
      = ∑ token ∈ tokens, load blocked charge token :=
        card_eq_sum_load blocked tokens charge declared
    _ ≤ ∑ _token ∈ tokens, load blocked charge best :=
        Finset.sum_le_sum fun token tokenMem => bestMax token tokenMem
    _ = tokens.card * load blocked charge best :=
        Finset.sum_const_nat fun _ _ => rfl

/-- **`lem:capacity-token-high-load`, first display.**

  `C(s,2) ≤ E_spine(n) + ((1/2)σ + 1)log₂ n + L_max|𝔗_cap|`.

The pair set splits as `Π_free ⊔ Π_blk`; the free part is bounded by the
entropy budget the caller supplies, and the blocked part by the fibre
partition under the load bound. -/
theorem pairCount_le_entropy_add_load_mul (blocked : Finset Pattern)
    (tokens : Finset Token) (charge : Pattern → Token)
    (pairCount free entropyBudget maxLoad : Nat)
    (split : pairCount = free + blocked.card)
    (sandwich : free ≤ entropyBudget)
    (declared : ∀ pattern ∈ blocked, charge pattern ∈ tokens)
    (loads : ∀ token ∈ tokens, load blocked charge token ≤ maxLoad) :
    pairCount ≤ entropyBudget + maxLoad * tokens.card := by
  have blockedBound :=
    card_le_mul_of_load_le blocked tokens charge maxLoad declared loads
  omega

/-- **The absorption step of `thm:tokenized-surplus-accounting-closure`.**

  `s(s−1) ≤ A + B·s`  gives  `s ≤ 1 + B + ⌊√A⌋`.

The manuscript absorbs the terms linear in `σ(G)` into `σ(G)²/2` "after
increasing constants"; this is that absorption done exactly, with the increase
recorded as the visible summand `B`. -/
theorem le_one_add_of_quadratic_le (demand quadraticBudget linearRate : Nat)
    (budget : demand * (demand - 1) ≤ quadraticBudget + linearRate * demand) :
    demand ≤ 1 + linearRate + Nat.sqrt quadraticBudget := by
  by_contra big
  push_neg at big
  set root := Nat.sqrt quadraticBudget with rootDef
  -- The demand exceeds the claimed bound, so its excess above `1 + B` is at
  -- least one more than the integer square root.
  obtain ⟨excess, demandDef⟩ :
      ∃ excess, demand = excess + 1 + linearRate ∧ root + 1 ≤ excess := by
    exact ⟨demand - 1 - linearRate, by omega, by omega⟩
  obtain ⟨demandEq, excessLarge⟩ := demandDef
  subst demandEq
  have expand : (excess + 1 + linearRate) * (excess + 1 + linearRate - 1) =
      excess * excess + excess * linearRate + excess +
        linearRate * (excess + 1 + linearRate) := by
    have simplify : excess + 1 + linearRate - 1 = excess + linearRate := by omega
    rw [simplify]; ring
  rw [expand] at budget
  have square : excess * excess ≤ quadraticBudget := by omega
  have root_lt : quadraticBudget < (root + 1) * (root + 1) := by
    rw [rootDef]; exact Nat.lt_succ_sqrt quadraticBudget
  have : (root + 1) * (root + 1) ≤ excess * excess :=
    Nat.mul_le_mul excessLarge excessLarge
  omega

/-- **`thm:tokenized-surplus-accounting-closure`, exact finite form.**

Under a uniform token load bound `M₀`, a linear token supply `|𝔗_cap| ≤ κ + s`
and a demand-independent entropy budget, the active family satisfies

  `s ≤ 1 + 2M₀ + ⌊√(2·entropy + 2M₀·κ)⌋`.

At the manuscript's values `κ = 8n` and `entropy ≤ C_E n + ((1/2)σ+1)log₂ n`
this is `σ(G) = O(√n)` with the implicit constant, which the manuscript says
"depends only on `c₁, C_E` and `M₀`", written out. -/
theorem demand_le_of_bounded_load (demand entropyBudget loadBound tokenCount scale : Nat)
    (budget : demand.choose 2 ≤ entropyBudget + loadBound * tokenCount)
    (supply : tokenCount ≤ scale + demand) :
    demand ≤ 1 + 2 * loadBound +
      Nat.sqrt (2 * entropyBudget + 2 * (loadBound * scale)) := by
  refine le_one_add_of_quadratic_le demand _ _ ?_
  have pairs : 2 * demand.choose 2 = demand * (demand - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm]
    exact Nat.div_mul_cancel demand.even_mul_pred_self.two_dvd
  have supplyMul : loadBound * tokenCount ≤ loadBound * (scale + demand) :=
    Nat.mul_le_mul_left _ supply
  have expand : loadBound * (scale + demand) = loadBound * scale + loadBound * demand := by
    ring
  have doubled : 2 * demand.choose 2 ≤
      2 * entropyBudget + 2 * (loadBound * scale) + 2 * loadBound * demand := by
    have := Nat.mul_le_mul_left 2 budget
    have expand2 : 2 * loadBound * demand = 2 * (loadBound * demand) := by ring
    omega
  omega

end Hypostructure.Graph.TokenLoad
