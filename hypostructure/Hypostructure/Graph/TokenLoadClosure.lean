import Hypostructure.Graph.CanonicalFibreLedger
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The high-load alternative and the tokenized closure

What `lem:capacity-token-high-load` and
`thm:tokenized-surplus-accounting-closure` add to the canonical ledger.

The ledger itself is not built here.  `Graph/CanonicalFibreLedger.lean` is the
single implementation of both of the manuscript's canonical ledgers, and
`lem:token-ledger-no-overcount` -- `|Π_blk| = Σ_t ℓ_cap(t)` -- is its
`card_assigned_eq_sum_multiplicity`.  This module reads that identity; it does
not restate it.  `ℓ_cap(t)` is `CanonicalFibreLedger.multiplicity`.

Three statements are added.

`L_max`, realized: some declared token carries a load large enough that the
whole charged family fits inside `|𝔗_cap|` copies of it.  The manuscript writes
`L_max := max_t ℓ_cap(t)`; a witness is what its consumers actually use.

`lem:capacity-token-high-load`:

  `C(s,2) ≤ E_spine(n) + ((1/2)σ + 1)log₂ n + L_max|𝔗_cap|`,

from the ledger's own free/charged split, the entropy sandwich bound on the free
part, and the fibre identity on the charged part.  The entropy budget is a
parameter: this module does not know how the free pairs were charged.

`thm:tokenized-surplus-accounting-closure`: a uniform load bound `M₀` turns that
display into `σ(G) = O(√n)`.  The manuscript argues asymptotically, absorbing the
terms linear in `σ` into `σ²/2` "after increasing constants"; the exact finite
form below does the absorption explicitly and keeps the constant visible,

  `s(s−1) ≤ A + B·s`  gives  `s ≤ 1 + B + ⌊√A⌋`,

with `A` the part of the budget that does not scale with the demand family and
`B` the part that does.  At `A = 2C_E n + 16M₀ n` and `B = 2M₀` -- the values
`|𝔗_cap| ≤ 8n + σ(G)` and `E_spine(n) ≤ C_E n` produce -- this is the
manuscript's `σ(G) = O(√n)` with the implicit constant written out.
-/

namespace Hypostructure.Graph.TokenLoad

open scoped BigOperators
open Hypostructure.Graph.CanonicalFibreLedger

universe uDemand uLabel

variable {Demand : Type uDemand} {Token : Type uLabel}
variable [DecidableEq Demand] [DecidableEq Token]

/-- **`|Π_blk| ≤ M₀|𝔗_cap|`**: the canonical ledger under a uniform load bound.

The identity spent is `lem:token-ledger-no-overcount` as
`CanonicalFibreLedger.card_assigned_eq_sum_multiplicity`; only the bound is
new. -/
theorem card_assigned_le_mul_of_multiplicity_le
    (demands : Finset Demand) (order : List Token)
    (Applies : Token → Demand → Prop)
    [∀ token demand, Decidable (Applies token demand)] (bound : Nat)
    (loads : ∀ token ∈ order.toFinset,
      multiplicity demands order Applies token ≤ bound) :
    (assigned demands order Applies).card ≤ bound * order.toFinset.card := by
  calc (assigned demands order Applies).card
      = ∑ token ∈ order.toFinset, multiplicity demands order Applies token :=
        card_assigned_eq_sum_multiplicity demands order Applies
    _ ≤ ∑ _token ∈ order.toFinset, bound := Finset.sum_le_sum loads
    _ = bound * order.toFinset.card := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Nat.mul_comm]

/-- **`L_max`, realized.**  Some declared token carries a load large enough that
the whole charged family fits inside `|𝔗_cap|` copies of it.  This is the
maximum the manuscript writes as `L_max := max_t ℓ_cap(t)`, produced as a witness
rather than as a defined extremum. -/
theorem exists_multiplicity_ge
    (demands : Finset Demand) (order : List Token)
    (Applies : Token → Demand → Prop)
    [∀ token demand, Decidable (Applies token demand)]
    (nonempty : order.toFinset.Nonempty) :
    ∃ token ∈ order.toFinset,
      (assigned demands order Applies).card ≤
        order.toFinset.card * multiplicity demands order Applies token := by
  classical
  obtain ⟨best, bestMem, bestMax⟩ :=
    Finset.exists_max_image order.toFinset
      (fun token => multiplicity demands order Applies token) nonempty
  refine ⟨best, bestMem, ?_⟩
  calc (assigned demands order Applies).card
      = ∑ token ∈ order.toFinset, multiplicity demands order Applies token :=
        card_assigned_eq_sum_multiplicity demands order Applies
    _ ≤ ∑ _token ∈ order.toFinset, multiplicity demands order Applies best :=
        Finset.sum_le_sum fun token tokenMem => bestMax token tokenMem
    _ = order.toFinset.card * multiplicity demands order Applies best :=
        Finset.sum_const_nat fun _ _ => rfl

/-- **`lem:capacity-token-high-load`, first display.**

  `C(s,2) ≤ E_spine(n) + ((1/2)σ + 1)log₂ n + L_max|𝔗_cap|`.

The pair set splits as `Π_free ⊔ Π_blk` -- the ledger's own
`card_assigned_add_card_unassigned` -- the free part is bounded by the entropy
budget the caller supplies, and the charged part by the fibre identity under the
load bound. -/
theorem card_le_entropy_add_load_mul
    (demands : Finset Demand) (order : List Token)
    (Applies : Token → Demand → Prop)
    [∀ token demand, Decidable (Applies token demand)]
    (entropyBudget maxLoad : Nat)
    (sandwich : (unassigned demands order Applies).card ≤ entropyBudget)
    (loads : ∀ token ∈ order.toFinset,
      multiplicity demands order Applies token ≤ maxLoad) :
    demands.card ≤ entropyBudget + maxLoad * order.toFinset.card := by
  have split := card_assigned_add_card_unassigned demands order Applies
  have charged :=
    card_assigned_le_mul_of_multiplicity_le demands order Applies maxLoad loads
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
