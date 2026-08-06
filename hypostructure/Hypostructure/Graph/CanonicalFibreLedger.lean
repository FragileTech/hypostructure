import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum

/-!
# Canonical single-valued ledgers and their no-overcount identity

`def:canonical-blocker-ledger` and `def:capacity-token-ledger` are the same
construction twice: a finite family of *demands*, a declared total order on a
finite *label* alphabet, a per-label relation saying that a label applies to a
demand, and the assignment that sends each applying demand to the **first**
applicable label in that order.  The manuscript's two no-overcount lemmas --
`lem:canonical-blocker-ledger-no-overcount` (`|Π_blk| = Σ_B μ(B)`) and
`lem:token-ledger-no-overcount` (`|Π_blk| = Σ_t ℓ_cap(t)`) -- are the same
statement about that assignment: the fibres of a single-valued map partition its
domain, so the fibre multiplicities sum to the number of assigned demands and
nothing is charged twice.

Everything here is stated about an arbitrary demand type, an arbitrary label
alphabet, and an arbitrary applicability relation, because that is exactly what
the two lemmas use: their proofs never inspect what a blocker or a token *is*,
only that the canonical choice is single-valued and lands in the declared
alphabet.  The declared order is a `List`, which is what makes "the first
applicable label" canonical and total.

This module is the single implementation of both ledgers.  A consumer supplies
its own alphabet and order -- `def:canonical-sparse-blocker-order` at one node,
`def:capacity-token-ledger`'s token universe at the next -- and reads the same
identity back.
-/

namespace Hypostructure.Graph.CanonicalFibreLedger

universe uDemand uLabel

variable {Demand : Type uDemand} {Label : Type uLabel}

/-- **`Π(𝒜₀) = C(𝒜₀,2)`**: the unordered pairs of a finite family. -/
def pairs [DecidableEq Demand] (family : Finset Demand) : Finset (Finset Demand) :=
  family.powersetCard 2

/-- The pair count of a family is the binomial coefficient the manuscript
writes. -/
theorem card_pairs [DecidableEq Demand] (family : Finset Demand) :
    (pairs family).card = family.card.choose 2 :=
  Finset.card_powersetCard 2 family

/-- **The canonical assignment.**  The first label of the declared order that
applies to the demand, if any.  Single-valuedness is `Option`'s, and canonicity
is the order's: nothing here chooses. -/
def appliesTo (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] (demand : Demand)
    (label : Label) : Bool :=
  decide (Applies label demand)

/-- The first applicable label of the declared order, if any. -/
def canonicalLabel (order : List Label) (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] (demand : Demand) :
    Option Label :=
  order.find? (appliesTo Applies demand)

/-- The canonical label really applies: it was found by the search. -/
theorem applies_canonicalLabel {order : List Label}
    {Applies : Label → Demand → Prop}
    [∀ label demand, Decidable (Applies label demand)] {demand : Demand}
    {label : Label} (found : canonicalLabel order Applies demand = some label) :
    Applies label demand := by
  exact of_decide_eq_true (List.find?_some (p := appliesTo Applies demand) found)

/-- The canonical label is one of the declared alphabet's. -/
theorem mem_of_canonicalLabel {order : List Label}
    {Applies : Label → Demand → Prop}
    [∀ label demand, Decidable (Applies label demand)] {demand : Demand}
    {label : Label} (found : canonicalLabel order Applies demand = some label) :
    label ∈ order := by
  exact List.mem_of_find?_eq_some found

/-- **`Π_blk`**: the demands the ledger charges, those some declared label
applies to. -/
def assigned [DecidableEq Demand] (demands : Finset Demand) (order : List Label)
    (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] : Finset Demand :=
  demands.filter fun demand => (canonicalLabel order Applies demand).isSome

/-- **`Π_free`**: the complementary demands, which no declared label applies
to. -/
def unassigned [DecidableEq Demand] (demands : Finset Demand)
    (order : List Label) (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] : Finset Demand :=
  demands.filter fun demand => ¬ (canonicalLabel order Applies demand).isSome

/-- **`μ(B)`, `ℓ_cap(t)`**: the multiplicity of one label, the number of demands
the canonical assignment sends to it. -/
def multiplicity [DecidableEq Demand] [DecidableEq Label]
    (demands : Finset Demand) (order : List Label)
    (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] (label : Label) : Nat :=
  (demands.filter fun demand =>
    canonicalLabel order Applies demand = some label).card

/-- **The split is exhaustive**: every demand is either charged or free. -/
theorem card_assigned_add_card_unassigned [DecidableEq Demand]
    (demands : Finset Demand) (order : List Label)
    (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] :
    (assigned demands order Applies).card +
        (unassigned demands order Applies).card = demands.card := by
  classical
  rw [assigned, unassigned]
  exact Finset.card_filter_add_card_filter_not _

/-- **A demand is charged exactly when some declared label applies to it.** -/
theorem isSome_canonicalLabel_iff (order : List Label)
    (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] (demand : Demand) :
    (canonicalLabel order Applies demand).isSome ↔
      ∃ label ∈ order, Applies label demand := by
  constructor
  · intro charged
    obtain ⟨label, found⟩ := Option.isSome_iff_exists.1 charged
    exact ⟨label, mem_of_canonicalLabel found, applies_canonicalLabel found⟩
  · intro ⟨label, member, applies⟩
    rcases equality : canonicalLabel order Applies demand with _ | found
    · rw [canonicalLabel, List.find?_eq_none] at equality
      exact absurd (decide_eq_true applies) (equality label member)
    · simp

/-- **A total assignment charges every demand.**

`Θ_cap` is defined on all of `Π_blk` -- its last case is the primitive carrier
`κ(B_π)`, which is always available -- so the manuscript's
`|Π_blk| = Σ_t ℓ_cap(t)` is the fibre identity at a *total* assignment. -/
theorem assigned_eq_of_total [DecidableEq Demand] (demands : Finset Demand)
    (order : List Label) (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)]
    (total : ∀ demand ∈ demands, ∃ label ∈ order, Applies label demand) :
    assigned demands order Applies = demands := by
  classical
  refine Finset.filter_true_of_mem fun demand member => ?_
  exact Option.isSome_iff_exists.2
    (Option.isSome_iff_exists.1
      ((isSome_canonicalLabel_iff order Applies demand).2 (total demand member)))

/-- **The no-overcount identity**, shared by
`lem:canonical-blocker-ledger-no-overcount` and
`lem:token-ledger-no-overcount`:

  `|Π_blk| = Σ_{label ∈ alphabet} multiplicity label`.

The canonical assignment is a function into the declared alphabet, so its fibres
partition the charged demands: no charged demand is missed and none is counted
at two labels. -/
theorem card_assigned_eq_sum_multiplicity [DecidableEq Demand] [DecidableEq Label]
    (demands : Finset Demand) (order : List Label)
    (Applies : Label → Demand → Prop)
    [∀ label demand, Decidable (Applies label demand)] :
    (assigned demands order Applies).card =
      ∑ label ∈ order.toFinset,
        multiplicity demands order Applies label := by
  classical
  have fibres :
      (assigned demands order Applies).card =
        ∑ value ∈ order.toFinset.image (some : Label → Option Label),
          ((assigned demands order Applies).filter
            fun demand => canonicalLabel order Applies demand = value).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro demand member
    have inside : demand ∈ assigned demands order Applies := member
    rw [assigned, Finset.mem_filter] at inside
    obtain ⟨label, found⟩ := Option.isSome_iff_exists.1 inside.2
    rw [found]
    exact Finset.mem_image.2
      ⟨label, List.mem_toFinset.2 (mem_of_canonicalLabel found), rfl⟩
  rw [fibres, Finset.sum_image (fun _ _ _ _ equality => Option.some_injective _ equality)]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [multiplicity, assigned, Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr fun demand _ => ?_)
  constructor
  · exact fun applied => applied.2
  · exact fun found => ⟨by rw [found]; rfl, found⟩

end Hypostructure.Graph.CanonicalFibreLedger
