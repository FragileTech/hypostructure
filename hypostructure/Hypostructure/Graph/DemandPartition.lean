import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The 2/3-demand partition

`def:typeA-pressure-ledger`'s combinatorial core, generically: a partition of
the entry index set into `Ξ₃ ⊔ Ξ₂ ⊔ Ξ_res`, with pairwise-disjoint assigned
incidence sets of sizes `3` and `2` drawn from each entry's available boundary
incidences, and the external-demand defect `𝖯_ext = N₂ + 3·N_res`.  The
no-overcount lemma `lem:typeA-pressure-ledger-no-overcount` is the pure
counting statement `3N₃ + 2N₂ ≤ |supply|`, equivalently
`3·Ñ ≤ |supply| + 𝖯_ext`, once every assigned incidence lies in the common
supply.  Nothing here mentions a graph, a support, or a presentation constant:
the boundary-incidence semantics enter through the `available`/`supply`
instantiation at the consuming row.
-/

namespace Hypostructure.Graph.DemandPartition

variable {Index Carrier : Type*} [DecidableEq Index] [DecidableEq Carrier]

/-- The `2/3`-demand partition of `def:typeA-pressure-ledger`: clauses
(L3)–(L5) on an abstract entry family. -/
structure Partition (entries : Finset Index)
    (available : Index → Finset Carrier) where
  /-- `Ξ₃`, the fully paid entries. -/
  three : Finset Index
  /-- `Ξ₂`, the two-incidence entries. -/
  two : Finset Index
  /-- `Ξ_res`, the unassigned residual. -/
  residual : Finset Index
  cover : three ∪ two ∪ residual = entries
  three_disj_two : Disjoint three two
  three_disj_residual : Disjoint three residual
  two_disj_residual : Disjoint two residual
  /-- `A(ξ)`, the assigned incidences (read only on `Ξ₃ ∪ Ξ₂`). -/
  assigned : Index → Finset Carrier
  assigned_available : ∀ ξ ∈ three ∪ two, assigned ξ ⊆ available ξ
  assigned_three : ∀ ξ ∈ three, (assigned ξ).card = 3
  assigned_two : ∀ ξ ∈ two, (assigned ξ).card = 2
  assigned_disjoint : ∀ ξ ∈ three ∪ two, ∀ ζ ∈ three ∪ two, ξ ≠ ζ →
    Disjoint (assigned ξ) (assigned ζ)

namespace Partition

variable {entries : Finset Index} {available : Index → Finset Carrier}
variable (P : Partition entries available)

/-- `𝖯_ext = N₂ + 3·N_res`. -/
def externalDefect : Nat :=
  P.two.card + 3 * P.residual.card

/-- The three classes partition the entry count. -/
theorem card_entries_eq :
    entries.card = P.three.card + P.two.card + P.residual.card := by
  classical
  have unionDisjoint : Disjoint (P.three ∪ P.two) P.residual :=
    Finset.disjoint_union_left.mpr ⟨P.three_disj_residual, P.two_disj_residual⟩
  calc entries.card = ((P.three ∪ P.two) ∪ P.residual).card := by rw [P.cover]
    _ = (P.three ∪ P.two).card + P.residual.card :=
        Finset.card_union_of_disjoint unionDisjoint
    _ = P.three.card + P.two.card + P.residual.card := by
        rw [Finset.card_union_of_disjoint P.three_disj_two]

/-- **`lem:typeA-pressure-ledger-no-overcount`, the raw count**: the assigned
incidences are pairwise disjoint members of the supply, so
`3N₃ + 2N₂ ≤ |supply|`. -/
theorem three_mul_add_two_mul_le (supply : Finset Carrier)
    (supplied : ∀ ξ ∈ P.three ∪ P.two, P.assigned ξ ⊆ supply) :
    3 * P.three.card + 2 * P.two.card ≤ supply.card := by
  classical
  have biCard : ((P.three ∪ P.two).biUnion P.assigned).card =
      ∑ ξ ∈ P.three ∪ P.two, (P.assigned ξ).card :=
    Finset.card_biUnion P.assigned_disjoint
  have sumSplit : ∑ ξ ∈ P.three ∪ P.two, (P.assigned ξ).card =
      (∑ ξ ∈ P.three, (P.assigned ξ).card) +
        ∑ ξ ∈ P.two, (P.assigned ξ).card :=
    Finset.sum_union P.three_disj_two
  have threeSum : ∑ ξ ∈ P.three, (P.assigned ξ).card = P.three.card * 3 :=
    Finset.sum_const_nat P.assigned_three
  have twoSum : ∑ ξ ∈ P.two, (P.assigned ξ).card = P.two.card * 2 :=
    Finset.sum_const_nat P.assigned_two
  have contained : (P.three ∪ P.two).biUnion P.assigned ⊆ supply :=
    Finset.biUnion_subset.mpr supplied
  have := Finset.card_le_card contained
  omega

/-- **The equivalent defect form**: `3·Ñ − 𝖯_ext ≤ |supply|`, written
subtraction-free as `3·Ñ ≤ |supply| + 𝖯_ext`. -/
theorem three_mul_card_le (supply : Finset Carrier)
    (supplied : ∀ ξ ∈ P.three ∪ P.two, P.assigned ξ ⊆ supply) :
    3 * entries.card ≤ supply.card + P.externalDefect := by
  have raw := P.three_mul_add_two_mul_le supply supplied
  have split := P.card_entries_eq
  unfold externalDefect
  omega

end Partition

/-- **Type (A1) boundary absorbers** (`def:typeA-pressure-absorbers`): an
assignment of one further supply incidence to each absorbed demand unit,
single-use and disjoint from every ledger assignment. -/
structure Absorption {entries : Finset Index}
    {available : Index → Finset Carrier}
    (P : Partition entries available) (Unit : Type*) where
  /-- The absorbed units. -/
  absorbed : Finset Unit
  /-- The absorbing incidence of each unit. -/
  absorber : Unit → Carrier
  absorber_injective : ∀ υ ∈ absorbed, ∀ ν ∈ absorbed, υ ≠ ν →
    absorber υ ≠ absorber ν
  absorber_unused : ∀ υ ∈ absorbed, ∀ ξ ∈ P.three ∪ P.two,
    absorber υ ∉ P.assigned ξ

namespace Absorption

variable {entries : Finset Index} {available : Index → Finset Carrier}
variable {P : Partition entries available} {Unit : Type*} [DecidableEq Unit]
variable (A : Absorption P Unit)

/-- **`lem:typeA-pressure-absorber-no-overcount`, the raw count**: the ledger
assignments and the absorbers use `3N₃ + 2N₂ + B_abs` pairwise-distinct
incidences of the supply. -/
theorem three_mul_add_two_mul_add_card_le [DecidableEq Carrier]
    (supply : Finset Carrier)
    (supplied : ∀ ξ ∈ P.three ∪ P.two, P.assigned ξ ⊆ supply)
    (absorberSupplied : ∀ υ ∈ A.absorbed, A.absorber υ ∈ supply) :
    3 * P.three.card + 2 * P.two.card + A.absorbed.card ≤ supply.card := by
  classical
  have biCard : ((P.three ∪ P.two).biUnion P.assigned).card =
      ∑ ξ ∈ P.three ∪ P.two, (P.assigned ξ).card :=
    Finset.card_biUnion P.assigned_disjoint
  have sumSplit : ∑ ξ ∈ P.three ∪ P.two, (P.assigned ξ).card =
      (∑ ξ ∈ P.three, (P.assigned ξ).card) +
        ∑ ξ ∈ P.two, (P.assigned ξ).card :=
    Finset.sum_union P.three_disj_two
  have threeSum : ∑ ξ ∈ P.three, (P.assigned ξ).card = P.three.card * 3 :=
    Finset.sum_const_nat P.assigned_three
  have twoSum : ∑ ξ ∈ P.two, (P.assigned ξ).card = P.two.card * 2 :=
    Finset.sum_const_nat P.assigned_two
  have absorberCard : (A.absorbed.image A.absorber).card = A.absorbed.card :=
    Finset.card_image_of_injOn fun υ υMem ν νMem eq => by
      by_contra ne
      exact A.absorber_injective υ υMem ν νMem ne eq
  have absorberDisjoint :
      Disjoint ((P.three ∪ P.two).biUnion P.assigned)
        (A.absorbed.image A.absorber) := by
    rw [Finset.disjoint_right]
    intro carrier imageMem biMem
    obtain ⟨υ, υMem, rfl⟩ := Finset.mem_image.mp imageMem
    obtain ⟨ξ, ξMem, assignedMem⟩ := Finset.mem_biUnion.mp biMem
    exact A.absorber_unused υ υMem ξ ξMem assignedMem
  have unionContained :
      (P.three ∪ P.two).biUnion P.assigned ∪ A.absorbed.image A.absorber ⊆
        supply := by
    refine Finset.union_subset (Finset.biUnion_subset.mpr supplied) ?_
    intro carrier imageMem
    obtain ⟨υ, υMem, rfl⟩ := Finset.mem_image.mp imageMem
    exact absorberSupplied υ υMem
  have unionCard := Finset.card_union_of_disjoint absorberDisjoint
  have := Finset.card_le_card unionContained
  omega

end Absorption

/-- **`prop:typeA-exit4-closure-from-open-pressure`, the cleared arithmetic.**

Three integer readings collide, exactly as in the census squeeze but with the
open demand carried on the budget side:

* `deficit` — `ambient ≤ basins + discharge·supply + slack`, the unified
  deficit with its sublinear allowance;
* `budget`  — `floor·basins ≤ supply + opendemand`, the no-overcount count
  with the unabsorbed units on the right (`3Ñ − 𝖯_open ≤ def⁺(R)`);
* `rate`    — `(floor·discharge + 1)·supply + floor·slack + opendemand <
  floor·ambient`, the registered rate with the open demand below the
  threshold margin.

No constant appears; every reading is one the branch carries. -/
theorem open_pressure_contradiction
    {floor discharge basins supply ambient slack opendemand : Nat}
    (deficit : ambient ≤ basins + discharge * supply + slack)
    (budget : floor * basins ≤ supply + opendemand)
    (rate : (floor * discharge + 1) * supply + floor * slack + opendemand <
      floor * ambient) :
    False := by
  have scaled : floor * ambient ≤
      floor * basins + floor * (discharge * supply) + floor * slack := by
    have step : floor * ambient ≤
        floor * (basins + discharge * supply + slack) :=
      Nat.mul_le_mul_left _ deficit
    rw [Nat.mul_add, Nat.mul_add] at step
    exact step
  have assoc : floor * (discharge * supply) = floor * discharge * supply :=
    (mul_assoc _ _ _).symm
  rw [assoc] at scaled
  have expand : (floor * discharge + 1) * supply =
      floor * discharge * supply + supply := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **`lem:typeA-open-window-blocker-count`**: assigning every open unit to a
unique window partitions the open demand into the window-blocker loads —
`𝖯_open = Σ_P B_open(P)`.  Generic fibre counting; the canonical blocker
choice (first token incidence, unique packed window through `W`) enters at
the consuming row. -/
theorem card_eq_sum_fibres {Unit Window : Type*}
    [DecidableEq Unit] [DecidableEq Window]
    (units : Finset Unit) (windows : Finset Window) (blocker : Unit → Window)
    (assigned : ∀ υ ∈ units, blocker υ ∈ windows) :
    units.card = ∑ P ∈ windows, (units.filter fun υ => blocker υ = P).card := by
  classical
  have cover : units =
      windows.biUnion fun P => units.filter fun υ => blocker υ = P := by
    ext υ
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro member
      exact ⟨blocker υ, assigned υ member, member, rfl⟩
    · rintro ⟨P, _windowMem, member, rfl⟩
      exact member
  have fibresDisjoint : ∀ left ∈ windows, ∀ right ∈ windows, left ≠ right →
      Disjoint (units.filter fun υ => blocker υ = left)
        (units.filter fun υ => blocker υ = right) := by
    intro left _leftMem right _rightMem distinct
    rw [Finset.disjoint_left]
    intro υ leftMem rightMem
    exact distinct ((Finset.mem_filter.mp leftMem).2.symm.trans
      (Finset.mem_filter.mp rightMem).2)
  conv_lhs => rw [cover]
  exact Finset.card_biUnion fibresDisjoint

/-- **The per-window split of the open demand**
(`fig:exit4-p13-attachment-accounting`): the first two units per window enter
the base term and the rest is the per-window excess —
`𝖯_open ≤ 2·p + Σ_P (B_open(P) − 2)`, with truncated subtraction. -/
theorem card_le_two_mul_card_add_excess {Unit Window : Type*}
    [DecidableEq Unit] [DecidableEq Window]
    (units : Finset Unit) (windows : Finset Window) (blocker : Unit → Window)
    (assigned : ∀ υ ∈ units, blocker υ ∈ windows) :
    units.card ≤ 2 * windows.card +
      ∑ P ∈ windows, ((units.filter fun υ => blocker υ = P).card - 2) := by
  classical
  have partition := card_eq_sum_fibres units windows blocker assigned
  have pointwise : ∀ P ∈ windows,
      (units.filter fun υ => blocker υ = P).card ≤
        2 + ((units.filter fun υ => blocker υ = P).card - 2) := by
    intro P _member
    omega
  have summed := Finset.sum_le_sum pointwise
  have baseSum : ∑ _P ∈ windows, (2 : Nat) = windows.card * 2 :=
    Finset.sum_const_nat fun _ _ => rfl
  rw [Finset.sum_add_distrib, baseSum] at summed
  omega

/-! ## The maximal ledger choice

`def:typeA-pressure-ledger`, clause (L1) and the closing paragraph: the pinned
entries (the manuscript's surviving route-8 entries) must be fully paid with
three incidences drawn from their private availability — pairwise-disjoint
private essential incidences — and among all such ledgers one is chosen
maximizing first `N₃ = |Ξ₃|`, then `N₂ = |Ξ₂|`.  The choice is purely
combinatorial; which entries are pinned and what availability and private
availability mean are decided by the consuming row. -/

namespace Partition

variable {entries : Finset Index} {available : Index → Finset Carrier}

/-- **Clause (L1) of `def:typeA-pressure-ledger`**: every pinned entry lies in
`Ξ₃`, paid from its private availability. -/
def Pinned (pinned : Finset Index) (privateAvailable : Index → Finset Carrier)
    (P : Partition entries available) : Prop :=
  pinned ⊆ P.three ∧ ∀ ξ ∈ pinned, P.assigned ξ ⊆ privateAvailable ξ

/-- `Ξ₃` is drawn from the entry family. -/
theorem three_subset_entries (P : Partition entries available) :
    P.three ⊆ entries := by
  intro ξ mem
  rw [← P.cover]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ mem)

/-- `Ξ₂` is drawn from the entry family. -/
theorem two_subset_entries (P : Partition entries available) :
    P.two ⊆ entries := by
  intro ξ mem
  rw [← P.cover]
  exact Finset.mem_union_left _ (Finset.mem_union_right _ mem)

/-- `Ξ_res` is drawn from the entry family. -/
theorem residual_subset_entries (P : Partition entries available) :
    P.residual ⊆ entries := by
  intro ξ mem
  rw [← P.cover]
  exact Finset.mem_union_right _ mem

/-- **`def:typeA-pressure-ledger`, existence of a clause-(L1) ledger**: when
every pinned entry holds at least three private incidences, private
availabilities lie in the common availability and are pairwise disjoint, the
ledger paying each pinned entry three private incidences and leaving every
other entry unassigned satisfies (L1)–(L5). -/
theorem exists_pinned (entries : Finset Index)
    (available : Index → Finset Carrier)
    (pinned : Finset Index) (privateAvailable : Index → Finset Carrier)
    (pinnedSubset : pinned ⊆ entries)
    (privateSubset : ∀ ξ ∈ pinned, privateAvailable ξ ⊆ available ξ)
    (privateLarge : ∀ ξ ∈ pinned, 3 ≤ (privateAvailable ξ).card)
    (privateDisjoint : ∀ ξ ∈ pinned, ∀ ζ ∈ pinned, ξ ≠ ζ →
      Disjoint (privateAvailable ξ) (privateAvailable ζ)) :
    ∃ P : Partition entries available, Pinned pinned privateAvailable P := by
  classical
  choose pick pickSubset pickCard using fun ξ (mem : ξ ∈ pinned) =>
    Finset.exists_subset_card_eq (privateLarge ξ mem)
  let pay : Index → Finset Carrier := fun ξ =>
    if mem : ξ ∈ pinned then pick ξ mem else ∅
  have payPinned : ∀ ξ (mem : ξ ∈ pinned), pay ξ = pick ξ mem :=
    fun ξ mem => dif_pos mem
  refine ⟨{ three := pinned
            two := ∅
            residual := entries \ pinned
            cover := by
              rw [Finset.union_empty, Finset.union_sdiff_of_subset pinnedSubset]
            three_disj_two := Finset.disjoint_empty_right _
            three_disj_residual := Finset.disjoint_sdiff
            two_disj_residual := Finset.disjoint_empty_left _
            assigned := pay
            assigned_available := ?_
            assigned_three := ?_
            assigned_two := ?_
            assigned_disjoint := ?_ }, Finset.Subset.refl _, ?_⟩
  · intro ξ mem
    rw [Finset.union_empty] at mem
    rw [payPinned ξ mem]
    exact (pickSubset ξ mem).trans (privateSubset ξ mem)
  · intro ξ mem
    rw [payPinned ξ mem]
    exact pickCard ξ mem
  · intro ξ mem
    exact absurd mem (Finset.notMem_empty ξ)
  · intro ξ ξMem ζ ζMem distinct
    rw [Finset.union_empty] at ξMem ζMem
    rw [payPinned ξ ξMem, payPinned ζ ζMem]
    exact (privateDisjoint ξ ξMem ζ ζMem distinct).mono (pickSubset ξ ξMem)
      (pickSubset ζ ζMem)
  · intro ξ mem
    show pay ξ ⊆ privateAvailable ξ
    rw [payPinned ξ mem]
    exact pickSubset ξ mem

/-- **`def:typeA-pressure-ledger`, the maximal choice**: among the
clause-(L1) ledgers, one maximizes first `N₃`, then `N₂`.  The manuscript's
lexicographically-first tie-break is immaterial to every later count; the
maximality of the pair is what the residual class carries. -/
theorem exists_maximal_pinned (entries : Finset Index)
    (available : Index → Finset Carrier)
    (pinned : Finset Index) (privateAvailable : Index → Finset Carrier)
    (pinnedSubset : pinned ⊆ entries)
    (privateSubset : ∀ ξ ∈ pinned, privateAvailable ξ ⊆ available ξ)
    (privateLarge : ∀ ξ ∈ pinned, 3 ≤ (privateAvailable ξ).card)
    (privateDisjoint : ∀ ξ ∈ pinned, ∀ ζ ∈ pinned, ξ ≠ ζ →
      Disjoint (privateAvailable ξ) (privateAvailable ζ)) :
    ∃ P : Partition entries available,
      Pinned pinned privateAvailable P ∧
        ∀ Q : Partition entries available, Pinned pinned privateAvailable Q →
          Q.three.card ≤ P.three.card ∧
            (Q.three.card = P.three.card → Q.two.card ≤ P.two.card) := by
  classical
  obtain ⟨base, basePinned⟩ := exists_pinned entries available pinned
    privateAvailable pinnedSubset privateSubset privateLarge privateDisjoint
  have valueLe : ∀ Q : Partition entries available,
      Q.three.card * (entries.card + 1) + Q.two.card ≤
        entries.card * (entries.card + 1) + entries.card := by
    intro Q
    exact Nat.add_le_add
      (mul_le_mul_left (Finset.card_le_card (three_subset_entries Q)) _)
      (Finset.card_le_card (two_subset_entries Q))
  have found := Nat.findGreatest_spec
    (P := fun value => ∃ P : Partition entries available,
      Pinned pinned privateAvailable P ∧
        P.three.card * (entries.card + 1) + P.two.card = value)
    (valueLe base) ⟨base, basePinned, rfl⟩
  obtain ⟨P, pinnedP, valueP⟩ := found
  refine ⟨P, pinnedP, ?_⟩
  intro Q pinnedQ
  have valueQLe : Q.three.card * (entries.card + 1) + Q.two.card ≤
      P.three.card * (entries.card + 1) + P.two.card := by
    rw [valueP]
    exact Nat.le_findGreatest
      (P := fun value => ∃ P : Partition entries available,
        Pinned pinned privateAvailable P ∧
          P.three.card * (entries.card + 1) + P.two.card = value)
      (valueLe Q) ⟨Q, pinnedQ, rfl⟩
  have twoLe : P.two.card ≤ entries.card :=
    Finset.card_le_card (two_subset_entries P)
  constructor
  · by_contra notLe
    have succLe : P.three.card + 1 ≤ Q.three.card :=
      Nat.succ_le_of_lt (Nat.lt_of_not_le notLe)
    have expanded : P.three.card * (entries.card + 1) + (entries.card + 1) ≤
        Q.three.card * (entries.card + 1) := by
      have := mul_le_mul_left succLe (entries.card + 1)
      rwa [Nat.succ_mul] at this
    have chain : P.three.card * (entries.card + 1) + (entries.card + 1) ≤
        P.three.card * (entries.card + 1) + entries.card :=
      expanded.trans ((Nat.le_add_right _ _).trans
        (valueQLe.trans (Nat.add_le_add_left twoLe _)))
    exact absurd (Nat.le_of_add_le_add_left chain) (Nat.not_succ_le_self _)
  · intro equal
    rw [equal] at valueQLe
    exact Nat.le_of_add_le_add_left valueQLe

/-! ### The weighted demand-defect split

`def:typeA-actual-profile-pressure-defects` and
`lem:typeA-pressure-defect-split`: each unpaid entry weighs `1` on `Ξ₂` and
`3` on `Ξ_res`, the external-demand defect is the total weight, and any
record-polarity predicate splits it exactly — `𝖯_ext = 𝖯_act + 𝖯_prof`.
Which predicate holds — membership in the actual-context record class — is
decided at the consuming row. -/

/-- `ω(ξ)`: the demand weight of an unpaid entry
(`def:typeA-actual-profile-pressure-defects`). -/
def demandWeight (P : Partition entries available) (ξ : Index) : Nat :=
  if ξ ∈ P.two then 1 else 3

/-- The external-demand defect is the total demand weight of `Ξ₂ ∪ Ξ_res`. -/
theorem externalDefect_eq_sum_demandWeight (P : Partition entries available) :
    P.externalDefect = ∑ ξ ∈ P.two ∪ P.residual, P.demandWeight ξ := by
  classical
  have twoSum : ∑ ξ ∈ P.two, P.demandWeight ξ = P.two.card * 1 :=
    Finset.sum_const_nat fun ξ mem => if_pos mem
  have residualSum : ∑ ξ ∈ P.residual, P.demandWeight ξ =
      P.residual.card * 3 :=
    Finset.sum_const_nat fun ξ mem =>
      if_neg (Finset.disjoint_right.mp P.two_disj_residual mem)
  rw [Finset.sum_union P.two_disj_residual, twoSum, residualSum]
  unfold externalDefect
  omega

/-- **`lem:typeA-pressure-defect-split`**: any record-polarity predicate
splits the external-demand defect exactly — no overlap, nothing dropped. -/
theorem externalDefect_split (P : Partition entries available)
    (Record : Index → Prop) [DecidablePred Record] :
    P.externalDefect =
      (∑ ξ ∈ (P.two ∪ P.residual).filter Record, P.demandWeight ξ) +
        ∑ ξ ∈ (P.two ∪ P.residual).filter (fun ξ => ¬ Record ξ),
          P.demandWeight ξ := by
  classical
  rw [externalDefect_eq_sum_demandWeight,
    ← Finset.sum_filter_add_sum_filter_not (P.two ∪ P.residual) Record]

/-! ### Demand units and the absorbed open count

`def:typeA-pressure-absorbers` and
`lem:typeA-pressure-absorber-no-overcount`: one demand unit per weight point
of each unpaid entry, `|𝒰_press| = 𝖯_ext`; a type-(A1) absorption assigns
single-use fresh supply incidences to some units, a type-(A2) set holds the
dependence-certificate absorptions, and the open demand is what remains.  The
no-overcount display is `3Ñ ≤ |supply| + B_dep + 𝖯_open` — subtraction-free
for `3Ñ − 𝖯_open ≤ def⁺(R) + B_dep`, with `B_dep = 0` on the branch where
every type-(A2) certificate has routed. -/

/-- `𝒰_press`: the demand units of the unpaid classes
(`def:typeA-pressure-absorbers`). -/
def demandUnits (P : Partition entries available) : Finset (Index × Nat) :=
  (P.two ∪ P.residual).biUnion fun ξ =>
    (Finset.range (P.demandWeight ξ)).image fun j => (ξ, j)

/-- `|𝒰_press| = 𝖯_ext`. -/
theorem card_demandUnits (P : Partition entries available) :
    P.demandUnits.card = P.externalDefect := by
  classical
  have blocks : ∀ ξ ∈ P.two ∪ P.residual,
      (((Finset.range (P.demandWeight ξ)).image fun j => (ξ, j)).card) =
        P.demandWeight ξ := by
    intro ξ _mem
    rw [Finset.card_image_of_injective _ fun a b eq =>
      (Prod.mk.injEq ξ a ξ b).mp eq |>.2]
    exact Finset.card_range _
  have disjointBlocks : ∀ ξ ∈ P.two ∪ P.residual, ∀ ζ ∈ P.two ∪ P.residual,
      ξ ≠ ζ →
      Disjoint ((Finset.range (P.demandWeight ξ)).image fun j => (ξ, j))
        ((Finset.range (P.demandWeight ζ)).image fun j => (ζ, j)) := by
    intro ξ _ ζ _ distinct
    rw [Finset.disjoint_left]
    rintro ⟨entry, j⟩ leftMem rightMem
    obtain ⟨_, _, eqL⟩ := Finset.mem_image.mp leftMem
    obtain ⟨_, _, eqR⟩ := Finset.mem_image.mp rightMem
    exact distinct ((((Prod.mk.injEq _ _ _ _).mp eqL).1).trans
      (((Prod.mk.injEq _ _ _ _).mp eqR).1).symm)
  rw [demandUnits, Finset.card_biUnion disjointBlocks,
    externalDefect_eq_sum_demandWeight]
  exact Finset.sum_congr rfl blocks

/-- A demand unit's entry lies in the unpaid classes `Ξ₂ ∪ Ξ_res`. -/
theorem fst_mem_of_mem_demandUnits {P : Partition entries available}
    {unit : Index × Nat} (member : unit ∈ P.demandUnits) :
    unit.1 ∈ P.two ∪ P.residual := by
  classical
  obtain ⟨ξ, ξMem, imageMem⟩ := Finset.mem_biUnion.mp member
  obtain ⟨j, _jMem, unitEq⟩ := Finset.mem_image.mp imageMem
  rw [← unitEq]
  exact ξMem

/-- **`lem:typeA-pressure-absorber-no-overcount`**: with a type-(A1)
absorption `A` on demand units (fresh single-use supply incidences) and a
disjoint type-(A2) absorbed set `dep`, the open demand
`𝖯_open = |𝒰_press ∖ (absorbed ∪ dep)|` satisfies
`3Ñ ≤ |supply| + B_dep + 𝖯_open`. -/
theorem three_mul_card_le_of_absorption
    {P : Partition entries available} [DecidableEq Carrier]
    (supply : Finset Carrier)
    (supplied : ∀ ξ ∈ P.three ∪ P.two, P.assigned ξ ⊆ supply)
    (A : Absorption P (Index × Nat))
    (absorbedUnits : A.absorbed ⊆ P.demandUnits)
    (absorberSupplied : ∀ υ ∈ A.absorbed, A.absorber υ ∈ supply)
    (dep : Finset (Index × Nat)) (depUnits : dep ⊆ P.demandUnits)
    (depDisjoint : Disjoint A.absorbed dep) :
    3 * entries.card ≤
      supply.card + dep.card +
        (P.demandUnits \ (A.absorbed ∪ dep)).card := by
  classical
  have raw := A.three_mul_add_two_mul_add_card_le supply supplied
    absorberSupplied
  have classes := P.card_entries_eq
  have unitsCard := P.card_demandUnits
  have absorbedAll : A.absorbed ∪ dep ⊆ P.demandUnits :=
    Finset.union_subset absorbedUnits depUnits
  have unitSplit := Finset.card_sdiff_add_card_eq_card absorbedAll
  have unionCard : (A.absorbed ∪ dep).card = A.absorbed.card + dep.card :=
    Finset.card_union_of_disjoint depDisjoint
  unfold externalDefect at unitsCard
  omega

/-- **`def:typeA-pressure-absorbers`, the maximal choice**: with the
type-(A2) absorbed set held fixed, among the single-use fresh type-(A1)
absorptions disjoint from it one maximizes the number of absorbed units.
Once the type-(A2) set is held, the manuscript's order — first the total
absorbed count, then the type-(A1) count — is carried entirely by the
type-(A1) count, and the lexicographically-first tie-break is immaterial to
every later count, exactly as in `exists_maximal_pinned`. -/
theorem exists_maximal_absorption {P : Partition entries available}
    {Unit : Type*} (units : Finset Unit) (supply : Finset Carrier)
    (dep : Finset Unit) (fallback : Unit → Carrier) :
    ∃ A : Absorption P Unit,
      A.absorbed ⊆ units ∧
        (∀ υ ∈ A.absorbed, A.absorber υ ∈ supply) ∧
        Disjoint A.absorbed dep ∧
        ∀ B : Absorption P Unit, B.absorbed ⊆ units →
          (∀ υ ∈ B.absorbed, B.absorber υ ∈ supply) →
          Disjoint B.absorbed dep →
          B.absorbed.card ≤ A.absorbed.card := by
  classical
  let base : Absorption P Unit :=
    { absorbed := ∅
      absorber := fallback
      absorber_injective := fun υ mem => absurd mem (Finset.notMem_empty υ)
      absorber_unused := fun υ mem => absurd mem (Finset.notMem_empty υ) }
  have baseAdmissible : base.absorbed ⊆ units ∧
      (∀ υ ∈ base.absorbed, base.absorber υ ∈ supply) ∧
      Disjoint base.absorbed dep :=
    ⟨Finset.empty_subset units,
      fun υ mem => absurd mem (Finset.notMem_empty υ),
      Finset.disjoint_empty_left dep⟩
  have valueLe : ∀ B : Absorption P Unit, B.absorbed ⊆ units →
      B.absorbed.card ≤ units.card :=
    fun B sub => Finset.card_le_card sub
  have found := Nat.findGreatest_spec
    (P := fun value => ∃ A : Absorption P Unit,
      (A.absorbed ⊆ units ∧ (∀ υ ∈ A.absorbed, A.absorber υ ∈ supply) ∧
        Disjoint A.absorbed dep) ∧ A.absorbed.card = value)
    (valueLe base baseAdmissible.1) ⟨base, baseAdmissible, rfl⟩
  obtain ⟨A, ⟨absorbedUnits, absorberSupplied, absorbedDisjoint⟩, valueA⟩ :=
    found
  refine ⟨A, absorbedUnits, absorberSupplied, absorbedDisjoint, ?_⟩
  intro B unitsB suppliedB disjointB
  have boundB := Nat.le_findGreatest
    (P := fun value => ∃ A : Absorption P Unit,
      (A.absorbed ⊆ units ∧ (∀ υ ∈ A.absorbed, A.absorber υ ∈ supply) ∧
        Disjoint A.absorbed dep) ∧ A.absorbed.card = value)
    (valueLe B unitsB) ⟨B, ⟨unitsB, suppliedB, disjointB⟩, rfl⟩
  rw [← valueA] at boundB
  exact boundB

end Partition

/-! ### The base/zero exhaustion of the open demand

`lem:typeA-window-blocker-accounting-audit` and
`lem:typeA-final-open-pressure-exhaustion`, generically: assigning every open
unit to a unique window, and given that every window holding three or more
open units is zero-signature (the branch of
`lem:typeA-routed-overload-not-open` after `lem:typeA-window-shadow-hit-routes`
has removed every recorded-hit overload), the open demand splits into a base
class of at most two units per window and a zero class of size exactly the
zero-signature excess `𝖯_zero⁺` — so `𝖯_open ≤ 2p + 𝖯_zero⁺`
(`lem:typeA-open-pressure-zero-shadow-excess`).  Which windows are
zero-signature is branch data at the consuming row;
`lem:typeA-primitive-excess-zero-shadow` is `Finset.filter_congr` on the
branch equivalence of the two window predicates. -/

/-- **`lem:typeA-final-open-pressure-exhaustion`, the partition**: base units
(at most two per window) and zero units (exactly the zero-signature
excess). -/
theorem exists_base_zero_partition {Unit Window : Type*}
    [DecidableEq Unit] [DecidableEq Window]
    (units : Finset Unit) (windows : Finset Window) (blocker : Unit → Window)
    (assigned : ∀ υ ∈ units, blocker υ ∈ windows)
    (Zero : Window → Prop) [DecidablePred Zero]
    (overloadZero : ∀ P ∈ windows,
      3 ≤ (units.filter fun υ => blocker υ = P).card → Zero P) :
    ∃ base zero : Finset Unit,
      Disjoint base zero ∧ base ∪ zero = units ∧
        base.card ≤ 2 * windows.card ∧
        zero.card = ∑ P ∈ windows.filter Zero,
          ((units.filter fun υ => blocker υ = P).card - 2) := by
  classical
  choose pick pickSubset pickCard using fun P : Window =>
    Finset.exists_subset_card_eq
      (Nat.min_le_right 2 ((units.filter fun υ => blocker υ = P).card))
  have pickUnits : ∀ P : Window, pick P ⊆ units := fun P =>
    (pickSubset P).trans (Finset.filter_subset _ _)
  have picksDisjoint : ∀ P ∈ windows, ∀ Q ∈ windows, P ≠ Q →
      Disjoint (pick P) (pick Q) := by
    intro P _ Q _ distinct
    refine Finset.disjoint_left.mpr fun υ pMem qMem => ?_
    have pFibre := Finset.mem_filter.mp (pickSubset P pMem)
    have qFibre := Finset.mem_filter.mp (pickSubset Q qMem)
    exact distinct (pFibre.2.symm.trans qFibre.2)
  refine ⟨windows.biUnion pick, units \ windows.biUnion pick,
    Finset.disjoint_sdiff, ?_, ?_, ?_⟩
  · exact Finset.union_sdiff_of_subset
      (Finset.biUnion_subset.mpr fun P _ => pickUnits P)
  · rw [Finset.card_biUnion picksDisjoint]
    calc ∑ P ∈ windows, (pick P).card
        ≤ ∑ _P ∈ windows, 2 :=
          Finset.sum_le_sum fun P _ => by rw [pickCard P]; exact Nat.min_le_left _ _
      _ = 2 * windows.card := by
          rw [Finset.sum_const_nat fun _ _ => rfl]
          omega
  · have baseSubset : windows.biUnion pick ⊆ units :=
      Finset.biUnion_subset.mpr fun P _ => pickUnits P
    have sdiffCard := Finset.card_sdiff_add_card_eq_card baseSubset
    have unitsCard := card_eq_sum_fibres units windows blocker assigned
    have baseCard : (windows.biUnion pick).card =
        ∑ P ∈ windows, min 2 ((units.filter fun υ => blocker υ = P).card) := by
      rw [Finset.card_biUnion picksDisjoint]
      exact Finset.sum_congr rfl fun P _ => pickCard P
    have fibreSplit : ∀ P ∈ windows,
        (units.filter fun υ => blocker υ = P).card =
          min 2 ((units.filter fun υ => blocker υ = P).card) +
            ((units.filter fun υ => blocker υ = P).card -
              min 2 ((units.filter fun υ => blocker υ = P).card)) := by
      intro P _
      omega
    have excessEq : ∀ P ∈ windows,
        (units.filter fun υ => blocker υ = P).card -
            min 2 ((units.filter fun υ => blocker υ = P).card) =
          (if Zero P
            then (units.filter fun υ => blocker υ = P).card - 2 else 0) := by
      intro P memP
      by_cases zero : Zero P
      · rw [if_pos zero]
        omega
      · rw [if_neg zero]
        have small : (units.filter fun υ => blocker υ = P).card ≤ 2 := by
          by_contra large
          exact zero (overloadZero P memP (by omega))
        omega
    have sumSplit : ∑ P ∈ windows, (units.filter fun υ => blocker υ = P).card =
        (∑ P ∈ windows,
            min 2 ((units.filter fun υ => blocker υ = P).card)) +
          ∑ P ∈ windows,
            ((units.filter fun υ => blocker υ = P).card -
              min 2 ((units.filter fun υ => blocker υ = P).card)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fibreSplit
    have excessSum : ∑ P ∈ windows,
        ((units.filter fun υ => blocker υ = P).card -
          min 2 ((units.filter fun υ => blocker υ = P).card)) =
        ∑ P ∈ windows.filter Zero,
          ((units.filter fun υ => blocker υ = P).card - 2) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl excessEq
    omega

/-- **`lem:typeA-open-pressure-zero-shadow-excess`**:
`𝖯_open ≤ 2p + 𝖯_zero⁺` on the branch where every overloaded window is
zero-signature. -/
theorem card_le_two_mul_card_add_zero_excess {Unit Window : Type*}
    [DecidableEq Unit] [DecidableEq Window]
    (units : Finset Unit) (windows : Finset Window) (blocker : Unit → Window)
    (assigned : ∀ υ ∈ units, blocker υ ∈ windows)
    (Zero : Window → Prop) [DecidablePred Zero]
    (overloadZero : ∀ P ∈ windows,
      3 ≤ (units.filter fun υ => blocker υ = P).card → Zero P) :
    units.card ≤ 2 * windows.card +
      ∑ P ∈ windows.filter Zero,
        ((units.filter fun υ => blocker υ = P).card - 2) := by
  classical
  obtain ⟨base, zero, disjoint, cover, baseCard, zeroCard⟩ :=
    exists_base_zero_partition units windows blocker assigned Zero overloadZero
  have coverCard : units.card = base.card + zero.card := by
    rw [← cover, Finset.card_union_of_disjoint disjoint]
  omega

/-- **`lem:typeA-same-window-cap-overload-excess`, the count**: under the
same-window two-blocker cap (`def:typeA-same-window-open-blocker-cap` — after
deleting an exceptional set, every window keeps at most two open units), the
total overload excess is at most the exceptional count; the sublinearity
`o(R)` of the exceptional set is a registered reading at the consuming row,
and the primitive and zero-signature excesses are bounded by this total since
their windows are subfamilies. -/
theorem excess_le_card_exceptional {Unit Window : Type*}
    [DecidableEq Unit] [DecidableEq Window]
    (units : Finset Unit) (windows : Finset Window) (blocker : Unit → Window)
    (assigned : ∀ υ ∈ units, blocker υ ∈ windows)
    (exceptional : Finset Unit) (exceptionalUnits : exceptional ⊆ units)
    (cap : ∀ P ∈ windows,
      ((units \ exceptional).filter fun υ => blocker υ = P).card ≤ 2) :
    ∑ P ∈ windows, ((units.filter fun υ => blocker υ = P).card - 2) ≤
      exceptional.card := by
  classical
  have exceptionalCard : exceptional.card =
      ∑ P ∈ windows, (exceptional.filter fun υ => blocker υ = P).card :=
    card_eq_sum_fibres exceptional windows blocker
      fun υ mem => assigned υ (exceptionalUnits mem)
  rw [exceptionalCard]
  refine Finset.sum_le_sum fun P memP => ?_
  have fibreSplit : (units.filter fun υ => blocker υ = P).card ≤
      ((units \ exceptional).filter fun υ => blocker υ = P).card +
        (exceptional.filter fun υ => blocker υ = P).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      Finset.disjoint_sdiff.symm)]
    refine Finset.card_le_card fun υ mem => ?_
    obtain ⟨uMem, bEq⟩ := Finset.mem_filter.mp mem
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases exc : υ ∈ exceptional
    · exact Or.inr ⟨exc, bEq⟩
    · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨uMem, exc⟩, bEq⟩
  have := cap P memP
  omega

end Hypostructure.Graph.DemandPartition
