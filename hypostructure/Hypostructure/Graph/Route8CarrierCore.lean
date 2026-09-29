import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Graph.Response
import Hypostructure.Graph.Route8Carrier

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

section IndexedCoreAccounting

variable {Carrier Index : Type u}
variable [DecidableEq Carrier] [DecidableEq Index]

/-- The carriers private to one indexed entry, counted inside the selected
essential-core family and not in a secondary entry object. -/
noncomputable def indexedPrivateCoreCarriers
    (entries : Finset Index) (core : Index → Finset Carrier)
    (index : Index) : Finset Carrier :=
  (core index).filter fun carrier =>
    ∀ other ∈ entries, other ≠ index → carrier ∉ core other

/-- The private essential-carrier count `π_X(ξ)`. -/
noncomputable def indexedPrivateCoreCount
    (entries : Finset Index) (core : Index → Finset Carrier)
    (index : Index) : Nat :=
  (indexedPrivateCoreCarriers entries core index).card

/-- The terminal two-carrier condition of node `[117]`, stated on the selected
indexed core family. -/
def IndexedTwoCarrierCore
    (entries : Finset Index) (core : Index → Finset Carrier)
    (threshold : Nat) (index : Index) : Prop :=
  indexedPrivateCoreCount entries core index ≤ threshold

theorem indexedPrivateCoreCarriers_subset_core
    (entries : Finset Index) (core : Index → Finset Carrier)
    (index : Index) :
    indexedPrivateCoreCarriers entries core index ⊆ core index := by
  intro carrier hcarrier
  exact (Finset.mem_filter.mp hcarrier).1

theorem indexedPrivateCoreCarriers_subset_supply
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {index : Index} (index_mem : index ∈ entries) :
    indexedPrivateCoreCarriers entries core index ⊆ supply := by
  exact subset_trans (indexedPrivateCoreCarriers_subset_core entries core index)
    (core_subset index index_mem)

theorem indexedPrivateCoreCarriers_disjoint
    (entries : Finset Index) (core : Index → Finset Carrier)
    {left right : Index} (left_mem : left ∈ entries)
    (right_mem : right ∈ entries) (distinct : left ≠ right) :
    Disjoint (indexedPrivateCoreCarriers entries core left)
      (indexedPrivateCoreCarriers entries core right) := by
  rw [Finset.disjoint_left]
  intro carrier hleft hright
  have hleft_private := (Finset.mem_filter.mp hleft).2
  exact hleft_private right right_mem (fun same => distinct same.symm)
    ((indexedPrivateCoreCarriers_subset_core entries core right) hright)

theorem indexedPrivateCoreCarriers_card_biUnion_le_supply
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply) :
    (entries.biUnion fun index =>
      indexedPrivateCoreCarriers entries core index).card ≤ supply.card := by
  refine Finset.card_le_card ?_
  intro carrier hcarrier
  rcases Finset.mem_biUnion.mp hcarrier with ⟨index, index_mem, carrier_mem⟩
  exact indexedPrivateCoreCarriers_subset_supply entries core supply core_subset
    index_mem carrier_mem

theorem indexedPrivateCoreCarriers_card_sum_le_supply
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply) :
    (∑ index ∈ entries, indexedPrivateCoreCount entries core index) ≤
      supply.card := by
  change (∑ index ∈ entries,
      (indexedPrivateCoreCarriers entries core index).card) ≤ supply.card
  rw [← Finset.card_biUnion]
  · exact indexedPrivateCoreCarriers_card_biUnion_le_supply entries core
      supply core_subset
  intro left left_mem right right_mem distinct
  exact indexedPrivateCoreCarriers_disjoint entries core left_mem right_mem
    distinct

theorem indexedCoreCardMul_le_supply
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {floor : Nat}
    (lower :
      ∀ index ∈ entries, floor ≤ indexedPrivateCoreCount entries core index) :
    floor * entries.card ≤ supply.card := by
  calc
    floor * entries.card
        = ∑ _index ∈ entries, floor := by
          rw [Finset.sum_const]
          simpa [mul_comm]
    _ ≤ ∑ index ∈ entries, indexedPrivateCoreCount entries core index := by
          exact Finset.sum_le_sum fun index index_mem => lower index index_mem
    _ ≤ supply.card :=
          indexedPrivateCoreCarriers_card_sum_le_supply entries core supply
            core_subset

/-- The integer squeeze used by the route-`8` carrier reduction. -/
theorem privateCarrierCensus_contradiction
    {floor discharge basins supply ambient : Nat}
    (deficit : ambient ≤ basins + discharge * supply)
    (budget : floor * basins ≤ supply)
    (rate : (floor * discharge + 1) * supply < floor * ambient) :
    False := by
  have scaled :
      floor * ambient ≤ floor * basins + floor * (discharge * supply) := by
    have step : floor * ambient ≤ floor * (basins + discharge * supply) :=
      Nat.mul_le_mul_left _ deficit
    rwa [Nat.mul_add] at step
  have assoc : floor * (discharge * supply) = floor * discharge * supply :=
    (mul_assoc _ _ _).symm
  rw [assoc] at scaled
  have expand : (floor * discharge + 1) * supply =
      floor * discharge * supply + supply := by
    rw [add_mul, one_mul]
  omega

/-- The node-`[117]` carrier-reduction squeeze, stated directly on the selected
indexed essential-core family. -/
theorem exists_indexedTwoCarrierCore
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold discharge ambient : Nat}
    (deficit : ambient ≤ entries.card + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient) :
    ∃ index ∈ entries, IndexedTwoCarrierCore entries core threshold index := by
  classical
  by_contra missing
  simp only [not_exists, not_and] at missing
  have lower :
      ∀ index ∈ entries,
        threshold + 1 ≤ indexedPrivateCoreCount entries core index := by
    intro index index_mem
    have not_two : ¬ IndexedTwoCarrierCore entries core threshold index :=
      missing index index_mem
    unfold IndexedTwoCarrierCore at not_two
    omega
  exact privateCarrierCensus_contradiction deficit
    (indexedCoreCardMul_le_supply entries core supply core_subset lower) rate

/-- The no-two-carrier branch of node `[119]`: every indexed entry has at
least `threshold + 1` private essential carriers. -/
theorem privateCarrierLower_of_noTwoCarrier
    (entries : Finset Index) (core : Index → Finset Carrier)
    {threshold : Nat}
    (noTwo :
      ∀ index ∈ entries,
        ¬ IndexedTwoCarrierCore entries core threshold index) :
    ∀ index ∈ entries,
      threshold + 1 ≤ indexedPrivateCoreCount entries core index := by
  intro index index_mem
  have not_two := noTwo index index_mem
  unfold IndexedTwoCarrierCore at not_two
  omega

/-- Nodes `[119]`--`[120]`: the no-two-carrier branch gives the private-carrier
budget bound against the single carrier supply. -/
theorem privateCarrierBudget_of_noTwoCarrier
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold : Nat}
    (noTwo :
      ∀ index ∈ entries,
        ¬ IndexedTwoCarrierCore entries core threshold index) :
    (threshold + 1) * entries.card ≤ supply.card :=
  indexedCoreCardMul_le_supply entries core supply core_subset
    (privateCarrierLower_of_noTwoCarrier entries core noTwo)

/-- Nodes `[121]`--`[122]`: the private-carrier budget contradicts the
selected burden/deficit inequality and registered rate bound. -/
theorem noTwoCarrier_contradiction
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold discharge ambient : Nat}
    (deficit : ambient ≤ entries.card + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient)
    (noTwo :
      ∀ index ∈ entries,
        ¬ IndexedTwoCarrierCore entries core threshold index) :
    False :=
  privateCarrierCensus_contradiction deficit
    (privateCarrierBudget_of_noTwoCarrier entries core supply core_subset noTwo)
    rate

/-- The reusable theorem package for node `[117]`: any concrete route-`8`
indexed core family satisfying the selected burden/deficit/rate readings has a
two-carrier entry. -/
def TwoCarrierReductionFacts : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold discharge ambient : Nat}
    (deficit : ambient ≤ entries.card + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient),
      ∃ index ∈ entries, IndexedTwoCarrierCore entries core threshold index

/-- The reusable theorem package for nodes `[119]`--`[120]`: no selected
two-carrier entry forces the private essential-carrier budget. -/
def PrivateCarrierBudgetFacts : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold : Nat},
      (∀ index ∈ entries,
        ¬ IndexedTwoCarrierCore entries core threshold index) →
      (threshold + 1) * entries.card ≤ supply.card

/-- The reusable theorem package for nodes `[121]`--`[122]`: no selected
two-carrier entry is incompatible with the route-`8` burden/deficit and rate
readings. -/
def NoTwoCarrierContradictionFacts : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    (supply : Finset Carrier)
    (core_subset : ∀ index ∈ entries, core index ⊆ supply)
    {threshold discharge ambient : Nat}
    (deficit : ambient ≤ entries.card + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient),
      (∀ index ∈ entries,
        ¬ IndexedTwoCarrierCore entries core threshold index) →
      False

theorem twoCarrierReductionFacts :
    TwoCarrierReductionFacts (Carrier := Carrier) := by
  intro Index indexDec entries core supply core_subset threshold discharge
    ambient deficit rate
  letI : DecidableEq Index := indexDec
  exact exists_indexedTwoCarrierCore entries core supply core_subset deficit rate

theorem privateCarrierBudgetFacts :
    PrivateCarrierBudgetFacts (Carrier := Carrier) := by
  intro Index indexDec entries core supply core_subset threshold noTwo
  letI : DecidableEq Index := indexDec
  exact privateCarrierBudget_of_noTwoCarrier entries core supply core_subset
    noTwo

theorem noTwoCarrierContradictionFacts :
    NoTwoCarrierContradictionFacts (Carrier := Carrier) := by
  intro Index indexDec entries core supply core_subset threshold discharge
    ambient deficit rate noTwo
  letI : DecidableEq Index := indexDec
  exact noTwoCarrier_contradiction entries core supply core_subset deficit
    rate noTwo

end IndexedCoreAccounting

section TerminalTwoCarrier

variable {Target : FiniteObject.{u} → Prop}
variable {Carrier Index : Type u}
variable [DecidableEq Carrier] [DecidableEq Index]
variable (entry : Entry Target Carrier)

/-- The node-`[118]` carrier-deletion witness package for one already selected
two-carrier indexed core.  It contains no route-`8` collection carrier: the
index, core family, and two-carrier fact are the concrete facts read from the
ledger by the caller.  A deletion witness is a realization of the deleted
restriction (for a graph-owned entry, a piece constructed from G at `B_u`)
whose target truth in the entry's actual surroundings `G − B_u` differs from
the full reading's. -/
def TwoCarrierDeletionWitnesses
    (entries : Finset Index) (core : Index → Finset Carrier)
    (threshold : Nat) (index : Index) : Prop :=
  IndexedTwoCarrierCore entries core threshold index ∧
    ∀ carrier ∈ core index,
      (∃ ρ : entry.Realization,
        entry.Realizes (entry.retained ((core index).erase carrier)) ρ ∧
          ¬ (Target (glue (entry.realize ρ) entry.actual) ↔
            Target (glue entry.full entry.actual))) ∧
      ∃ r ∈ entry.coordinates, entry.car r ⊆ core index ∧ carrier ∈ entry.car r

/-- The canonical deletion witnesses attached to a selected two-carrier core.

This is `lem:typeA-essential-deletion-witness` and
`lem:typeA-deletion-witness-declared`: once the selected indexed core is
identified with the canonical essential core of the selected reading, every
essential carrier has a realization of the deleted restriction separated from
the full reading, and a declared forgotten coordinate whose carrier support
contains it. -/
theorem twoCarrierDeletionWitnesses
    (entries : Finset Index) (core : Index → Finset Carrier)
    {threshold : Nat} {index : Index}
    (two : IndexedTwoCarrierCore entries core threshold index)
    (core_eq : core index = entry.essentialCore) :
    TwoCarrierDeletionWitnesses entry entries core threshold index := by
  refine ⟨two, ?_⟩
  intro carrier member
  rw [core_eq] at member ⊢
  exact ⟨entry.exists_deletion_witness member,
    entry.exists_forgotten_coordinate member⟩

/-- The reusable theorem package for node `[118]`. -/
def TwoCarrierDeletionWitnessFacts : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    {threshold : Nat} {index : Index},
      IndexedTwoCarrierCore entries core threshold index →
      core index = entry.essentialCore →
      TwoCarrierDeletionWitnesses entry entries core threshold index

theorem twoCarrierDeletionWitnessFacts :
    TwoCarrierDeletionWitnessFacts entry := by
  intro Index indexDec entries core threshold index two core_eq
  letI : DecidableEq Index := indexDec
  exact twoCarrierDeletionWitnesses entry entries core two core_eq

end TerminalTwoCarrier

end Hypostructure.Graph.Route8
