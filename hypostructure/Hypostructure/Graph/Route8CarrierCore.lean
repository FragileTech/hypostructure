import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Graph.ExitFourFamily
import Hypostructure.Graph.Response

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

section Core

variable {Target : FiniteObject.{u} → Prop}
variable {Carrier Coordinate : Type u}
variable [DecidableEq Carrier] [DecidableEq Coordinate]
variable {boundary : Boundary.{u}}
variable (carrierSupply : Enumeration Carrier)
variable (coordinates : Finset Coordinate)
variable (car : Coordinate → Finset Carrier)
variable (car_subset : ∀ r ∈ coordinates, car r ⊆ carrierSupply.toFinset)
variable (state : Finset Coordinate → BoundaryPiece boundary)

/-- The declared coordinates retained by the carrier restriction to `D`. -/
def retained (D : Finset Carrier) : Finset Coordinate :=
  let _carrierSupply : Enumeration Carrier := carrierSupply
  coordinates.filter fun r => car r ⊆ D

theorem mem_retained {D : Finset Carrier} {r : Coordinate} :
    r ∈ retained carrierSupply coordinates car D ↔
      r ∈ coordinates ∧ car r ⊆ D := by
  simp [retained]

theorem retained_mono {D E : Finset Carrier} (subset : D ⊆ E) :
    retained carrierSupply coordinates car D ⊆
      retained carrierSupply coordinates car E := by
  intro r member
  rw [mem_retained] at member ⊢
  exact ⟨member.1, member.2.trans subset⟩

/-- The boundary reading restricted to the carrier set `D`. -/
def restriction (D : Finset Carrier) : BoundaryPiece boundary :=
  state (retained carrierSupply coordinates car D)

include car_subset

/-- Restricting to the whole carrier supply retains every declared coordinate. -/
theorem retained_carrierSupply :
    retained carrierSupply coordinates car carrierSupply.toFinset =
      coordinates := by
  apply Finset.ext
  intro r
  rw [mem_retained]
  exact ⟨fun member => member.1, fun member => ⟨member, car_subset r member⟩⟩

@[simp] theorem restriction_carrierSupply :
    restriction carrierSupply coordinates car state carrierSupply.toFinset =
      state coordinates := by
  rw [restriction, retained_carrierSupply (car_subset := car_subset)]

omit car_subset

/-- A carrier set is complete when its restriction is target-equivalent to the
full reading against every outside context. -/
def Complete (D : Finset Carrier) : Prop :=
  Response.ContextEquivalent Target
    (restriction carrierSupply coordinates car state D) (state coordinates)

include car_subset

theorem complete_carrierSupply :
    Complete (Target := Target) carrierSupply coordinates car state
      carrierSupply.toFinset := by
  intro outside
  rw [restriction_carrierSupply (car_subset := car_subset)]

theorem retained_erase_of_not_mem {D : Finset Carrier} {carrier : Carrier}
    (outside : carrier ∉ carrierSupply.toFinset) :
    retained carrierSupply coordinates car (D.erase carrier) =
      retained carrierSupply coordinates car D := by
  refine Finset.Subset.antisymm
    (retained_mono carrierSupply coordinates car (Finset.erase_subset _ _)) ?_
  intro r member
  rw [mem_retained] at member ⊢
  refine ⟨member.1, ?_⟩
  intro other used
  refine Finset.mem_erase.mpr ⟨?_, member.2 used⟩
  intro same
  exact outside (same ▸ car_subset r member.1 used)

/-- Core's finite inclusion-minimal complete-carrier selector, applied to the
declared reading arguments. -/
noncomputable def carrierProfile : EssentialCarrier.Profile.{u} where
  Carrier := Carrier
  schedule := carrierSupply
  Complete := Complete (Target := Target) carrierSupply coordinates car state
  completeDecidable := fun _ => Classical.propDecidable _
  fullComplete := complete_carrierSupply (Target := Target)
    carrierSupply coordinates car (car_subset := car_subset) state

/-- The canonical essential carrier core. -/
noncomputable def essentialCore : Finset Carrier :=
  (carrierProfile (Target := Target) carrierSupply coordinates car
    (car_subset := car_subset) state).core

theorem essentialCore_complete :
    Complete (Target := Target) carrierSupply coordinates car state
      (essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state) :=
  (carrierProfile (Target := Target) carrierSupply coordinates car
    (car_subset := car_subset) state).core_complete

theorem essentialCore_erase_not_complete {carrier : Carrier}
    (member :
      carrier ∈
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) :
    ¬ Complete (Target := Target) carrierSupply coordinates car state
      ((essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state).erase
        carrier) := by
  letI : DecidableEq
      (carrierProfile (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state).Carrier :=
    ‹DecidableEq Carrier›
  exact (carrierProfile (Target := Target) carrierSupply coordinates car
    (car_subset := car_subset) state)
    |>.erase_not_complete carrier member

theorem essentialCore_subset_carrierSupply :
    essentialCore (Target := Target) carrierSupply coordinates car
      (car_subset := car_subset) state ⊆
      carrierSupply.toFinset := by
  intro carrier member
  by_contra outside
  refine essentialCore_erase_not_complete (Target := Target)
    carrierSupply coordinates car (car_subset := car_subset) state member ?_
  intro context
  have same := retained_erase_of_not_mem carrierSupply coordinates car
    (car_subset := car_subset)
    (D := essentialCore (Target := Target) carrierSupply coordinates car
      (car_subset := car_subset) state)
    outside
  have rewritten :
      restriction carrierSupply coordinates car state
          ((essentialCore (Target := Target) carrierSupply coordinates car
              (car_subset := car_subset) state).erase
            carrier) =
        restriction carrierSupply coordinates car state
          (essentialCore (Target := Target) carrierSupply coordinates car
            (car_subset := car_subset) state) := by
    rw [restriction, restriction, same]
  rw [rewritten]
  exact essentialCore_complete (Target := Target) carrierSupply coordinates car
    (car_subset := car_subset) state context

theorem deletion_targetDefect {carrier : Carrier}
    (member :
      carrier ∈
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) :
    Response.TargetDefect Target
      (restriction carrierSupply coordinates car state
        ((essentialCore (Target := Target) carrierSupply coordinates car
            (car_subset := car_subset) state).erase
          carrier))
      (restriction carrierSupply coordinates car state
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state)) := by
  refine Response.targetDefect_of_not_contextEquivalent ?_
  intro equivalent
  refine essentialCore_erase_not_complete (Target := Target)
    carrierSupply coordinates car (car_subset := car_subset) state member ?_
  intro outside
  exact (equivalent outside).trans
    (essentialCore_complete (Target := Target) carrierSupply coordinates car
      (car_subset := car_subset) state outside)

theorem retained_erase_ne {carrier : Carrier}
    (member :
      carrier ∈
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) :
    retained carrierSupply coordinates car
        ((essentialCore (Target := Target) carrierSupply coordinates car
            (car_subset := car_subset) state).erase
          carrier) ≠
      retained carrierSupply coordinates car
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) := by
  intro same
  obtain ⟨outside, separates⟩ := deletion_targetDefect (Target := Target)
    carrierSupply coordinates car (car_subset := car_subset) state member
  exact separates (by rw [restriction, restriction, same])

theorem exists_forgotten_coordinate {carrier : Carrier}
    (member :
      carrier ∈
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) :
    ∃ r ∈ coordinates,
      car r ⊆
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state ∧
      carrier ∈ car r := by
  classical
  by_contra missing
  simp only [not_exists, not_and] at missing
  refine retained_erase_ne (Target := Target) carrierSupply coordinates car state
    (car_subset := car_subset) member (Finset.Subset.antisymm ?_ ?_)
  · exact retained_mono carrierSupply coordinates car (Finset.erase_subset _ _)
  · intro r inCore
    rw [mem_retained] at inCore ⊢
    refine ⟨inCore.1, ?_⟩
    intro other used
    refine Finset.mem_erase.mpr ⟨?_, inCore.2 used⟩
    intro same
    exact missing r inCore.1 inCore.2 (same ▸ used)

/-- A retained crossing coordinate forces at least two carriers in the core.

This is the raw carrier-core form of the cut-parity input used by the
zero/one-carrier collapse: if every coordinate in `crossing` uses at least two
carriers, then a core of cardinality at most one retains none of them. -/
theorem not_mem_retained_of_core_card_le_one {crossing : Finset Coordinate}
    (parity : ∀ r ∈ crossing, 2 ≤ (car r).card)
    (small :
      (essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state).card ≤ 1)
    {r : Coordinate} (member : r ∈ crossing) :
    r ∉ retained carrierSupply coordinates car
      (essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state) := by
  intro retainedMember
  rw [mem_retained] at retainedMember
  have two := parity r member
  have bounded :
      (car r).card ≤
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state).card :=
    Finset.card_le_card retainedMember.2
  omega

/-- With a core of cardinality at most one, forgetting all crossing coordinates
changes no retained reading. -/
theorem retained_sdiff_eq_of_core_card_le_one {crossing : Finset Coordinate}
    (parity : ∀ r ∈ crossing, 2 ≤ (car r).card)
    (small :
      (essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state).card ≤ 1) :
    retained carrierSupply coordinates car
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) \ crossing =
      retained carrierSupply coordinates car
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) := by
  refine Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.mpr ?_)
  intro r retainedMember member
  exact not_mem_retained_of_core_card_le_one (Target := Target)
    carrierSupply coordinates car car_subset state parity small member
    retainedMember

/-- **Small-core collapse, raw carrier-core form.**

If the trace-basin minimality clause says that the internal-crossing forgetting
quotient being equal to the core restriction triggers the paper alternatives,
then a zero/one-carrier core triggers those alternatives.  The alternatives are
not supplied by this theorem; they are the selected entry's
target-complete-minimality datum, and downstream Strategy rows must read the
corresponding no-exit facts from the ledger before closing the branch. -/
theorem smallCoreCollapse {crossing : Finset Coordinate} {Alternatives : Prop}
    (parity : ∀ r ∈ crossing, 2 ≤ (car r).card)
    (minimality :
      state (retained carrierSupply coordinates car
          (essentialCore (Target := Target) carrierSupply coordinates car
            (car_subset := car_subset) state) \ crossing) =
        restriction carrierSupply coordinates car state
          (essentialCore (Target := Target) carrierSupply coordinates car
            (car_subset := car_subset) state) →
      Alternatives)
    (small :
      (essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state).card ≤ 1) :
    Alternatives := by
  refine minimality ?_
  rw [retained_sdiff_eq_of_core_card_le_one (Target := Target)
    carrierSupply coordinates car car_subset state parity small, restriction]

/-- The reusable theorem package for node `[114]`: the minimal carrier core is
complete, lies in the declared carrier supply, and every core carrier has the
forced deletion target-defect plus a declared forgotten coordinate using it. -/
def CarrierCoreFacts : Prop :=
  let core := essentialCore (Target := Target) carrierSupply coordinates car
    (car_subset := car_subset) state
  Complete (Target := Target) carrierSupply coordinates car state core ∧
    core ⊆ carrierSupply.toFinset ∧
      ∀ carrier ∈ core,
        Response.TargetDefect Target
          (restriction carrierSupply coordinates car state (core.erase carrier))
          (restriction carrierSupply coordinates car state core) ∧
        ∃ r ∈ coordinates, car r ⊆ core ∧ carrier ∈ car r

theorem carrierCoreFacts :
    CarrierCoreFacts (Target := Target) carrierSupply coordinates car
      car_subset state := by
  dsimp [CarrierCoreFacts]
  refine ⟨essentialCore_complete (Target := Target)
      carrierSupply coordinates car (car_subset := car_subset) state,
    essentialCore_subset_carrierSupply (Target := Target)
      carrierSupply coordinates car car_subset state, ?_⟩
  intro carrier member
  exact ⟨deletion_targetDefect (Target := Target)
      carrierSupply coordinates car (car_subset := car_subset) state member,
    exists_forgotten_coordinate (Target := Target)
      carrierSupply coordinates car car_subset state member⟩

/-- The reusable theorem package for nodes `[115]`--`[116]`: every zero/one
carrier core activates the selected trace-basin minimality alternatives once
the caller supplies the entry's cut-parity crossing family and its own
minimality clause. -/
def SmallCoreCollapseFacts : Prop :=
  ∀ {crossing : Finset Coordinate} {Alternatives : Prop},
    (∀ r ∈ crossing, 2 ≤ (car r).card) →
    (state (retained carrierSupply coordinates car
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) \ crossing) =
      restriction carrierSupply coordinates car state
        (essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) →
        Alternatives) →
    (essentialCore (Target := Target) carrierSupply coordinates car
      (car_subset := car_subset) state).card ≤ 1 →
    Alternatives

theorem smallCoreCollapseFacts :
    SmallCoreCollapseFacts (Target := Target) carrierSupply coordinates car
      car_subset state := by
  intro crossing Alternatives parity minimality small
  exact smallCoreCollapse (Target := Target) carrierSupply coordinates car
    car_subset state parity minimality small

end Core

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
variable {Carrier Coordinate Index : Type u}
variable [DecidableEq Carrier] [DecidableEq Coordinate] [DecidableEq Index]
variable {boundary : Boundary.{u}}
variable (carrierSupply : Enumeration Carrier)
variable (coordinates : Finset Coordinate) (car : Coordinate → Finset Carrier)
variable (car_subset : ∀ r ∈ coordinates, car r ⊆ carrierSupply.toFinset)
variable (state : Finset Coordinate → BoundaryPiece boundary)

/-- The node-`[118]` carrier-deletion witness package for one already selected
two-carrier indexed core.  It contains no route-`8` collection carrier: the
index, core family, and two-carrier fact are the concrete facts read from the
ledger by the caller. -/
def TwoCarrierDeletionWitnesses
    (entries : Finset Index) (core : Index → Finset Carrier)
    (threshold : Nat) (index : Index) : Prop :=
  IndexedTwoCarrierCore entries core threshold index ∧
    ∀ carrier ∈ core index,
      Response.TargetDefect Target
        (restriction carrierSupply coordinates car state
          ((core index).erase carrier))
        (restriction carrierSupply coordinates car state (core index)) ∧
      ∃ r ∈ coordinates, car r ⊆ core index ∧ carrier ∈ car r

/-- The canonical deletion witnesses attached to a selected two-carrier core.

This is `lem:typeA-essential-deletion-witness` and
`lem:typeA-deletion-witness-declared` in raw carrier-core form: once the
selected indexed core is identified with the canonical essential core of the
selected reading, every essential carrier has the separating deletion quotient
and a declared forgotten coordinate whose carrier support contains it. -/
theorem twoCarrierDeletionWitnesses
    (entries : Finset Index) (core : Index → Finset Carrier)
    {threshold : Nat} {index : Index}
    (two : IndexedTwoCarrierCore entries core threshold index)
    (core_eq :
      core index =
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state) :
    TwoCarrierDeletionWitnesses (Target := Target) carrierSupply coordinates car
      state entries core threshold index := by
  refine ⟨two, ?_⟩
  intro carrier member
  have essentialMember :
      carrier ∈ essentialCore (Target := Target) carrierSupply coordinates car
        (car_subset := car_subset) state := by
    simpa [core_eq] using member
  have defect := deletion_targetDefect (Target := Target)
    carrierSupply coordinates car (car_subset := car_subset) state
    essentialMember
  have declared := exists_forgotten_coordinate (Target := Target)
    carrierSupply coordinates car car_subset state essentialMember
  refine ⟨?_, ?_⟩
  · simpa [core_eq] using defect
  · simpa [core_eq] using declared

/-- The reusable theorem package for node `[118]`: every selected two-carrier
essential-core entry has its carrier-deletion target-defect witnesses and the
declared forgotten coordinates required by the canonical Q5 clause. -/
def TwoCarrierDeletionWitnessFacts : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    {threshold : Nat} {index : Index},
      IndexedTwoCarrierCore entries core threshold index →
      core index =
        essentialCore (Target := Target) carrierSupply coordinates car
          (car_subset := car_subset) state →
      TwoCarrierDeletionWitnesses (Target := Target) carrierSupply coordinates
        car state entries core threshold index

theorem twoCarrierDeletionWitnessFacts :
    TwoCarrierDeletionWitnessFacts (Target := Target) carrierSupply coordinates
      car car_subset state := by
  intro Index indexDec entries core threshold index two core_eq
  letI : DecidableEq Index := indexDec
  exact twoCarrierDeletionWitnesses (Target := Target) carrierSupply
    coordinates car car_subset state entries core two core_eq

/-- The terminal no-go consumed at node `[124]`.

Once a selected two-carrier core has carrier-deletion witnesses, any generated
Q5 carrier-deletion quotient with the recorded boundary-profile preservation is
an ordinary exit-`(4)` witness.  The already committed no-exit-`(4)` ledger fact
therefore closes the terminal route-`8` survivor. -/
theorem terminalTwoCarrierNoGo
    (entries : Finset Index) (core : Index → Finset Carrier)
    {carrierBound : Nat} {index : Index}
    (witnesses :
      TwoCarrierDeletionWitnesses (Target := Target) carrierSupply coordinates
        car state entries core carrierBound index)
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {degreeThreshold : Nat} {receiver : object.Vertex}
    {peeled : Finset object.Vertex} {eligible : object.Vertex → Prop}
    (noExitFour :
      ¬ ∃ witness : ExitFour.Witness Target support degreeThreshold receiver
          peeled,
        eligible witness.load)
    (family : ExitFour.ReceiverFamily Target support degreeThreshold receiver)
    {base identified : Finset family.Coordinate}
    (generated :
      family.Generated ExitFour.ReceiverClause.carrierDeletion base identified)
    {load : object.Vertex}
    (unpeeled :
      load ∈ ExitFour.unpeeledLoads support degreeThreshold receiver peeled)
    (declared : load ∈ family.declaredLoads identified)
    (eligibleLoad : eligible load)
    {carrier : Carrier} (member : carrier ∈ core index)
    (sameBoundaryProfile :
      (restriction carrierSupply coordinates car state
          ((core index).erase carrier)).boundaryDegreeProfile =
        (restriction carrierSupply coordinates car state
          (core index)).boundaryDegreeProfile) :
    False := by
  have defect := (witnesses.2 carrier member).1
  exact ExitFour.Witness.carrierDeletion_contradicts_noExitFour noExitFour
    family generated unpeeled declared eligibleLoad sameBoundaryProfile defect

/-- The reusable theorem package for node `[124]`: a terminal selected
two-carrier carrier-deletion quotient contradicts the no-exit-`(4)` fact from
the same residual. -/
def TerminalTwoCarrierNoGoFacts
    (Target : FiniteObject.{u} → Prop)
    (carrierSupply : Enumeration Carrier) (coordinates : Finset Coordinate)
    (car : Coordinate → Finset Carrier)
    (_car_subset : ∀ r ∈ coordinates, car r ⊆ carrierSupply.toFinset)
    (state : Finset Coordinate → BoundaryPiece boundary) : Prop :=
  ∀ {Index : Type u} [DecidableEq Index]
    (entries : Finset Index) (core : Index → Finset Carrier)
    {carrierBound : Nat} {index : Index},
      TwoCarrierDeletionWitnesses (Target := Target) carrierSupply coordinates
        car state entries core carrierBound index →
      ∀ {object : FiniteObject.{u}} {support : Finset object.Vertex}
        {degreeThreshold : Nat} {receiver : object.Vertex}
        {peeled : Finset object.Vertex} {eligible : object.Vertex → Prop},
        (¬ ∃ witness : ExitFour.Witness Target support degreeThreshold receiver
            peeled,
          eligible witness.load) →
        (family : ExitFour.ReceiverFamily Target support degreeThreshold
          receiver) →
        ∀ {base identified : Finset family.Coordinate},
          family.Generated ExitFour.ReceiverClause.carrierDeletion base
            identified →
          ∀ {load : object.Vertex},
            load ∈ ExitFour.unpeeledLoads support degreeThreshold receiver
              peeled →
            load ∈ family.declaredLoads identified →
            eligible load →
            ∀ {carrier : Carrier},
              carrier ∈ core index →
              (restriction carrierSupply coordinates car state
                  ((core index).erase carrier)).boundaryDegreeProfile =
                (restriction carrierSupply coordinates car state
                  (core index)).boundaryDegreeProfile →
              False

theorem terminalTwoCarrierNoGoFacts :
    TerminalTwoCarrierNoGoFacts Target carrierSupply coordinates
      car car_subset state := by
  intro Index indexDec entries core carrierBound index witnesses object
    support degreeThreshold receiver peeled eligible noExitFour family base
    identified generated load unpeeled declared eligibleLoad carrier member
    sameBoundaryProfile
  letI : DecidableEq Index := indexDec
  exact terminalTwoCarrierNoGo (Target := Target) carrierSupply coordinates
    car state entries core witnesses noExitFour family generated
    unpeeled declared eligibleLoad member sameBoundaryProfile

end TerminalTwoCarrier

end Hypostructure.Graph.Route8
