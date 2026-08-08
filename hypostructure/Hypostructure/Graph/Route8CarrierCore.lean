import Hypostructure.Core.Finite.EssentialCarrier
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
  rw [restriction, retained_carrierSupply]

/-- A carrier set is complete when its restriction is target-equivalent to the
full reading against every outside context. -/
def Complete (D : Finset Carrier) : Prop :=
  Response.ContextEquivalent Target
    (restriction carrierSupply coordinates car state D) (state coordinates)

theorem complete_carrierSupply :
    Complete (Target := Target) carrierSupply coordinates car state
      carrierSupply.toFinset := by
  intro outside
  rw [restriction_carrierSupply]

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
    member (Finset.Subset.antisymm ?_ ?_)
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

end Hypostructure.Graph.Route8
