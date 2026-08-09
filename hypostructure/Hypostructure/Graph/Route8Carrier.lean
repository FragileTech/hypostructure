import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Graph.Response

/-!
# Boundary-carrier cores of an indexed boundaried reading

A reading of a boundaried piece is presented by a finite family of *declared
coordinates*, each of which records the finite set of *boundary carriers* --
oriented incidences leaving the piece's own support -- that its declared
support uses.  Restricting the reading to a set `D` of carriers keeps exactly
the coordinates whose carrier set is contained in `D`, and always keeps the
labelled boundary itself.  `D` is *complete* when the restricted reading has
the same target response as the full one against every outside context.

This module owns four things, and nothing else:

* the `D`-restriction and its completeness predicate;
* the canonical inclusion-minimal complete carrier set, taken with Core's own
  `Finite.EssentialCarrier.Profile`, and its cardinality;
* the *deletion witness* that inclusion-minimality forces at every carrier of
  that core, and the fact that a witness's forgotten coordinate uses the
  deleted carrier;
* the local deletion witness forced at one indexed reading.

Nothing here mentions a graph target, a manuscript, a strategy, a ledger, or a
proof.  This is the exact local content of the manuscript's
`def:typeA-route8-carriers`, `lem:typeA-essential-deletion-witness` and
`lem:typeA-deletion-witness-declared`, stated for any target predicate on finite
objects.  Census-level route-8 facts belong on the canonical ledger; this module
does not define a secondary carrier.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

/-- The paper's ambient carriers for route-`8`: oriented boundary incidences of
the selected support, represented by the inside vertex and the ambient edge. -/
abbrev BoundaryCarrier (object : FiniteObject.{u}) : Type u :=
  object.Vertex × Sym2 object.Vertex

/-- Decidable equality on the concrete graph-owned route-`8` carriers. -/
noncomputable def boundaryCarrierDecEq (object : FiniteObject.{u}) :
    DecidableEq (BoundaryCarrier object) := by
  classical
  infer_instance

/-- **One indexed reading with its declared carrier signature.**

`carriers` is the ambient supply `∂_E X` of oriented boundary incidences the
reading may use; `coordinates` is the declared coordinate family of the reading;
`car` is the carrier support each declared coordinate records; and `state`
assembles the boundaried piece that retains exactly a given set of declared
coordinates.  The labelled boundary is fixed, so every restriction below is
taken inside one boundary-degree fibre -- which is what makes a restriction a
*response quotient* rather than a change of interface. -/
structure Entry (Target : FiniteObject.{u} → Prop) (Carrier : Type u) where
  /-- The labelled interface every restricted reading is presented on. -/
  boundary : Boundary.{u}
  /-- `∂_E X`: the finite carrier supply of this entry. -/
  carriers : Enumeration Carrier
  /-- The declared coordinates of the reading. -/
  Coordinate : Type u
  /-- Decidable equality on the declared coordinates. -/
  coordinateDecEq : DecidableEq Coordinate
  /-- The declared coordinate family `𝓡_u(B_u)`. -/
  coordinates : Finset Coordinate
  /-- `car(r)`: the carriers the declared support of `r` uses. -/
  car : Coordinate → Finset Carrier
  /-- Every declared coordinate uses carriers of this entry's own supply. -/
  car_subset : ∀ r ∈ coordinates, car r ⊆ carriers.toFinset
  /-- The boundaried reading retaining exactly a set of declared coordinates. -/
  state : Finset Coordinate → BoundaryPiece boundary

namespace Entry

variable {Target : FiniteObject.{u} → Prop} {Carrier : Type u}
variable [DecidableEq Carrier] (entry : Entry Target Carrier)

attribute [instance] Entry.coordinateDecEq

/-- The declared coordinates a `D`-restriction retains: exactly those whose
carrier support lies inside `D`. -/
def retained (D : Finset Carrier) : Finset entry.Coordinate :=
  entry.coordinates.filter fun r => entry.car r ⊆ D

theorem mem_retained {D : Finset Carrier} {r : entry.Coordinate} :
    r ∈ entry.retained D ↔ r ∈ entry.coordinates ∧ entry.car r ⊆ D := by
  simp [retained]

theorem retained_mono {D E : Finset Carrier} (subset : D ⊆ E) :
    entry.retained D ⊆ entry.retained E := by
  intro r member
  rw [mem_retained] at member ⊢
  exact ⟨member.1, member.2.trans subset⟩

/-- `ρ|_D`: the reading restricted to the carrier set `D`. -/
def restriction (D : Finset Carrier) : BoundaryPiece entry.boundary :=
  entry.state (entry.retained D)

/-- The unrestricted reading. -/
def full : BoundaryPiece entry.boundary :=
  entry.state entry.coordinates

/-- The whole carrier supply retains every declared coordinate. -/
theorem retained_carriers :
    entry.retained entry.carriers.toFinset = entry.coordinates := by
  apply Finset.ext
  intro r
  rw [mem_retained]
  exact ⟨fun member => member.1, fun member => ⟨member, entry.car_subset r member⟩⟩

@[simp] theorem restriction_carriers :
    entry.restriction entry.carriers.toFinset = entry.full := by
  rw [restriction, retained_carriers, full]

/-- **A target-complete carrier set.**  Restricting to `D` is invisible to the
target against every outside context. -/
def Complete (D : Finset Carrier) : Prop :=
  Response.ContextEquivalent Target (entry.restriction D) entry.full

/-- The whole supply is complete: it restricts nothing. -/
theorem complete_carriers : entry.Complete entry.carriers.toFinset := by
  intro outside
  rw [restriction_carriers]

/-- A carrier outside this entry's own supply is used by no declared
coordinate, so deleting it from a carrier set changes no restriction. -/
theorem retained_erase_of_not_mem {D : Finset Carrier} {carrier : Carrier}
    (outside : carrier ∉ entry.carriers.toFinset) :
    entry.retained (D.erase carrier) = entry.retained D := by
  refine Finset.Subset.antisymm (entry.retained_mono (Finset.erase_subset _ _)) ?_
  intro r member
  rw [mem_retained] at member ⊢
  refine ⟨member.1, ?_⟩
  intro other used
  refine Finset.mem_erase.mpr ⟨?_, member.2 used⟩
  intro same
  exact outside (same ▸ entry.car_subset r member.1 used)

/-- Core's own inclusion-minimal carrier selection, at this entry's supply and
completeness predicate.  The core is a *minimum-cardinality* complete set, hence
inclusion-minimal, and `Finite.EssentialCarrier` owns both facts. -/
noncomputable def carrierProfile : EssentialCarrier.Profile.{u} where
  Carrier := Carrier
  schedule := entry.carriers
  Complete := entry.Complete
  completeDecidable := fun _ => Classical.propDecidable _
  fullComplete := entry.complete_carriers

/-- `𝓒_ess(ξ)`: the canonical inclusion-minimal target-complete carrier set. -/
noncomputable def essentialCore : Finset Carrier :=
  entry.carrierProfile.core

/-- `α(ξ) = |𝓒_ess(ξ)|`. -/
noncomputable def alpha : Nat :=
  entry.essentialCore.card

theorem essentialCore_complete : entry.Complete entry.essentialCore :=
  entry.carrierProfile.core_complete

/-- **Every essential carrier is essential.**  Deleting one from the core
destroys completeness; this is Core's `erase_not_complete` read here. -/
theorem essentialCore_erase_not_complete {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    ¬ entry.Complete (entry.essentialCore.erase carrier) := by
  letI : DecidableEq entry.carrierProfile.Carrier := ‹DecidableEq Carrier›
  have essential := entry.carrierProfile.erase_not_complete carrier member
  exact essential

/-- **The canonical core draws on this entry's own supply.**  A carrier outside
the supply is used by no declared coordinate, so a core containing one would
stay complete after deleting it -- and a complete proper subset contradicts the
core's minimality. -/
theorem essentialCore_subset_carriers :
    entry.essentialCore ⊆ entry.carriers.toFinset := by
  intro carrier member
  by_contra outside
  refine entry.essentialCore_erase_not_complete member ?_
  intro context
  have same := entry.retained_erase_of_not_mem
    (D := entry.essentialCore) outside
  have rewritten :
      entry.restriction (entry.essentialCore.erase carrier) =
        entry.restriction entry.essentialCore := by
    rw [restriction, restriction, same]
  rw [rewritten]
  exact entry.essentialCore_complete context

/-- **Deletion witnesses exist** (`lem:typeA-essential-deletion-witness`).

For every essential carrier `c`, the `c`-deletion quotient of the core reading
is not target-complete: some outside context separates the core reading from the
one carrier `c` was deleted from.  Nothing is assumed -- the witness is forced by
inclusion-minimality of the core and completeness of the core itself. -/
theorem deletion_targetDefect {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    Response.TargetDefect Target
      (entry.restriction (entry.essentialCore.erase carrier))
      (entry.restriction entry.essentialCore) := by
  refine Response.targetDefect_of_not_contextEquivalent ?_
  intro equivalent
  refine entry.essentialCore_erase_not_complete member ?_
  intro outside
  exact (equivalent outside).trans (entry.essentialCore_complete outside)

/-- A deletion quotient really forgets a declared coordinate: if it retained the
same coordinates it would be the same reading, and no context could separate
them. -/
theorem retained_erase_ne {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    entry.retained (entry.essentialCore.erase carrier) ≠
      entry.retained entry.essentialCore := by
  intro same
  obtain ⟨outside, separates⟩ := entry.deletion_targetDefect member
  exact separates (by rw [restriction, restriction, same])

/-- **Deletion witnesses are declared, and their carrier support contains the
deleted carrier** (`lem:typeA-deletion-witness-declared`).

The coordinates a `c`-deletion forgets are exactly the declared coordinates of
the core reading whose carrier support uses `c`, and at least one of them
exists.  Both halves are forced by the definition of the `D`-restriction. -/
theorem exists_forgotten_coordinate {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    ∃ r ∈ entry.coordinates,
      entry.car r ⊆ entry.essentialCore ∧ carrier ∈ entry.car r := by
  classical
  by_contra missing
  simp only [not_exists, not_and] at missing
  refine entry.retained_erase_ne member (Finset.Subset.antisymm ?_ ?_)
  · exact entry.retained_mono (Finset.erase_subset _ _)
  · intro r inCore
    rw [mem_retained] at inCore ⊢
    refine ⟨inCore.1, ?_⟩
    intro other used
    refine Finset.mem_erase.mpr ⟨?_, inCore.2 used⟩
    intro same
    exact missing r inCore.1 inCore.2 (same ▸ used)

/-- The selected entry's carrier-core facts: completeness of the canonical
core, containment in the entry's own supply, and the deletion witness/declared
forgotten-coordinate clause for every essential carrier. -/
def CarrierCoreFacts : Prop :=
  entry.Complete entry.essentialCore ∧
    entry.essentialCore ⊆ entry.carriers.toFinset ∧
      ∀ carrier ∈ entry.essentialCore,
        Response.TargetDefect Target
          (entry.restriction (entry.essentialCore.erase carrier))
          (entry.restriction entry.essentialCore) ∧
        ∃ r ∈ entry.coordinates,
          entry.car r ⊆ entry.essentialCore ∧ carrier ∈ entry.car r

theorem carrierCoreFacts : entry.CarrierCoreFacts := by
  dsimp [CarrierCoreFacts]
  refine ⟨entry.essentialCore_complete, entry.essentialCore_subset_carriers, ?_⟩
  intro carrier member
  exact ⟨entry.deletion_targetDefect member,
    entry.exists_forgotten_coordinate member⟩

end Entry

section IndexedCarrierAccounting

variable {Target : FiniteObject.{u} → Prop} {Carrier Index : Type u}
variable [DecidableEq Carrier] [DecidableEq Index]

/-- The carriers private to one indexed route-`8` entry, inside the selected
finite family read from the ledger.  This is pure carrier arithmetic, not a
secondary residual object. -/
noncomputable def indexedPrivateCarriers
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (index : Index) : Finset Carrier :=
  (entry index).carriers.toFinset.filter fun carrier =>
    ∀ other ∈ entries, other ≠ index → carrier ∉ (entry other).carriers.toFinset

/-- The number of private carriers of one indexed route-`8` entry. -/
noncomputable def indexedPrivateCount
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (index : Index) : Nat :=
  (indexedPrivateCarriers entries entry index).card

/-- The terminal two-carrier condition of Part IX, stated on the selected
indexed family rather than packaged in a carrier object. -/
def IndexedTwoCarrier
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (threshold : Nat) (index : Index) : Prop :=
  indexedPrivateCount entries entry index ≤ threshold

theorem indexedPrivateCarriers_subset_entry
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (index : Index) :
    indexedPrivateCarriers entries entry index ⊆ (entry index).carriers.toFinset := by
  intro carrier hcarrier
  exact (Finset.mem_filter.mp hcarrier).1

theorem indexedPrivateCarriers_subset_supply
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply)
    {index : Index} (index_mem : index ∈ entries) :
    indexedPrivateCarriers entries entry index ⊆ supply := by
  exact subset_trans (indexedPrivateCarriers_subset_entry entries entry index)
    (carriers_subset index index_mem)

theorem indexedPrivateCarriers_disjoint
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    {left right : Index} (left_mem : left ∈ entries) (right_mem : right ∈ entries)
    (distinct : left ≠ right) :
    Disjoint (indexedPrivateCarriers entries entry left)
      (indexedPrivateCarriers entries entry right) := by
  rw [Finset.disjoint_left]
  intro carrier hleft hright
  have hleft_private := (Finset.mem_filter.mp hleft).2
  exact hleft_private right right_mem (fun same => distinct same.symm)
    ((indexedPrivateCarriers_subset_entry entries entry right) hright)

theorem indexedPrivateCarriers_card_biUnion_le_supply
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply) :
    (entries.biUnion fun index => indexedPrivateCarriers entries entry index).card ≤
      supply.card := by
  refine Finset.card_le_card ?_
  intro carrier hcarrier
  rcases Finset.mem_biUnion.mp hcarrier with ⟨index, index_mem, carrier_mem⟩
  exact indexedPrivateCarriers_subset_supply entries entry supply carriers_subset
    index_mem carrier_mem

theorem indexedPrivateCarriers_card_sum_le_supply
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply) :
    (∑ index ∈ entries, indexedPrivateCount entries entry index) ≤
      supply.card := by
  change (∑ index ∈ entries,
      (indexedPrivateCarriers entries entry index).card) ≤ supply.card
  rw [← Finset.card_biUnion]
  · exact indexedPrivateCarriers_card_biUnion_le_supply entries entry supply
      carriers_subset
  intro left left_mem right right_mem distinct
  exact indexedPrivateCarriers_disjoint entries entry left_mem right_mem distinct

theorem indexedCardMul_le_supply
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply)
    {floor : Nat}
    (lower : ∀ index ∈ entries, floor ≤ indexedPrivateCount entries entry index) :
    floor * entries.card ≤ supply.card := by
  calc
    floor * entries.card
        = ∑ _index ∈ entries, floor := by
          rw [Finset.sum_const]
          simpa [mul_comm]
    _ ≤ ∑ index ∈ entries, indexedPrivateCount entries entry index := by
          exact Finset.sum_le_sum fun index index_mem => lower index index_mem
    _ ≤ supply.card :=
          indexedPrivateCarriers_card_sum_le_supply entries entry supply
            carriers_subset

end IndexedCarrierAccounting

end Hypostructure.Graph.Route8
