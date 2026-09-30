import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Graph.Response

/-!
# Boundary-carrier cores of an indexed boundaried reading

A reading of a boundaried piece is presented by a finite family of *declared
coordinates*, each of which records the finite set of *boundary carriers* --
oriented incidences leaving the piece's own support -- that its declared
support uses.  Restricting the reading to a set `D` of carriers keeps exactly
the coordinates whose carrier set is contained in `D`, and always keeps the
labelled boundary itself.  `D` is *complete* when every *realization* of the
restricted reading -- a piece of the entry's realization family (for a
graph-owned entry, the pieces constructed from G at `B_u`, `GConstructedPiece`)
that carries every retained coordinate exactly -- has the target response of the
full reading in the entry's one actual context (G's surroundings `G − B_u`).
The context is G's; the realizations are pieces built from G.

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
*response quotient* rather than a change of interface.

`Realization`, `realize` and `Realizes` are the realizations a restricted
reading is tested on (`def:typeA-trace-basin`: *"a realization of such a
quotient is a boundaried response state with the same boundary degree profile
whose image under the quotient map is the given quotient"*): `Realizes R ρ`
says that `realize ρ` carries every coordinate of `R` exactly.  Carrying more
coordinates is carrying fewer (`realizes_anti`). -/
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
  /-- The one outside context the reading is ever glued into: the actual
  surroundings of the reading's support in its own ambient graph (for a
  graph-owned entry, `SupportAtom.outside G B_u`, i.e. `G − B_u`).  No other
  context is quantified. -/
  actual : OutsideContext boundary
  /-- The realizations a restricted reading is tested on (for a graph-owned
  entry: the pieces constructed from G at `B_u`). -/
  Realization : Type u
  /-- The boundaried piece a realization denotes. -/
  realize : Realization → BoundaryPiece boundary
  /-- `Realizes R ρ`: `realize ρ` lies in the reading's boundary-degree fibre and
  carries every coordinate of `R` exactly. -/
  Realizes : Finset Coordinate → Realization → Prop
  /-- A realization of a larger retained set realizes every smaller one. -/
  realizes_anti : ∀ {R S : Finset Coordinate} (ρ : Realization),
    R ⊆ S → Realizes S ρ → Realizes R ρ

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

/-- **A target-complete carrier set, at G.**  Every realization of the
restricted reading `ρ|_D` has, in the entry's actual surroundings (G − B_u for a
graph-owned entry), the target truth of the full reading.

Stated about G, the paper's "for every outside context compatible with the
boundary profile, all realizations of the quotient" reads the one context of G
and the realizations built from G. -/
def Complete (D : Finset Carrier) : Prop :=
  ∀ ρ : entry.Realization, entry.Realizes (entry.retained D) ρ →
    (Target (glue (entry.realize ρ) entry.actual) ↔
      Target (glue entry.full entry.actual))

/-- **The declared family determines the target** (`def:typeA-trace-basin`:
*"once the boundary degree profile and all entries of `𝓡_u(B_u)` are fixed,
every compatible outside context has the same truth value"*), at G: the whole
supply is complete.  The manuscript asserts it ("Such sets exist: for
`D = ∂_E X` ... the completeness clause applies"); at G it is a property of the
entry that can fail, and it is tested, not assumed. -/
def Determined : Prop :=
  entry.Complete entry.carriers.toFinset

/-- Completeness is monotone: a larger carrier set retains more coordinates, so
it has fewer realizations. -/
theorem complete_mono {D E : Finset Carrier} (subset : D ⊆ E)
    (complete : entry.Complete D) : entry.Complete E :=
  fun ρ realizes =>
    complete ρ (entry.realizes_anti ρ (entry.retained_mono subset) realizes)

/-- Completeness reads only the retained coordinates. -/
theorem complete_congr {D E : Finset Carrier}
    (same : entry.retained D = entry.retained E) :
    entry.Complete D ↔ entry.Complete E := by
  unfold Complete
  rw [same]

/-- An undetermined entry has no complete carrier set at all. -/
theorem not_complete_of_not_determined (undetermined : ¬ entry.Determined)
    (D : Finset Carrier) : ¬ entry.Complete D := by
  classical
  intro complete
  have union := entry.complete_mono (Finset.subset_union_left
    (s₂ := entry.carriers.toFinset)) complete
  refine undetermined ((entry.complete_congr ?_).mp union)
  rw [retained_carriers]
  apply Finset.Subset.antisymm
  · intro r member
    exact (entry.mem_retained.mp member).1
  · intro r member
    exact entry.mem_retained.mpr ⟨member,
      (entry.car_subset r member).trans Finset.subset_union_right⟩

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

/-- The completeness predicate the core is selected against: `D` is complete,
or the entry is undetermined (then no carrier set is complete and the core is
empty). -/
def CoreComplete (D : Finset Carrier) : Prop :=
  entry.Complete D ∨ ¬ entry.Determined

theorem coreComplete_carriers : entry.CoreComplete entry.carriers.toFinset := by
  by_cases determined : entry.Determined
  · exact Or.inl determined
  · exact Or.inr determined

/-- Core's own inclusion-minimal carrier selection, at this entry's supply and
completeness predicate.  The core is a *minimum-cardinality* complete set, hence
inclusion-minimal, and `Finite.EssentialCarrier` owns both facts. -/
noncomputable def carrierProfile : EssentialCarrier.Profile.{u} where
  Carrier := Carrier
  schedule := entry.carriers
  Complete := entry.CoreComplete
  completeDecidable := fun _ => Classical.propDecidable _
  fullComplete := entry.coreComplete_carriers

/-- `𝓒_ess(ξ)`: the canonical inclusion-minimal target-complete carrier set. -/
noncomputable def essentialCore : Finset Carrier :=
  entry.carrierProfile.core

/-- `α(ξ) = |𝓒_ess(ξ)|`. -/
noncomputable def alpha : Nat :=
  entry.essentialCore.card

theorem essentialCore_coreComplete : entry.CoreComplete entry.essentialCore :=
  entry.carrierProfile.core_complete

/-- **A determined entry's core is complete.** -/
theorem essentialCore_complete (determined : entry.Determined) :
    entry.Complete entry.essentialCore := by
  rcases entry.essentialCore_coreComplete with complete | undetermined
  · exact complete
  · exact absurd determined undetermined

/-- **An empty complete set empties the core**: the core is a minimum-cardinality
complete set, so a complete `∅` gives `α(ξ) = 0`. -/
theorem alpha_eq_zero_of_coreComplete_empty (empty : entry.CoreComplete ∅) :
    entry.alpha = 0 := by
  have minimumLe := entry.carrierProfile.minimumCard_le ∅ empty
  have coreCard := entry.carrierProfile.core_card
  change entry.essentialCore.card = entry.carrierProfile.minimumCard at coreCard
  change entry.essentialCore.card = 0
  rw [coreCard]
  simpa using minimumLe

theorem alpha_eq_zero_of_complete_empty (empty : entry.Complete ∅) :
    entry.alpha = 0 :=
  entry.alpha_eq_zero_of_coreComplete_empty (Or.inl empty)

/-- **An undetermined entry has an empty core.** -/
theorem alpha_eq_zero_of_not_determined (undetermined : ¬ entry.Determined) :
    entry.alpha = 0 :=
  entry.alpha_eq_zero_of_coreComplete_empty (Or.inr undetermined)

/-- **A nonempty core means the declared family determines the target.** -/
theorem determined_of_mem_essentialCore {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) : entry.Determined := by
  by_contra undetermined
  have zero := entry.alpha_eq_zero_of_not_determined undetermined
  have positive : 0 < entry.essentialCore.card :=
    Finset.card_pos.mpr ⟨carrier, member⟩
  change entry.essentialCore.card = 0 at zero
  omega

theorem determined_of_one_le_alpha (one : 1 ≤ entry.alpha) : entry.Determined := by
  have positive : 0 < entry.essentialCore.card := one
  obtain ⟨carrier, member⟩ := Finset.card_pos.mp positive
  exact entry.determined_of_mem_essentialCore member

/-- **`lem:typeA-carrier-cut-parity`, last step**:
*"Each such crossing is recorded in the declared support of the corresponding
`u`-supported coordinate ... Since the event survives in the restricted state
`\rho_u(B_u)|_{\mathcal C_{\rm ess}(\xi)}`, every boundary incidence in its
declared support lies in `\mathcal C_{\rm ess}(\xi)`.  The two distinct cut
crossings therefore give two distinct boundary incidences from
`\mathcal C_{\rm ess}(\xi)`."*

A coordinate the core retains has its whole carrier set inside the core, so a
coordinate with two distinct carriers forces `\alpha(\xi) \ge 2`. -/
theorem two_le_alpha_of_two_le_card_car {r : entry.Coordinate}
    (member : r ∈ entry.retained entry.essentialCore)
    (two : 2 ≤ (entry.car r).card) : 2 ≤ entry.alpha :=
  two.trans (Finset.card_le_card (entry.mem_retained.mp member).2)

/-- The same hinge read through the core's own carriers: two distinct carriers
of a retained coordinate are two distinct essential carriers. -/
theorem two_le_alpha_of_two_carriers {r : entry.Coordinate}
    (member : r ∈ entry.retained entry.essentialCore)
    {left right : Carrier} (distinct : left ≠ right)
    (leftCarrier : left ∈ entry.car r) (rightCarrier : right ∈ entry.car r) :
    2 ≤ entry.alpha := by
  classical
  refine entry.two_le_alpha_of_two_le_card_car member ?_
  have subset : ({left, right} : Finset Carrier) ⊆ entry.car r := by
    intro carrier carrierMem
    rcases Finset.mem_insert.mp carrierMem with rfl | tail
    · exact leftCarrier
    · rw [Finset.mem_singleton.mp tail]
      exact rightCarrier
  have card : ({left, right} : Finset Carrier).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using distinct),
      Finset.card_singleton]
  exact card ▸ Finset.card_le_card subset

/-- **Two recorded incidences are two essential carriers, even when they are
recorded by different coordinates.** -/
theorem two_le_alpha_of_two_core_carriers {left right : Carrier}
    (distinct : left ≠ right) {r s : entry.Coordinate}
    (rCore : r ∈ entry.retained entry.essentialCore)
    (sCore : s ∈ entry.retained entry.essentialCore)
    (leftMem : left ∈ entry.car r) (rightMem : right ∈ entry.car s) :
    2 ≤ entry.alpha := by
  classical
  have leftCore : left ∈ entry.essentialCore :=
    (entry.mem_retained.mp rCore).2 leftMem
  have rightCore : right ∈ entry.essentialCore :=
    (entry.mem_retained.mp sCore).2 rightMem
  have subset : ({left, right} : Finset Carrier) ⊆ entry.essentialCore := by
    intro carrier carrierMem
    rcases Finset.mem_insert.mp carrierMem with rfl | tail
    · exact leftCore
    · rw [Finset.mem_singleton.mp tail]
      exact rightCore
  have card : ({left, right} : Finset Carrier).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using distinct),
      Finset.card_singleton]
  exact card ▸ Finset.card_le_card subset

/-- **Every essential carrier is essential.**  Deleting one from the core
destroys completeness; this is Core's `erase_not_complete` read here (the entry
is determined, since its core is nonempty). -/
theorem essentialCore_erase_not_complete {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    ¬ entry.Complete (entry.essentialCore.erase carrier) := by
  letI : DecidableEq entry.carrierProfile.Carrier := ‹DecidableEq Carrier›
  have essential := entry.carrierProfile.erase_not_complete carrier member
  exact fun complete => essential (Or.inl complete)

/-- **The canonical core draws on this entry's own supply.** -/
theorem essentialCore_subset_carriers :
    entry.essentialCore ⊆ entry.carriers.toFinset := by
  intro carrier member
  by_contra outside
  refine entry.essentialCore_erase_not_complete member ?_
  exact (entry.complete_congr (entry.retained_erase_of_not_mem outside)).mpr
    (entry.essentialCore_complete (entry.determined_of_mem_essentialCore member))

/-- **Deletion witnesses exist** (`lem:typeA-essential-deletion-witness`), at G.

For every essential carrier `c`, the `c`-deletion quotient of the core reading
is not target-complete: some realization of `ρ|_{𝒞 ∖ {c}}` has, in
`entry.actual`, a target truth different from the full reading's -- equivalently
(`lem:target-complete-quotient-composition`, the core being complete) from the
core reading's.  Nothing is assumed: it is forced by inclusion-minimality of the
core. -/
theorem exists_deletion_witness {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    ∃ ρ : entry.Realization,
      entry.Realizes (entry.retained (entry.essentialCore.erase carrier)) ρ ∧
        ¬ (Target (glue (entry.realize ρ) entry.actual) ↔
          Target (glue entry.full entry.actual)) := by
  by_contra absent
  refine entry.essentialCore_erase_not_complete member ?_
  intro ρ realizes
  by_contra different
  exact absent ⟨ρ, realizes, different⟩

/-- A deletion quotient really forgets a declared coordinate: if it retained the
same coordinates it would have the same realizations. -/
theorem retained_erase_ne {carrier : Carrier}
    (member : carrier ∈ entry.essentialCore) :
    entry.retained (entry.essentialCore.erase carrier) ≠
      entry.retained entry.essentialCore := by
  intro same
  refine entry.essentialCore_erase_not_complete member ?_
  exact (entry.complete_congr same).mpr
    (entry.essentialCore_complete (entry.determined_of_mem_essentialCore member))

/-- **Deletion witnesses are declared, and their carrier support contains the
deleted carrier** (`lem:typeA-deletion-witness-declared`). -/
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

/-- The selected entry's carrier-core facts: the core is complete or the entry is
undetermined (and then the core is empty), it lies in the entry's own supply,
and every essential carrier has a realization of the deleted restriction whose
target truth differs from the full reading's, together with a declared
forgotten coordinate using it. -/
def CarrierCoreFacts : Prop :=
  entry.CoreComplete entry.essentialCore ∧
    entry.essentialCore ⊆ entry.carriers.toFinset ∧
      ∀ carrier ∈ entry.essentialCore,
        entry.Determined ∧
        (∃ ρ : entry.Realization,
          entry.Realizes (entry.retained (entry.essentialCore.erase carrier)) ρ ∧
            ¬ (Target (glue (entry.realize ρ) entry.actual) ↔
              Target (glue entry.full entry.actual))) ∧
        ∃ r ∈ entry.coordinates,
          entry.car r ⊆ entry.essentialCore ∧ carrier ∈ entry.car r

theorem carrierCoreFacts : entry.CarrierCoreFacts := by
  dsimp [CarrierCoreFacts]
  refine ⟨entry.essentialCore_coreComplete, entry.essentialCore_subset_carriers, ?_⟩
  intro carrier member
  exact ⟨entry.determined_of_mem_essentialCore member,
    entry.exists_deletion_witness member,
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
