import Hypostructure.Graph.Contracts.RouteEight.DemandLedger

/-!
# Contracts: the node-`[181]` absorption and window-blocker ledgers

* `def:typeA-pressure-absorbers` with `lem:typeA-pressure-absorber-no-overcount`
  (`route8DemandAbsorption`);
* the (O2) step of `lem:typeA-routed-overload-not-open`
  (`route8OpenBoundarySaturated`) and the demand-unit count
  (`route8DemandUnitCount`);
* `def:typeA-open-window-blocker` with `lem:typeA-open-window-blocker-count`
  (`route8WindowBlockers`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`def:typeA-pressure-absorbers` with
`lem:typeA-pressure-absorber-no-overcount`**: every committed maximal
`2/3`-demand ledger carries a maximal same-support single-use absorption with
empty type-(A2) set, and `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`. -/
theorem exists_route8AbsorptionSpec (data : Parameters)
    (object : FiniteObject.{u})
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    ∃ x : DemandPartition.Absorption P (Route8Census.Index object × Nat) ×
        Finset (Route8Census.Index object × Nat),
      Route8AbsorptionSpec data object P x.1 x.2 := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨A, absorbedUnits, absorberSupplied, absorberSameSupport,
    absorbedDisjoint, maximalA⟩ :=
    Graph.DemandPartition.Partition.exists_maximal_absorption
      (P := P) P.demandUnits
      (Graph.Route8Census.supply object
        (canonicalWindowPacking data object))
      (∅ : Finset
        (Graph.Route8Census.Index object × Nat))
      (fun υ => s(υ.1.2.1, υ.1.2.1))
      (fun υ carrier =>
        carrier ∈ Graph.Route8.cutEdges object υ.1.1)
  have supplied : ∀ index ∈ P.three ∪ P.two,
      P.assigned index ⊆
        Graph.Route8Census.supply object
          (canonicalWindowPacking data object) := by
    intro index memUnion
    have memEntries : index ∈
        Graph.Route8Census.entriesOfComponents object
          (canonicalWindowPacking data object)
          (route8UnifiedComponents data object)
          data.threshold data.dischargeScale := by
      have memUnified : index ∈
          route8UnifiedEntries data object := by
        rcases Finset.mem_union.mp memUnion with mem | mem
        · exact P.three_subset_entries mem
        · exact P.two_subset_entries mem
      simpa only [route8UnifiedEntries] using memUnified
    exact (P.assigned_available index memUnion).trans
      (Graph.Route8Census.core_subset_supply_ofComponents
        object
        (canonicalWindowPacking data object)
        (route8UnifiedComponents data object)
        data.threshold data.dischargeScale data.LengthOK index
        memEntries)
  have display :=
    Graph.DemandPartition.Partition.three_mul_card_le_of_absorption
      (Graph.Route8Census.supply object
        (canonicalWindowPacking data object))
      supplied A absorbedUnits absorberSupplied
      (∅ : Finset
        (Graph.Route8Census.Index object × Nat))
      (Finset.empty_subset _) absorbedDisjoint
  rw [Graph.Route8Census.card_supply] at display
  exact ⟨(A, ∅), absorbedUnits, absorberSupplied, absorberSameSupport,
    Finset.empty_subset _, absorbedDisjoint, rfl, maximalA, display⟩

/-- **Node `[351]`** at the committed ledger `P₀`: the canonical absorption
`A₀` exists and has the displayed properties. -/
theorem route8DemandAbsorption (data : Parameters) (object : FiniteObject.{u})
    (ledger : Route8DemandLedgerStatement data object) :
    Route8DemandAbsorptionStatement data object := by
  obtain ⟨P, pin⟩ := canonicalRoute8Partition_exists data object ledger
  obtain ⟨x, xPin, spec⟩ := canonicalRoute8Absorption_spec data object P
    (exists_route8AbsorptionSpec data object P)
  exact ⟨P, pin, x, xPin, spec⟩

/-- **(O2) of `lem:typeA-routed-overload-not-open`**: after the committed
absorption is maximal, an open demand unit has no unused eligible boundary
incidence -- inserting it would enlarge the maximal absorption. -/
theorem openBoundarySaturated_of_absorptionSpec (data : Parameters)
    (object : FiniteObject.{u})
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : DemandPartition.Absorption P (Route8Census.Index object × Nat))
    (dep : Finset (Route8Census.Index object × Nat))
    (spec : Route8AbsorptionSpec data object P A dep) :
    ∀ unit ∈ P.demandUnits \ (A.absorbed ∪ dep),
      ∀ carrier : Sym2 object.Vertex,
        carrier ∈ Route8.cutEdges object unit.1.1 →
        (∀ index ∈ P.three ∪ P.two, carrier ∉ P.assigned index) →
        ∃ other ∈ A.absorbed, A.absorber other = carrier := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨absorbedUnits, supplied, sameSupport, _depUnits,
    disjoint, _depEmpty, maximalA, _display⟩ := spec
  intro unit openUnit carrier inSupport ledgerUnused
  by_contra notAssigned
  have unitMem := (Finset.mem_sdiff.mp openUnit).1
  have entryMem : unit.1 ∈ route8UnifiedEntries data object := by
    have unpaid :=
      Graph.DemandPartition.Partition.fst_mem_of_mem_demandUnits unitMem
    rcases Finset.mem_union.mp unpaid with inTwo | inResidual
    · exact P.two_subset_entries inTwo
    · exact P.residual_subset_entries inResidual
  change unit.1 ∈ Graph.Route8Census.entriesOfComponents
    object (canonicalWindowPacking data object)
    (route8UnifiedComponents data object)
    data.threshold data.dischargeScale at entryMem
  simp only [Graph.Route8Census.entriesOfComponents,
    Finset.mem_biUnion, Finset.mem_image] at entryMem
  obtain ⟨component, _componentMem, receiver, _receiverMem,
    load, _loadMem, indexEq⟩ := entryMem
  have pieceEq : unit.1.1 = object.pieceSupport
      (object.remainderSupport
        (canonicalWindowPacking data object)) component := by
    rw [← indexEq]
  have inSupply : carrier ∈ Graph.Route8Census.supply object
      (canonicalWindowPacking data object) := by
    apply Graph.Route8Census.cutEdges_piece_subset object
      (canonicalWindowPacking data object) component
    simpa only [← pieceEq] using inSupport
  have unitOutside := (Finset.mem_sdiff.mp openUnit).2
  have notAbsorbed : unit ∉ A.absorbed := fun h =>
    unitOutside (Finset.mem_union_left _ h)
  have notDep : unit ∉ dep := fun h =>
    unitOutside (Finset.mem_union_right _ h)
  have fresh : ∀ other ∈ A.absorbed, A.absorber other ≠ carrier := by
    intro other member same
    exact notAssigned ⟨other, member, same⟩
  let B : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat) :=
    { absorbed := insert unit A.absorbed
      absorber := fun other =>
        if other = unit then carrier else A.absorber other
      absorber_injective := by
        intro left leftMem right rightMem distinct
        by_cases leftEq : left = unit
        · subst left
          have rightNe : right ≠ unit := Ne.symm distinct
          have oldRight := (Finset.mem_insert.mp rightMem).resolve_left rightNe
          simpa [rightNe] using
            (fresh right oldRight).symm
        · by_cases rightEq : right = unit
          · subst right
            have oldLeft := (Finset.mem_insert.mp leftMem).resolve_left leftEq
            simpa [leftEq] using fresh left oldLeft
          · have oldLeft := (Finset.mem_insert.mp leftMem).resolve_left leftEq
            have oldRight := (Finset.mem_insert.mp rightMem).resolve_left rightEq
            simpa only [if_neg leftEq, if_neg rightEq] using
              A.absorber_injective left oldLeft right oldRight distinct
      absorber_unused := by
        intro other member index indexMem
        by_cases same : other = unit
        · subst other
          simpa using ledgerUnused index indexMem
        · have old := (Finset.mem_insert.mp member).resolve_left same
          simpa only [if_neg same] using A.absorber_unused other old index indexMem }
  have unitsB : B.absorbed ⊆ P.demandUnits :=
    Finset.insert_subset unitMem absorbedUnits
  have suppliedB : ∀ other ∈ B.absorbed, B.absorber other ∈
      Graph.Route8Census.supply object
        (canonicalWindowPacking data object) := by
    intro other member
    by_cases same : other = unit
    · subst other
      simpa [B] using inSupply
    · have old := (Finset.mem_insert.mp member).resolve_left same
      simpa only [B, if_neg same] using supplied other old
  have supportB : ∀ other ∈ B.absorbed, B.absorber other ∈
      Graph.Route8.cutEdges object other.1.1 := by
    intro other member
    by_cases same : other = unit
    · subst other
      simpa [B] using inSupport
    · have old := (Finset.mem_insert.mp member).resolve_left same
      simpa only [B, if_neg same] using sameSupport other old
  have disjointB : Disjoint B.absorbed dep := by
    exact Finset.disjoint_insert_left.mpr ⟨notDep, disjoint⟩
  have bound := maximalA B unitsB suppliedB supportB disjointB
  change (insert unit A.absorbed).card ≤ A.absorbed.card at bound
  rw [Finset.card_insert_of_notMem notAbsorbed] at bound
  omega

/-- **Node `[517]`** at `(P₀, A₀)`, reading node `[351]`. -/
theorem route8OpenBoundarySaturated (data : Parameters)
    (object : FiniteObject.{u})
    (absorption : Route8DemandAbsorptionStatement data object) :
    Route8OpenBoundarySaturatedStatement data object := by
  obtain ⟨P, pin, x, xPin, spec⟩ := absorption
  exact ⟨P, pin, x, xPin,
    openBoundarySaturated_of_absorptionSpec data object P x.1 x.2 spec⟩

/-- The actual demand units of every ledger number exactly its external
demand defect `𝖯_ext = N₂ + 3N_res`. -/
theorem demandUnits_card_eq_externalDefect (data : Parameters)
    (object : FiniteObject.{u})
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    P.demandUnits.card = P.externalDefect := by
  classical
  have blocks : ∀ index ∈ P.two ∪ P.residual,
      (((Finset.range (P.demandWeight index)).image
        fun j => (index, j)).card) = P.demandWeight index := by
    intro index _member
    rw [Finset.card_image_of_injective _ fun a b equal =>
      (Prod.mk.injEq index a index b).mp equal |>.2]
    exact Finset.card_range _
  have disjointBlocks : ∀ left ∈ P.two ∪ P.residual,
      ∀ right ∈ P.two ∪ P.residual, left ≠ right →
      Disjoint
        ((Finset.range (P.demandWeight left)).image fun j => (left, j))
        ((Finset.range (P.demandWeight right)).image fun j => (right, j)) := by
    intro left _leftMem right _rightMem distinct
    rw [Finset.disjoint_left]
    rintro ⟨entry, j⟩ leftMem rightMem
    obtain ⟨_, _, equalLeft⟩ := Finset.mem_image.mp leftMem
    obtain ⟨_, _, equalRight⟩ := Finset.mem_image.mp rightMem
    exact distinct ((((Prod.mk.injEq _ _ _ _).mp equalLeft).1).trans
      (((Prod.mk.injEq _ _ _ _).mp equalRight).1).symm)
  rw [Graph.DemandPartition.Partition.demandUnits,
    Finset.card_biUnion disjointBlocks,
    Graph.DemandPartition.Partition.externalDefect_eq_sum_demandWeight]
  exact Finset.sum_congr rfl blocks

/-- **Node `[518]`** at `P₀`, read from node `[351]`'s pin. -/
theorem route8DemandUnitCount (data : Parameters) (object : FiniteObject.{u})
    (absorption : Route8DemandAbsorptionStatement data object) :
    Route8DemandUnitCountStatement data object := by
  obtain ⟨P, pin, _⟩ := absorption
  exact ⟨P, pin, demandUnits_card_eq_externalDefect data object P⟩

/-- **`def:typeA-open-window-blocker` with
`lem:typeA-open-window-blocker-count`**: on the unified census every open
demand unit has an actual available carrier edge of its owner leaving the
remainder into a packed window, and `𝖯_open = Σ_P B_open(P)`. -/
theorem exists_route8WindowBlockerSpec (data : Parameters)
    (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : DemandPartition.Absorption P (Route8Census.Index object × Nat))
    (dep : Finset (Route8Census.Index object × Nat)) :
    ∃ y : (Route8Census.Index object × Nat → Sym2 object.Vertex) ×
        (Route8Census.Index object × Nat → Finset object.Vertex),
      Route8WindowBlockerSpec data object P A dep y.1 y.2 := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let entries := route8UnifiedEntries data object
  let core := route8DemandCore data object
  let openUnits := P.demandUnits \ (A.absorbed ∪ dep)
  have blockerAt : ∀ υ :
      Graph.Route8Census.Index object × Nat,
      ∃ carrier : Sym2 object.Vertex,
        ∃ window : Finset object.Vertex,
          υ ∈ openUnits →
            carrier ∈ core υ.1 ∧
              ∃ inside ∈ carrier, ∃ outside ∈ carrier,
                inside ∈ remainder ∧ outside ∉ remainder ∧
                  outside ∈ window ∧ window ∈ packing := by
    intro υ
    by_cases υMem : υ ∈ openUnits
    · have unitMem : υ ∈ P.demandUnits :=
        (Finset.mem_sdiff.mp υMem).1
      have fstMem :=
        Graph.DemandPartition.Partition.fst_mem_of_mem_demandUnits
          unitMem
      have entryMem : υ.1 ∈ entries := by
        rcases Finset.mem_union.mp fstMem with mem | mem
        · exact P.two_subset_entries mem
        · exact P.residual_subset_entries mem
      have alphaAtLeast := (census υ.1 entryMem).2.1
      have coreNonempty : (core υ.1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro empty
        have zero : (core υ.1).card = 0 := by rw [empty]; simp
        change 2 ≤ (core υ.1).card at alphaAtLeast
        omega
      obtain ⟨carrier, carrierMem⟩ := coreNonempty
      have entryMem' : υ.1 ∈
          Graph.Route8Census.entriesOfComponents
            object packing
            (route8UnifiedComponents data object)
            data.threshold data.dischargeScale := by
        simpa only [entries, route8UnifiedEntries] using entryMem
      have carrierSupply : carrier ∈
          Graph.Route8Census.supply object packing :=
        Graph.Route8Census.core_subset_supply_ofComponents
          object packing
          (route8UnifiedComponents data object)
          data.threshold data.dischargeScale data.LengthOK υ.1
          entryMem' carrierMem
      change carrier ∈ Graph.Route8.cutEdges object
        remainder at carrierSupply
      rw [Graph.Route8.mem_cutEdges] at carrierSupply
      obtain ⟨_edgeMem, inside, insideMem, outside, outsideMem,
        insideRemainder, outsideRemainder⟩ := carrierSupply
      obtain ⟨window, windowMem, outsideWindow⟩ :=
        object.exists_mem_packing_of_notMem_remainderSupport
          outsideRemainder
      exact ⟨carrier, window, fun _ =>
        ⟨carrierMem, inside, insideMem, outside, outsideMem,
          insideRemainder, outsideRemainder, outsideWindow,
          windowMem⟩⟩
    · refine ⟨s(υ.1.2.1, υ.1.2.1), ∅, ?_⟩
      intro present
      exact (υMem present).elim
  choose carrier blocker blockerSpec using blockerAt
  have assigned : ∀ υ ∈ openUnits,
      carrier υ ∈ core υ.1 ∧
        ∃ inside ∈ carrier υ, ∃ outside ∈ carrier υ,
          inside ∈ remainder ∧ outside ∉ remainder ∧
            outside ∈ blocker υ ∧ blocker υ ∈ packing := by
    intro υ υMem
    exact blockerSpec υ υMem
  have assignedWindow : ∀ υ ∈ openUnits,
      blocker υ ∈ packing := by
    intro υ υMem
    obtain ⟨_carrierMem, inside, _insideMem, outside, _outsideMem,
      _insideRemainder, _outsideRemainder, _outsideWindow,
      windowMem⟩ := assigned υ υMem
    exact windowMem
  exact ⟨(carrier, blocker), assigned,
    Graph.DemandPartition.card_eq_sum_fibres openUnits packing blocker
      assignedWindow⟩

/-- **Node `[352]`** at `(P₀, A₀)`: the canonical window blocker `b₀`, read
from the unified census and node `[351]`. -/
theorem route8WindowBlockers (data : Parameters) (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    (absorption : Route8DemandAbsorptionStatement data object) :
    Route8WindowBlockersStatement data object := by
  obtain ⟨P, pin, x, xPin, _spec⟩ := absorption
  obtain ⟨y, yPin, spec⟩ := canonicalRoute8WindowBlocker_spec data object P x.1
    x.2 (exists_route8WindowBlockerSpec data object census P x.1 x.2)
  exact ⟨P, pin, x, xPin, y, yPin, spec⟩

end Hypostructure.Graph.Contracts.RouteEight
