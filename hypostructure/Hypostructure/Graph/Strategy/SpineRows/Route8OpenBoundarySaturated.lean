import Hypostructure.Graph.Strategy.SpineVocabulary

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The (O2) step of `lem:typeA-routed-overload-not-open`: an open unit has
no unused eligible boundary incidence after the committed absorption is
maximal. The proof inserts that very unit and incidence into the same
assignment and contradicts its retained maximality. -/
@[reducible] noncomputable def route8OpenBoundarySaturatedRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8OpenBoundarySaturated
    { Requires := [K .route8DemandAbsorption]
      Produces := [K .route8OpenBoundarySaturated, K .route8DemandUnitCount]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8OpenBoundarySaturated)
        (show Value BranchState Presentation presentation data
            .route8OpenBoundarySaturated inputs.current from ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          show Route8OpenBoundarySaturatedStatement data inputs.current.object
          unfold Route8OpenBoundarySaturatedStatement
          refine fun P pinnedP maximalP raw defect => ?_
          obtain ⟨A, dep, absorbedUnits, supplied, sameSupport, depUnits,
            disjoint, depEmpty, maximalA, display⟩ :=
            (inputs.get (K .route8DemandAbsorption)).down
              P pinnedP maximalP raw defect
          refine ⟨A, dep, absorbedUnits, supplied, sameSupport, depUnits,
            disjoint, depEmpty, maximalA, display, ?_⟩
          intro unit openUnit carrier inSupport ledgerUnused
          by_contra notAssigned
          have unitMem := (Finset.mem_sdiff.mp openUnit).1
          have entryMem : unit.1 ∈ route8UnifiedEntries data inputs.current.object := by
            have unpaid :=
              Graph.DemandPartition.Partition.fst_mem_of_mem_demandUnits unitMem
            rcases Finset.mem_union.mp unpaid with inTwo | inResidual
            · exact P.two_subset_entries inTwo
            · exact P.residual_subset_entries inResidual
          change unit.1 ∈ Graph.Route8Census.entriesOfComponents
            inputs.current.object (canonicalWindowPacking data inputs.current.object)
            (route8UnifiedComponents data inputs.current.object)
            data.threshold data.dischargeScale at entryMem
          simp only [Graph.Route8Census.entriesOfComponents,
            Finset.mem_biUnion, Finset.mem_image] at entryMem
          obtain ⟨component, _componentMem, receiver, _receiverMem,
            load, _loadMem, indexEq⟩ := entryMem
          have pieceEq : unit.1.1 = inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component := by
            rw [← indexEq]
          have inSupply : carrier ∈ Graph.Route8Census.supply inputs.current.object
              (canonicalWindowPacking data inputs.current.object) := by
            apply Graph.Route8Census.cutEdges_piece_subset inputs.current.object
              (canonicalWindowPacking data inputs.current.object) component
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
              (Graph.Route8Census.Index inputs.current.object × Nat) :=
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
              Graph.Route8Census.supply inputs.current.object
                (canonicalWindowPacking data inputs.current.object) := by
            intro other member
            by_cases same : other = unit
            · subst other
              simpa [B] using inSupply
            · have old := (Finset.mem_insert.mp member).resolve_left same
              simpa only [B, if_neg same] using supplied other old
          have supportB : ∀ other ∈ B.absorbed, B.absorber other ∈
              Graph.Route8.cutEdges inputs.current.object other.1.1 := by
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
          omega⟩)
        (.cons (key := K .route8DemandUnitCount)
          (show Value BranchState Presentation presentation data
              .route8DemandUnitCount inputs.current from ⟨by
            classical
            intro P
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
            exact Finset.sum_congr rfl blocks⟩)
          .nil))

end Hypostructure.Graph.Strategy.Spine
