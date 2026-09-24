import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[123]`, the failed-rate stage: demand absorption and window
blockers

`def:typeA-pressure-absorbers` with `lem:typeA-pressure-absorber-no-overcount`:
on every committed maximal 2/3-demand ledger the demand units carry a
type-(A1)/(A2) absorption — with the type-(A2) set held, a maximal single-use
assignment of fresh cut incidences — and the kernel counting engine
(`DemandPartition.Partition.three_mul_card_le_of_absorption`) yields the
subtraction-free display `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`.  Then
`def:typeA-open-window-blocker` with `lem:typeA-open-window-blocker-count`:
every open demand unit's entry keeps a receiver below the baseline inside its
component support, so a boundary incidence leaves the remainder — landing in
the packed-window support by the set-difference reading of `R = G − W` — and
the generic fibre count (`DemandPartition.card_eq_sum_fibres`) partitions the
open demand as `𝖯_open = Σ_P B_open(P)`.  The blocker choice is a classical
witness, as everywhere in this lane. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
set_option maxHeartbeats 1000000 in
@[reducible] noncomputable def route8DemandAbsorptionRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8DemandAbsorption
    { Requires := [K .route8DemandLedger]
      Produces := [K .route8DemandAbsorption]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _ledger := inputs.get (K .route8DemandLedger)
      .cons (key := K .route8DemandAbsorption)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          show Route8DemandAbsorptionStatement data inputs.current.object
          unfold Route8DemandAbsorptionStatement
          refine fun P _pinnedP _maximalP _raw _defect => ?_
          obtain ⟨A, absorbedUnits, absorberSupplied, absorberSameSupport,
            absorbedDisjoint, maximalA⟩ :=
            Graph.DemandPartition.Partition.exists_maximal_absorption
              (P := P) P.demandUnits
              (Graph.Route8Census.supply inputs.current.object
                (canonicalWindowPacking data inputs.current.object))
              (∅ : Finset
                (Graph.Route8Census.Index inputs.current.object × Nat))
              (fun υ => s(υ.1.2.1, υ.1.2.1))
              (fun υ carrier =>
                carrier ∈ Graph.Route8.cutEdges inputs.current.object υ.1.1)
          have supplied : ∀ index ∈ P.three ∪ P.two,
              P.assigned index ⊆
                Graph.Route8Census.supply inputs.current.object
                  (canonicalWindowPacking data inputs.current.object) := by
            intro index memUnion
            have memEntries : index ∈
                Graph.Route8Census.entriesOfComponents inputs.current.object
                  (canonicalWindowPacking data inputs.current.object)
                  (route8UnifiedComponents data inputs.current.object)
                  data.threshold data.dischargeScale := by
              have memUnified : index ∈
                  route8UnifiedEntries data inputs.current.object := by
                rcases Finset.mem_union.mp memUnion with mem | mem
                · exact P.three_subset_entries mem
                · exact P.two_subset_entries mem
              simpa only [route8UnifiedEntries] using memUnified
            exact (P.assigned_available index memUnion).trans
              (Graph.Route8Census.core_subset_supply_ofComponents
                inputs.current.object
                (canonicalWindowPacking data inputs.current.object)
                (route8UnifiedComponents data inputs.current.object)
                data.threshold data.dischargeScale data.LengthOK index
                memEntries)
          have display :=
            Graph.DemandPartition.Partition.three_mul_card_le_of_absorption
              (Graph.Route8Census.supply inputs.current.object
                (canonicalWindowPacking data inputs.current.object))
              supplied A absorbedUnits absorberSupplied
              (∅ : Finset
                (Graph.Route8Census.Index inputs.current.object × Nat))
              (Finset.empty_subset _) absorbedDisjoint
          rw [Graph.Route8Census.card_supply] at display
          exact ⟨A, ∅, absorbedUnits, absorberSupplied, absorberSameSupport,
            Finset.empty_subset _, absorbedDisjoint, rfl, maximalA, display⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
