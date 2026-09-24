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

/-! ## Node `[118]`: the selected two-support entry is a true route-8 entry

On the pure collection selected at `[111]`, `K .route8TrueResidual` already
records clauses (R1)--(R4), including the absence of the canonical exit-`(4)`
family.  This row attaches that exact no-exit fact to the entry selected by
`[117]`; the target-defect alternative belongs only to the unified peeling
ledger of `[123]`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8TrueTwoCarrierEntryRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.route8TrueTwoCarrierEntry
    { Requires := [K .route8TwoCarrierEntry, K .route8TrueResidual]
      Produces := [K .route8TrueTwoCarrierEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := inputs.get (K .route8TwoCarrierEntry)
      let trueResidual := inputs.get (K .route8TrueResidual)
      .cons (key := K .route8TrueTwoCarrierEntry)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          obtain ⟨index, indexMem, two⟩ := selected.down
          rcases index with ⟨piece, receiver, load⟩
          have indexSpec :
              (piece, receiver, load) ∈
                  Graph.Route8Census.entriesOfComponents inputs.current.object
                    (canonicalWindowPacking data inputs.current.object)
                    ((inputs.current.object.canonicalPieces
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))).filter
                      (Route8Survives data inputs.current.object
                        (canonicalWindowPacking data inputs.current.object)))
                    data.threshold data.dischargeScale ↔
                ∃ component ∈
                    ((inputs.current.object.canonicalPieces
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))).filter
                      (Route8Survives data inputs.current.object
                        (canonicalWindowPacking data inputs.current.object))),
                  piece = inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object)) component ∧
                    receiver ∈ Graph.VisibleEntry.saturatedReceivers
                      inputs.current.object piece data.threshold data.dischargeScale ∧
                    load ∈ Graph.VisibleEntry.excessBasin inputs.current.object piece
                      data.threshold data.dischargeScale receiver := by
            simp only [Graph.Route8Census.entriesOfComponents,
              Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
            constructor
            · rintro ⟨component, componentMem, receiver', receiverMem, load',
                loadMem, rfl, rfl, rfl⟩
              exact ⟨component, componentMem, rfl, receiverMem, loadMem⟩
            · rintro ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩
              subst piece
              exact ⟨component, componentMem, receiver, receiverMem, load,
                loadMem, rfl, rfl, rfl⟩
          obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
            indexSpec.mp indexMem
          change piece = inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object)) component at pieceEq
          subst piece
          have survives := (Finset.mem_filter.mp componentMem).2
          have componentFacts := trueResidual.down.2 component componentMem
          have receiverFacts := componentFacts.2 receiver receiverMem
          have exactDegree : ∀ vertex ∈ inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component,
              inputs.current.object.degree vertex = data.threshold := by
            intro vertex vertexMem
            have nonneg := le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
            have summand : inputs.current.object.degree vertex -
                data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (survives.2.1 ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) vertexMem)
            omega
          have silentLoadMem : load ∈ Graph.VisibleEntry.silentExcess
              inputs.current.object
              (inputs.current.object.pieceSupport
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)) component)
              data.threshold data.dischargeScale receiver := by
            rw [Graph.VisibleEntry.silentExcess_eq_excessBasin
              inputs.current.object _ data.threshold data.dischargeScale
              (exactDegree receiver receiverFacts.1.1) receiverFacts.1
              data.dischargeScale_pos
              (fun saturated =>
                componentFacts.1 receiver receiverFacts.1 saturated)]
            exact loadMem
          have noExitFour := (receiverFacts.2.2 load silentLoadMem).2.2
          exact ⟨_, indexMem, two, noExitFour⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
