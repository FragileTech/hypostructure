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

/-! ## Nodes `[73]`/`[83]`: full global-to-local bridge

The B2 failure already carries the cardinality-minimal obstruction.  This row
does not rebuild it: it reads that exact obstruction, selection, and global
high-centre normal form from the incoming ledger and appends the five-clause
reflection.  The indexed and same-token handoff carriers are retained without
being coerced into canonical remainder components. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBGlobalLocalBridgeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBGlobalLocalBridge
    { Requires := [K .typeBOverlapObstruction, K .selection,
        K .highCentreNormalForm]
      Produces := [K .typeBGlobalLocalBridge]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let normalForms := (inputs.get (K .highCentreNormalForm)).down
      .cons (key := K .typeBGlobalLocalBridge)
        (⟨by
          classical
          rcases (inputs.get (K .typeBOverlapObstruction)).down with
            canonical | absorbed | sameToken
          · obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
                ⟨obstruction⟩⟩ := canonical
            have directFree : ∀ hub ∈ obstruction.demands,
                Graph.TypeBDirectCycle.DirectCycleFree inputs.current.object
                  data.windowOrder data.LengthOK packing hub := by
              intro hub _hubMem configuration
              exact avoids
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid configuration)
            have reflected :=
              Graph.TypeBRefinedSupport.globalLocalReflectionACE
                (presentation := data.typeABPresentation)
                (order := data.windowOrder) (LengthOK := data.LengthOK)
                (threshold := data.threshold)
                (dischargeScale := data.dischargeScale)
                obstruction
                (by
                  simpa [Graph.TypeAB.ContextuallyDyadicSafe,
                    Data.typeABPresentation] using avoids)
                (fun hub hubMem => normalForms hub
                  (obstruction.demands_high hub hubMem))
                directFree
            exact Or.inl ⟨packing, valid, maximal, canonicalPiece, centres,
              assigned, obstruction, reflected⟩
          · exact Or.inr (Or.inl absorbed)
          · exact Or.inr (Or.inr sameToken)⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
