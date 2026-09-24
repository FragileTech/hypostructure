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

/-! ## Nodes `[74]`/`[82]`: Type B exclusion on the active B2 ledger

The decision reads the one `K .typeBDisjointLedger` selected on this branch.
Its yes arm performs the manuscript's local B1/B2 charge sum on that exact
ledger and contradicts the support's negative net charge.  Its no arm publishes
the same ledger and its still-negative remaining core as the bridge residual.
The selected-entry nonnegativity is an internal subproof used only to construct
the declared decision arm, so no generic or support-detached charge fact is
published. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeBExclusionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBDisjointLedger) known]
    (closedFresh : K .typeBExcluded ∉ known)
    (residualFresh : K .typeBExclusionResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBExcluded) (K .typeBExclusionResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBExcluded) (K .typeBExclusionResidual)
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionDichotomy
    (by
      classical
      apply Classical.choice
      rcases (ExactLedger.get previous (K .typeBDisjointLedger)).down with
        canonical | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
          ledger, exact, postLedger, _groupedCoverage⟩ := canonical
        -- Both manuscript forms of an assigned support carry the negative net
        -- charge of its counted core (`def:typeB-assigned-ledger`).
        have negative : current.object.NegativeNetCharge canonicalPiece.vertices
            data.threshold data.dischargeScale := by
          rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;>
            exact negative
        let charge := ∑ vertex ∈ ledger.remainingCore,
          Graph.TypeBRefinedSupport.scaledCoreCharge current.object
            data.threshold data.dischargeScale canonicalPiece.vertices vertex
        have selectedNonnegative : (0 : Int) ≤ ledger.selectedEntryPayment₂ := by
          rw [Graph.TypeBRefinedSupport.DisjointLedger.selectedEntryPayment₂]
          refine Finset.sum_nonneg ?_
          intro centre _member
          exact (ledger.entry_isCandidate centre.1 centre.2).entryRefines
        by_cases clean : (0 : Int) ≤ charge
        · have nonnegative :=
            Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative
              (object := current.object) ledger exact selectedNonnegative clean
          exact ⟨.inl ⟨.inl ⟨packing, valid, maximal, canonicalPiece,
            centres, assigned, nonnegative⟩⟩⟩
        · exact ⟨.inr ⟨packing, valid, maximal, canonicalPiece,
            centres, assigned, ledger, exact, postLedger,
            by simpa [charge] using clean⟩⟩
      · -- `[177]` has a successful B2 entry, so it follows the paper's
        -- yes edge `[74]`/`[82]` → `[76]`/`[85]`, never `[84]`.
        exact ⟨.inl ⟨.inr (.inl absorbed)⟩⟩
      · -- The same-token handoff has exactly the same successful B2(a)--(c)
        -- status.  Retain its literal packing, core, envelope, and choice on
        -- the yes edge; no canonical post-ledger core is asserted here.
        exact ⟨.inl ⟨.inr (.inr sameToken)⟩⟩)
    closedFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
