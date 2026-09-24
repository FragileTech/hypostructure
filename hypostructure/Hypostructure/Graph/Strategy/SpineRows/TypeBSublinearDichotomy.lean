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

/-! ## The tested sublinear hypotheses of `prop:typeB-bridge-sublinear`

The `[113]` pattern: the manuscript's bridge-sublinear hypotheses — the flat
off-centre pair at every negative positive-surplus piece and the grouped
fan-assignment data at the handoff pieces — are tested exactly, never assumed.
The yes arm feeds the unified deficit; the no arm retains the literal negation
as the tested Part IX bridge-residual state. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeBSublinearDichotomy
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
    (ledgerFresh : K .typeBSublinearLedger ∉ known)
    (residualFresh : K .typeBSublinearResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBSublinearLedger) (K .typeBSublinearResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBSublinearLedger) (K .typeBSublinearResidual)
    `Hypostructure.Graph.Strategy.Spine.typeBSublinearDichotomy
    (by
      classical
      exact if hypotheses : TypeBSublinearHypotheses data current.object then
        .inl ⟨hypotheses⟩
      else
        .inr ⟨hypotheses⟩)
    ledgerFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
