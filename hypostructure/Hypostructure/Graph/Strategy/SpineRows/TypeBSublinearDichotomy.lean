import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Bridge

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}


/-! ## The tested sublinear hypotheses of `prop:typeB-bridge-sublinear`

The `[113]` pattern: the manuscript's bridge-sublinear hypotheses — the flat
off-centre pair at every negative positive-surplus piece and the grouped
fan-assignment data at the handoff pieces — are tested exactly, never assumed.
The decision reads its predecessor, the bridge-sublinear fact
`K .typeBBridgeSublinear` at the same `P₀` and canonical role unions.  The yes
arm feeds the unified deficit; the no arm retains the literal negation as the
tested Part IX bridge-residual state. -/
noncomputable def typeBSublinearDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    (ledgerFresh : K .typeBSublinearLedger ∉ known)
    (residualFresh : K .typeBSublinearResidual ∉ known) :
    Decision (K .typeBSublinearLedger) (K .typeBSublinearResidual) previous :=
  Decision.run previous (K .typeBSublinearLedger) (K .typeBSublinearResidual)
    `Hypostructure.Graph.Strategy.Spine.typeBSublinearDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBSublinearLedger).At current ⊕
          (K .typeBSublinearResidual).At current) from by
      rcases Contracts.TypeB.typeBSublinear_split
          (ExactLedger.get previous (K .typeBBridgeSublinear)).down with
        holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    ledgerFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
