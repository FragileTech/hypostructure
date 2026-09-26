import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Nodes `[71]`/`[80]`: certificate labelling present?**  The decision reads
the node-`[70]` cap (`K .fanCertificateCap`) and splits at its Type B support:
every assigned centre is certificate-marked (`def:marked-typeB-fan`), or one of
them is a fan-certificate residual centre. -/
noncomputable def fanCertificateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fanCertificateCap) known]
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known) :
    Decision (K .fanCertificateMarked) (K .fanCertificateResidual) previous :=
  Decision.run previous (K .fanCertificateMarked) (K .fanCertificateResidual)
    `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy
    (Classical.choice (show Nonempty
        ((K .fanCertificateMarked).At current ⊕ (K .fanCertificateResidual).At current) from by
      rcases Contracts.TypeB.fanCertificate_split
          (ExactLedger.get previous (K .fanCertificateCap)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    markedFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
