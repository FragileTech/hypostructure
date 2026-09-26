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

/-- **Nodes `[71]`/`[80]`: certificate labelling present?**  The yes key says every
assigned centre of every Type B support is certificate-marked
(`def:marked-typeB-fan`); the no key is its exact negation, a fan-certificate
residual centre. -/
noncomputable def fanCertificateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known) :
    Decision (K .fanCertificateMarked) (K .fanCertificateResidual) previous :=
  Decision.run previous (K .fanCertificateMarked) (K .fanCertificateResidual)
    `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy
    (Classical.choice (show Nonempty
        ((K .fanCertificateMarked).At current ⊕ (K .fanCertificateResidual).At current) from by
      by_cases holds : TypeBFanCertificateMarkedStatement data.toParameters current.object
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨(Contracts.TypeB.typeBFanCertificateResidual_iff_not_marked).mpr holds⟩⟩))
    markedFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
