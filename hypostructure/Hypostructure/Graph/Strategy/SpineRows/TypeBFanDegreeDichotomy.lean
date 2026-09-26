import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[68]`: some center has `d_G(h) > 4`?**  The yes key is
`typeBFanHeavyCentre` (some assigned centre of some Type B support is heavy);
the no key `typeBFanDegreeFourCentres` is its exact negation on the same
support family, normalized by the high-centre bound to `d_G(h) = δ + 1`. -/
noncomputable def typeBFanDegreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known) :
    Decision (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres) previous :=
  Decision.run previous (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres)
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBFanHeavyCentre).At current ⊕ (K .typeBFanDegreeFourCentres).At current) from by
      by_cases holds : TypeBFanHeavyCentreStatement data.toParameters current.object
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨(Contracts.TypeB.typeBFanDegreeFourCentres_iff_not_heavy).mpr holds⟩⟩))
    heavyFresh degreeFourFresh

end Hypostructure.Graph.Strategy.Spine
