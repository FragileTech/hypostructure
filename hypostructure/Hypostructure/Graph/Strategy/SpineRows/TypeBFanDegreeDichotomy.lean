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

/-- **Node `[68]`: some center has `d_G(h) > 4`?**  The decision reads the
node-`[65]` entry (`K .typeBFanEntry`, on the `[19]` at-or-below arm) and splits
at its Type B support `X`: some assigned centre of `X` is heavy
(`K .typeBFanHeavyCentre`), or every assigned centre of `X` has the
high-but-not-heavy degree `δ + 1` (`K .typeBFanDegreeFourCentres`). -/
noncomputable def typeBFanDegreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known) :
    Decision (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres) previous :=
  Decision.run previous (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres)
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBFanHeavyCentre).At current ⊕ (K .typeBFanDegreeFourCentres).At current) from by
      rcases Contracts.TypeB.typeBFanDegree_split
          (ExactLedger.get previous (K .typeBFanEntry)).down
          (ExactLedger.get previous (K .surplusAtOrBelow)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    heavyFresh degreeFourFresh

end Hypostructure.Graph.Strategy.Spine
