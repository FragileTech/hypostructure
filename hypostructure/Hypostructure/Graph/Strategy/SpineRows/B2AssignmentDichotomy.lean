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

/-- **Nodes `[72]`/`[81]`: B2 disjointness holds?**  The yes key is the disjoint
choice of candidate entries at every Type B support
(`def:typeB-bridge-statements` B2); the no key is its exact negation in the
positive form of `lem:typeB-bridge-to-overlap`: a minimal overlap obstruction
(`[73]`/`[83]`). -/
noncomputable def b2AssignmentDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known) :
    Decision (K .typeBB2Choice) (K .typeBOverlapObstruction) previous :=
  Decision.run previous (K .typeBB2Choice) (K .typeBOverlapObstruction)
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBB2Choice).At current ⊕ (K .typeBOverlapObstruction).At current) from by
      by_cases holds : TypeBB2ChoiceStatement data.toParameters current.object
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨(Contracts.TypeB.typeBB2Obstruction_iff_not_choice).mpr holds⟩⟩))
    choiceFresh obstructionFresh

end Hypostructure.Graph.Strategy.Spine
