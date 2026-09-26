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

/-- **Nodes `[72]`/`[81]`: B2 disjointness holds?**  The decision reads the
direct-cycle-free fact (`K .typeBDirectCycleFree`) and splits at its Type B
support `X`: the assigned centres of `X` admit a disjoint choice of candidate
entries at `P₀` (`def:typeB-bridge-statements` B2), or, in the positive form of
`lem:typeB-bridge-to-overlap`, `X` carries a minimal overlap obstruction
(`[73]`/`[83]`). -/
noncomputable def b2AssignmentDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known) :
    Decision (K .typeBB2Choice) (K .typeBOverlapObstruction) previous :=
  Decision.run previous (K .typeBB2Choice) (K .typeBOverlapObstruction)
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBB2Choice).At current ⊕ (K .typeBOverlapObstruction).At current) from by
      rcases Contracts.TypeB.b2_split
          (ExactLedger.get previous (K .typeBDirectCycleFree)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    choiceFresh obstructionFresh

end Hypostructure.Graph.Strategy.Spine
