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

/-- **Nodes `[72]`/`[81]`: local fan-window ledger complete?**  The decision
reads the marked fact (`K .fanCertificateMarked`) and splits at its Type B
support `X`: some assigned centre of `X` carries a direct fan-window
configuration at `P₀` (`lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`), or every assigned centre of `X` is
direct-cycle free (`def:direct-cycle-free-closed-pair`). -/
noncomputable def directCycleDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known) :
    Decision (K .typeBDirectCycle) (K .typeBDirectCycleFree) previous :=
  Decision.run previous (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBDirectCycle).At current ⊕ (K .typeBDirectCycleFree).At current) from by
      rcases Contracts.TypeB.directCycle_split
          (ExactLedger.get previous (K .fanCertificateMarked)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    cycleFresh freeFresh

/-- **The direct-cycle arm closes.**  A direct fan-window configuration builds a
cycle of accepted length, which the selection denies; the framework appends the
closure key from the two committed facts. -/
noncomputable instance instIncompatibleSelectionTypeBDirectCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeBDirectCycle) where
  contradiction := fun _input selection cycle =>
    selection.down.1
      (Contracts.TypeB.hasCycleWithLength_of_typeBFanDirectCycle cycle.down)

end Hypostructure.Graph.Strategy.Spine
