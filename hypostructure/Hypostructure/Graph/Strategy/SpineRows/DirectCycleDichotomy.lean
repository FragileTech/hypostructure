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

/-- **Nodes `[72]`/`[81]`: local fan-window ledger complete?**  The yes key is a
direct fan-window configuration at some assigned centre
(`lem:typeB-direct-fan-window-cycles`, `lem:typeB-two-window-cycles`); the no
key is its exact negation, `def:direct-cycle-free-closed-pair` at every
assigned centre. -/
noncomputable def directCycleDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known) :
    Decision (K .typeBDirectCycle) (K .typeBDirectCycleFree) previous :=
  Decision.run previous (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBDirectCycle).At current ⊕ (K .typeBDirectCycleFree).At current) from by
      by_cases holds : TypeBFanDirectCycleStatement data.toParameters current.object
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨(Contracts.TypeB.typeBFanDirectCycleFree_iff_not_directCycle).mpr holds⟩⟩))
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
