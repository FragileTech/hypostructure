import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.Entropy

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Nodes `[131]`, `[137]` and `[138]`: the entropy count, the certified capacity
ledger, and the square-root surplus estimate

`prop:sparse-entropy-sandwich-with-blockers` rests on one count —
`lem:independent-target-entropy` with `lem:skeleton-dominates`: the mixed family
`ℐ_spine ∪ ℛ_Π` realizes its full code among the labelled skeletons of the
current object.  Per the methodology it is a decision on the literal residual:
the yes arm carries the count and continues the manuscript's chain, the no arm is
the residual on which it fails, carried as its own branch.  On the yes arm the
rest is arithmetic already proved in `Graph.SparsePressureLedger`. -/

/-- Node `[131]`: the entropy count of `prop:sparse-entropy-sandwich` at the full
pair schedule, decided on the literal independent residual of `[130]`.  The
decision reads G's node-`[129]` spine family and G's canonical activation from
their keys and splits on the count at exactly those two objects; the count-fails
arm is its literal negation. -/
noncomputable def freePairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .independentPairFamily) known]
    (sandwichFresh : K .freePairEntropySandwich ∉ known)
    (failsFresh : K .freePairCountFails ∉ known) :
    Decision (K .freePairEntropySandwich) (K .freePairCountFails) previous := by
  classical
  exact Decision.run previous (K .freePairEntropySandwich)
    (K .freePairCountFails)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (Classical.choice (show Nonempty
        ((K .freePairEntropySandwich).At current ⊕
          (K .freePairCountFails).At current) from by
      obtain ⟨spine, spineSelected, -⟩ :=
        (previous.get (K .baselineSpineDemand)).down
      obtain ⟨activation, activationSelected, -⟩ :=
        (previous.get (K .independentPairFamily)).down
      by_cases count : 2 ^ (spine.family.card +
          (activation.pairFamily
            (current.object.portPairSchedule data.threshold)).card) ≤
        Graph.skeletonBudget current.object
      · exact ⟨.inl ⟨⟨activation, spine, activationSelected, spineSelected, count⟩⟩⟩
      · refine ⟨.inr ⟨?_⟩⟩
        rintro ⟨activation', spine', activationSelected', spineSelected', count'⟩
        obtain rfl := Option.some.inj
          (activationSelected'.symm.trans activationSelected)
        obtain rfl := Option.some.inj (spineSelected'.symm.trans spineSelected)
        exact count count'))
    sandwichFresh failsFresh

/-- Node `[131]`, count fails: at G's node-`[129]` spine family and G's canonical
activation, the failure is the failure on the literal blocker-free schedule,
with the canonical realization of the spine family's code; this is node
`[178]`'s input. -/
@[reducible] noncomputable def freePairCodeUnrealizedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairCodeUnrealized
    { Requires := [K .freePairCountFails, K .baselineSpineDemand,
        K .independentPairFamily]
      Produces := [K .freePairCodeUnrealized]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .freePairCodeUnrealized)
        ⟨Graph.Contracts.SurplusPair.freePairCodeUnrealized_of_countFails
          inputs.current.baseline
          (inputs.get (K .freePairCountFails)).down
          (inputs.get (K .baselineSpineDemand)).down
          (inputs.get (K .independentPairFamily)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
