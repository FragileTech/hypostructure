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
pair schedule, decided by exact case analysis on its predicate.  The count-fails
arm is its literal negation. -/
noncomputable def freePairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (sandwichFresh : K .freePairEntropySandwich ∉ known)
    (failsFresh : K .freePairCountFails ∉ known) :
    Decision (K .freePairEntropySandwich) (K .freePairCountFails) previous := by
  classical
  exact Decision.run previous (K .freePairEntropySandwich)
    (K .freePairCountFails)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (if realized : Holds BranchState Presentation presentation data
        .freePairEntropySandwich current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨realized⟩)
    sandwichFresh failsFresh

/-- Node `[131]`, count fails: the failure is the failure for the node-`[129]`
baseline family itself, with its first failed pair extension on the literal
blocker-free pair schedule; this is node `[178]`'s input. -/
@[reducible] noncomputable def freePairCodeUnrealizedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairCodeUnrealized
    { Requires := [K .freePairCountFails, K .baselineSpineDemand,
        K .independentPairFamily, K .incrementalSkeletonRoom]
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
          (inputs.get (K .independentPairFamily)).down
          (inputs.get (K .incrementalSkeletonRoom)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
