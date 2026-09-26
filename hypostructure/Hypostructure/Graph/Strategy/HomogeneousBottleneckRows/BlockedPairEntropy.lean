import Hypostructure.Graph.Strategy.SpineVocabulary
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

/-- Node `[137]`: the entropy count of
`prop:sparse-entropy-sandwich-with-blockers` on the free side of the capacity
charge, decided by exact case analysis on its predicate.  The count-fails arm
is its literal negation. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (sandwichFresh : K .blockedPairEntropySandwich ∉ known)
    (failsFresh : K .blockedPairCountFails ∉ known) :
    Decision (K .blockedPairEntropySandwich) (K .blockedPairCountFails)
      previous := by
  classical
  exact Decision.run previous (K .blockedPairEntropySandwich)
    (K .blockedPairCountFails)
    `Hypostructure.Graph.Strategy.Spine.blockedPairEntropyDichotomy
    (if realized : Holds BranchState Presentation presentation data
        .blockedPairEntropySandwich current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨realized⟩)
    sandwichFresh failsFresh

/-- Node `[137]`, count fails on the free side: at the object's capacity-token
and canonical pair ledgers and the node-`[129]` baseline family, the failure is
the failure for that presentation and family, with its first failed free-pair
extension; this is node `[178]`'s input. -/
@[reducible] noncomputable def blockedPairCodeUnrealizedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairCodeUnrealized
    { Requires := [K .blockedPairCountFails, K .capacityTokenLedger,
        K .canonicalPairLedger, K .baselineSpineDemand]
      Produces := [K .blockedPairCodeUnrealized]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedPairCodeUnrealized)
        ⟨Graph.Contracts.SurplusPair.blockedPairCodeUnrealized_of_countFails
          (inputs.get (K .blockedPairCountFails)).down
          (inputs.get (K .capacityTokenLedger)).down
          (inputs.get (K .canonicalPairLedger)).down
          (inputs.get (K .baselineSpineDemand)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
