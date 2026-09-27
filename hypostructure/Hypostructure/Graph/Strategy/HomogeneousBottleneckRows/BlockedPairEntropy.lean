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

/-- Node `[137]`'s input: G's canonical capacity presentation (node `[136]`),
the schedule count of node `[134]`, and G's node-`[129]` spine family, read
through their keys before the free-side entropy count is decided. -/
@[reducible] noncomputable def blockedPairEntropySetupRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairEntropySetup
    { Requires := [K .capacityTokenLedger, K .canonicalPairLedger,
        K .baselineSpineDemand]
      Produces := [K .blockedPairEntropySetup]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedPairEntropySetup)
        ⟨Graph.Contracts.SurplusPair.blockedPairEntropySetup_of_ledgers
          (inputs.get (K .capacityTokenLedger)).down
          (inputs.get (K .canonicalPairLedger)).down
          (inputs.get (K .baselineSpineDemand)).down⟩
        .nil)

/-- Node `[137]`: the entropy count of
`prop:sparse-entropy-sandwich-with-blockers` on the free side of G's canonical
capacity charge, decided from the setup `[137]` input: the decision reads G's
canonical capacity presentation and spine family from the setup key and splits
on the free-side count at exactly those objects; the count-fails arm is its
literal negation. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    (sandwichFresh : K .blockedPairEntropySandwich ∉ known)
    (failsFresh : K .blockedPairCountFails ∉ known) :
    Decision (K .blockedPairEntropySandwich) (K .blockedPairCountFails)
      previous := by
  classical
  exact Decision.run previous (K .blockedPairEntropySandwich)
    (K .blockedPairCountFails)
    `Hypostructure.Graph.Strategy.Spine.blockedPairEntropyDichotomy
    (Classical.choice (show Nonempty
        ((K .blockedPairEntropySandwich).At current ⊕
          (K .blockedPairCountFails).At current) from by
      obtain ⟨capacity, spine, capacitySelected, spineSelected, -⟩ :=
        (previous.get (K .blockedPairEntropySetup)).down
      by_cases count : 2 ^ (spine.family.card +
          (codeFreeSide data.toParameters current.object capacity).card) ≤
        Graph.skeletonBudget current.object
      · exact ⟨.inl ⟨⟨capacity, capacitySelected, spine, spineSelected, count⟩⟩⟩
      · refine ⟨.inr ⟨?_⟩⟩
        rintro ⟨capacity', capacitySelected', spine', spineSelected', count'⟩
        obtain rfl := Option.some.inj
          (capacitySelected'.symm.trans capacitySelected)
        obtain rfl := Option.some.inj (spineSelected'.symm.trans spineSelected)
        exact count count'))
    sandwichFresh failsFresh

/-- Node `[137]`, count fails on the free side: at G's canonical capacity
presentation and spine family, the failure with the canonical realization of
the spine family's code; this is node `[178]`'s input. -/
@[reducible] noncomputable def blockedPairCodeUnrealizedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairCodeUnrealized
    { Requires := [K .blockedPairCountFails, K .blockedPairEntropySetup,
        K .baselineSpineDemand]
      Produces := [K .blockedPairCodeUnrealized]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedPairCodeUnrealized)
        ⟨Graph.Contracts.SurplusPair.blockedPairCodeUnrealized_of_countFails
          (inputs.get (K .blockedPairCountFails)).down
          (inputs.get (K .blockedPairEntropySetup)).down
          (inputs.get (K .baselineSpineDemand)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
