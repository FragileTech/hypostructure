import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Descent

/-!
# Node `[123]`: finite exact descent terminates in true route 8?

The decision is the reduced-rate test of `thm:large-budget-route8-only` at the
terminal stage `route8DescentChain` of the descent: the yes key
`route8StageRate` is the test, the no key `route8StageRateFailed` its exact
negation at the same stage.  On the yes arm the terminal stage carries a true
two-support route-`8` entry (`route8StageTrueEntryRow`), the input of node
`[124]`; the no arm ("failed reduced rate") is routed to the demand ledgers and
node `[181]`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[123]`, yes arm → node `[124]`**: the terminal stage passing the
reduced-rate test carries the terminal true two-support route-`8` entry. -/
@[reducible] noncomputable def route8StageTrueEntryRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8StageTrueEntry
    { Requires := [K .route8PeelingDescent, K .route8StageRate,
        K .route8UnifiedEntryCensus]
      Produces := [K .route8UnifiedTrueTwoCarrierEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedTrueTwoCarrierEntry)
        ⟨Graph.Contracts.RouteEight.route8StageTrueEntry data.toParameters
          inputs.current.object (inputs.get (K .route8PeelingDescent)).down
          (inputs.get (K .route8StageRate)).down
          (inputs.get (K .route8UnifiedEntryCensus)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[123]`**: decided by case analysis on the reduced-rate test at the
terminal stage. -/
noncomputable def route8StageOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (rateFresh : K .route8StageRate ∉ known)
    (failedFresh : K .route8StageRateFailed ∉ known) :
    Decision (K .route8StageRate) (K .route8StageRateFailed) previous :=
  Decision.run previous (K .route8StageRate) (K .route8StageRateFailed)
    `Hypostructure.Graph.Strategy.Spine.route8StageOutcomeDichotomy
    (Classical.choice (show Nonempty
        ((K .route8StageRate).At current ⊕
          (K .route8StageRateFailed).At current) from by
      by_cases rate : Route8StageRateStatement data.toParameters current.object
      · exact ⟨.inl ⟨rate⟩⟩
      · exact ⟨.inr ⟨rate⟩⟩))
    rateFresh failedFresh

end Hypostructure.Graph.Strategy.Spine
