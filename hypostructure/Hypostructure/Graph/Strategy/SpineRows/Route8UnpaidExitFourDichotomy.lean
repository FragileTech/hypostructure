import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.DemandLedger

/-!
# Node `[181]`: some unpaid entry lacks an exit-(4) witness?

`thm:typeA-unpaid-exit4-reduction` on the maximal demand ledgers of the
node-`[181]` residual.  The one-entry augmentation (168.1) is published first
(`route8UnpaidTwoCarrierRow`).  The decision then asks the paper's question:
the yes key `route8UnpaidWitnessFree` is outcome (i), the no key
`route8UnpaidExitFourResidual` its exact negation, outcome (ii) = node
`[183]`.  On the yes arm the witness-free entry is exactly the terminal input
of `thm:typeA-two-carrier-nogo` (`route8UnpaidTrueEntryRow`), closed at node
`[124]`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **(168.1)**: every unpaid entry of a maximal demand ledger is
two-support. -/
@[reducible] noncomputable def route8UnpaidTwoCarrierRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnpaidTwoCarrier
    { Requires := []
      Produces := [K .route8UnpaidTwoCarrier]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnpaidTwoCarrier)
        ⟨Graph.Contracts.RouteEight.route8UnpaidTwoCarrier data.toParameters
          inputs.current.object data.three_le_threshold⟩ .nil)
    0 0

/-- **Node `[181]`, yes arm → node `[124]`**: the witness-free unpaid entry is
the terminal true two-support route-`8` entry. -/
@[reducible] noncomputable def route8UnpaidTrueEntryRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnpaidTrueEntry
    { Requires := [K .route8UnpaidWitnessFree, K .route8UnpaidTwoCarrier,
        K .route8UnifiedEntryCensus]
      Produces := [K .route8UnifiedTrueTwoCarrierEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedTrueTwoCarrierEntry)
        ⟨Graph.Contracts.RouteEight.route8UnpaidTrueEntry data.toParameters
          inputs.current.object (inputs.get (K .route8UnpaidWitnessFree)).down
          (inputs.get (K .route8UnpaidTwoCarrier)).down
          (inputs.get (K .route8UnifiedEntryCensus)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[181]`**: decided by case analysis on outcome (i). -/
noncomputable def route8UnpaidExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known)
    (residualFresh : K .route8UnpaidExitFourResidual ∉ known) :
    Decision (K .route8UnpaidWitnessFree) (K .route8UnpaidExitFourResidual)
      previous :=
  Decision.run previous (K .route8UnpaidWitnessFree)
    (K .route8UnpaidExitFourResidual)
    `Hypostructure.Graph.Strategy.Spine.route8UnpaidExitFourDichotomy
    (Classical.choice (show Nonempty
        ((K .route8UnpaidWitnessFree).At current ⊕
          (K .route8UnpaidExitFourResidual).At current) from by
      by_cases witnessFree :
          Route8UnpaidWitnessFreeStatement data.toParameters current.object
      · exact ⟨.inl ⟨witnessFree⟩⟩
      · exact ⟨.inr ⟨Graph.Contracts.RouteEight.route8UnpaidExitFourResidual_of_not_witnessFree
          data.toParameters current.object witnessFree⟩⟩))
    witnessFreeFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
