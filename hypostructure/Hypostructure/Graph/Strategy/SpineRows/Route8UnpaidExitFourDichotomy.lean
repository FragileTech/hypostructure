import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.DemandLedger

/-!
# Node `[181]`: some unpaid entry of `P₀` lacks an exit-(4) witness?

`thm:typeA-unpaid-exit4-reduction` at the maximal demand ledger `P₀` fixed by
node `[349]` (`canonicalRoute8Partition`).  The one-entry augmentation (168.1)
at `P₀` is published first (`route8UnpaidTwoCarrierRow`).  The decision reads
`[349]` and splits at `P₀`: the yes key `route8UnpaidWitnessFree` is outcome
(i), the no key `route8UnpaidExitFourResidual` its exact negation at the same
`P₀`, outcome (ii) = node `[183]`.  On the yes arm the witness-free entry `ξ*`
of `P₀` is the terminal entry of `thm:typeA-two-carrier-nogo`
(`route8UnpaidTrueEntryRow`), closed at node `[124]`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **(168.1)** at `P₀`: every unpaid entry of the committed maximal demand
ledger is two-support. -/
@[reducible] noncomputable def route8UnpaidTwoCarrierRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnpaidTwoCarrier
    { Requires := [K .route8DemandLedger, K .cubicBaseline]
      Produces := [K .route8UnpaidTwoCarrier]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnpaidTwoCarrier)
        ⟨Graph.Contracts.RouteEight.route8UnpaidTwoCarrier data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          (inputs.get (K .route8DemandLedger)).down⟩ .nil)
    0 0

/-- **Node `[181]`, yes arm → node `[124]`**: on the rate-failed arm the
terminal entry is the witness-free unpaid entry `ξ*` of `P₀`, a true
two-support route-`8` entry. -/
@[reducible] noncomputable def route8UnpaidTrueEntryRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnpaidTrueEntry
    { Requires := [K .route8UnpaidWitnessFree, K .route8UnpaidTwoCarrier,
        K .route8UnifiedEntryCensus, K .route8StageRateFailed]
      Produces := [K .route8UnifiedTrueTwoCarrierEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedTrueTwoCarrierEntry)
        ⟨Graph.Contracts.RouteEight.route8UnpaidTrueEntry data.toParameters
          inputs.current.object (inputs.get (K .route8UnpaidWitnessFree)).down
          (inputs.get (K .route8UnpaidTwoCarrier)).down
          (inputs.get (K .route8UnifiedEntryCensus)).down
          (inputs.get (K .route8StageRateFailed)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[181]`**: reads the committed ledger `[349]` and splits at its
partition `P₀` on outcome (i); the two arms are exact complements at `P₀`. -/
noncomputable def route8UnpaidExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .route8DemandLedger) known]
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
      obtain ⟨P, pin⟩ :=
        Graph.Contracts.RouteEight.canonicalRoute8Partition_exists
          data.toParameters current.object
          (previous.get (K .route8DemandLedger)).down
      by_cases witnessFree :
          ∃ index, Route8UnpaidWitnessFreeSpec data.toParameters current.object
            P index
      · exact ⟨.inl ⟨⟨P, pin, witnessFree⟩⟩⟩
      · exact ⟨.inr ⟨⟨P, pin,
          Graph.Contracts.RouteEight.unpaidExitFour_of_not_witnessFree
            data.toParameters current.object P witnessFree⟩⟩⟩))
    witnessFreeFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
