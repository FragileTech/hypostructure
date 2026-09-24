import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[181]`: the explicit peeled target-defect demand residual

This row proves no closure.  It publishes the exact residual assembled by node
`[123]`: the failed peeling stage with its stage-local accounting, the maximal
demand partition, its maximal absorption, and the exact packed-window blocker
partition.  `AtomicCT.run` appends that one key to the literal incoming
`ExactLedger`; every fact in the node-`[123]` prefix therefore remains in the
type index and is available to the eventual node-`[181]` continuation. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PeeledDemandResidualRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8PeeledDemandResidual
    { Requires := [K .route8StageRateFailed, K .route8DemandLedger,
        K .route8DemandAbsorption, K .route8WindowBlockers]
      Produces := [K .route8PeeledDemandResidual]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let failed := inputs.get (K .route8StageRateFailed)
      let ledger := inputs.get (K .route8DemandLedger)
      let absorption := inputs.get (K .route8DemandAbsorption)
      let blockers := inputs.get (K .route8WindowBlockers)
      .cons (key := K .route8PeeledDemandResidual)
        ⟨failed.down, ledger.down, absorption.down, blockers.down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
