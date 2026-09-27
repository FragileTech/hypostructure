import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.NetCharge

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

/-! ## Node `[56]`: the large-budget net-deficiency cap (density-cap arm)

This is the manuscript's displayed bound `def⁺(R) − σ(R) ≤ (1/4 − ε)|R|`
"for all sufficiently large `n`", in the exact cleared finite form: reading the
density cap and the registered sufficiently-large predicate gives the strict
scaled inequality the net-charge step consumes.  The implication is stored on
the literal Residual C ledger of the `[24]` bounded arm. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def netDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .densityCap, K .cubicBaseline,
        K .spinePresentationLaws]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- `[55]` → `[56]`: the Residual C ledger fact is this node's predecessor.
      let _residualC := (inputs.get (K .largeBudgetResidual)).down
      let laws := (inputs.get (K .spinePresentationLaws)).down
      .cons (key := K .netDeficiencyCap)
        ⟨Contracts.Spine.netDeficiencyCap_of_densityCap data.toParameters
          inputs.current.object laws.2.2.2.1
          (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)
          laws.2.2.2.2.1
          (inputs.get (K .densityCap)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
