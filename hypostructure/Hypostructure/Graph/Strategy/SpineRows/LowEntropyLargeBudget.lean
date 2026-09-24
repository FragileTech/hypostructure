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

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- **Node `[55]`, Residual C on the low-entropy arm.**

The low arm of `prop:two-budget` is itself the second alternative in the
paper's Residual C statement.  Read that exact fact from the current ledger and
append only the canonical Residual C key.  Node `[56]`'s net-deficiency bound
is a separate subsequent fact and is not published here. -/
@[reducible] noncomputable def lowEntropyLargeBudgetRow :
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
    `Hypostructure.Graph.Strategy.Spine.lowEntropyLargeBudget
    { Requires := [K .remainderEntropyLow]
      Produces := [K .largeBudgetResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .largeBudgetResidual)
        (show Value BranchState Presentation presentation data
            .largeBudgetResidual inputs.current from
          ⟨Or.inr (inputs.get (K .remainderEntropyLow)).down⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
