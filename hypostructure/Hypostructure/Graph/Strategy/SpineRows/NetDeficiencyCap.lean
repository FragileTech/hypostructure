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
    { Requires := [K .densityCap]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .netDeficiencyCap)
        ⟨Contracts.Spine.netDeficiencyCap_of_densityCap data.toParameters
          inputs.current.object data.separatedScaleCount_eq_log2
          data.three_le_threshold data.netCapRateSlack
          (inputs.get (K .densityCap)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
