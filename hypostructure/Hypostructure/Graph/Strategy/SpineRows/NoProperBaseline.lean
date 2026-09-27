import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineSelection

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

/-! ## Node `[8]`: no proper subgraph satisfies the baseline

`lem:no-proper-core`.  A proper subgraph is strictly smaller in the registered
order, so minimality forces it to have an accepted cycle; but every cycle of a
proper subgraph is a cycle of the ambient graph
(`Graph.cycleProperSubgraphTargetMonotone`), which the selected object does not
have.  So no proper subgraph satisfies the baseline. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def noProperBaselineRow :
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
    `Hypostructure.Graph.Strategy.Spine.noProperBaseline
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .noProperBaseline]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .noProperBaseline)
        ⟨Contracts.Spine.noProperBaseline_of_selection data.toParameters
          inputs.current.object inputs.current.baseline
          (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
