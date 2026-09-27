import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.Estimate

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[138]` on the free-pair side of `[137]`: the realized `[131]` count,
`lem:sparse-slack-surplus` and the strict surplus of node `[19]` give
`σ(G) ≤ C_sp ⌈√n⌉` (`cor:spine-lower-bound-surplus-estimates`), on either arm
of the coupled test. -/
@[reducible] noncomputable def freePairSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairSurplusEstimate
    { Requires := [K .freePairEntropySandwich, K .sparseSlackSurplus, K .surplusAbove,
        K .cubicBaseline]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        ⟨Graph.Contracts.SurplusPair.spineSurplusEstimate_of_pairSandwich
          inputs.current.baseline
          (inputs.get (K .freePairEntropySandwich)).down
          (inputs.get (K .sparseSlackSurplus)).down
          (inputs.get (K .surplusAbove)).down
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.2⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
