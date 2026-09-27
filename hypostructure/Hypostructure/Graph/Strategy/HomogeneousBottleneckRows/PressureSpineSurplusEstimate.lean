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

/-- Node `[138]` on `[137]`'s no arm: no capacity ledger of the object has
positive coupled excess, so the object's own certified ledger is capped and
`σ(G) ≤ R_L(n) ≤ C_sp ⌈√n⌉`. -/
@[reducible] noncomputable def pressureSpineSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pressureSpineSurplusEstimate
    { Requires := [K .sparsePressureNearCubic, K .fibrePressure, K .surplusAbove,
        K .surplusPresentation]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        ⟨Graph.Contracts.SurplusPair.spineSurplusEstimate_of_notOverloaded
          (inputs.get (K .sparsePressureNearCubic)).down
          (inputs.get (K .fibrePressure)).down
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .surplusPresentation)).down.2.2.2.2⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
