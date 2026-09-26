import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.JointBalance

/-!
# Node `[186]`: joint accounting on the visible-overload residual

This row does not restart the demand construction.  It reads the exact peel
chain and stage accounting of node `[123]`, the failed reduced-rate test, the
unified deficit, the committed maximal demand ledger and its empty-dependence
maximal absorption, the demand-unit count, and the node-`[184]`/`[185]`
visibility facts simultaneously (`lem:typeA-unified-joint-balance`).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[186]`**: the simultaneous exact balances. -/
@[reducible] noncomputable def route8JointBalanceRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8JointBalance
    { Requires := [K .route8UnifiedVisibleOverload,
        K .route8UnifiedVisibleResidual, K .route8PeelingDescent,
        K .route8StageRateFailed, K .route8DemandLedger,
        K .route8DemandAbsorption, K .route8UnifiedDeficit,
        K .route8DemandUnitCount]
      Produces := [K .route8JointBalance]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8JointBalance)
        ⟨Graph.Contracts.RouteEight.route8JointBalance data.toParameters
          inputs.current.object
          (inputs.get (K .route8UnifiedVisibleOverload)).down
          (inputs.get (K .route8UnifiedVisibleResidual)).down
          (inputs.get (K .route8PeelingDescent)).down
          (inputs.get (K .route8StageRateFailed)).down
          (inputs.get (K .route8DemandAbsorption)).down
          (inputs.get (K .route8UnifiedDeficit)).down
          (inputs.get (K .route8DemandUnitCount)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
