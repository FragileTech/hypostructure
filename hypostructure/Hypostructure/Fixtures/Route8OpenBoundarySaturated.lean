import Hypostructure.Graph.Strategy.SpineRows.Route8OpenBoundarySaturated
import Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance

namespace Hypostructure.Fixtures.Route8OpenBoundarySaturated

open Core.Residual Core.Strategy Graph.Strategy.Spine

universe u v

noncomputable section

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data.{u}}

example {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger _ current known)
    [FactKeys.Has (K .route8DemandAbsorption) known]
    (saturationFresh : K .route8OpenBoundarySaturated ∉ known)
    (countFresh : K .route8DemandUnitCount ∉ known) :
    ExactLedger _ current
      ([K .route8OpenBoundarySaturated, K .route8DemandUnitCount] ++ known) :=
  route8OpenBoundarySaturatedRow.run history
    (by simp [K_eq_iff, saturationFresh, countFresh])

#print axioms route8OpenBoundarySaturatedRow
#print axioms route8JointBalanceRow

end

end Hypostructure.Fixtures.Route8OpenBoundarySaturated
