import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded

namespace Hypostructure.Fixtures.WindowShadowRows

open Core.Residual Core.Strategy Graph.Strategy.Spine

universe u v

noncomputable section

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data.{u}}

/-- Both publications preserve an arbitrary incoming prefix, including its
selected-object fact and the node-`[352]` window blockers they are pinned to.
The final exclusion consumes the cycle certificate published on this very
branch. -/
example {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger _ current known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .route8WindowBlockers) known]
    (cycleFresh : K .windowShadowHitCycle ∉ known)
    (excludedFresh : K .windowShadowHitExcluded ∉ known) :
    ExactLedger _ current
      ([K .windowShadowHitExcluded, K .windowShadowHitCycle] ++ known) := by
  let cycle := windowShadowHitCycleRow.run history
    (by simp [cycleFresh])
  exact windowShadowHitExcludedRow.run cycle
    (by simp [K_eq_iff, excludedFresh])

#print axioms windowShadowHitCycleRow
#print axioms windowShadowHitExcludedRow

end

end Hypostructure.Fixtures.WindowShadowRows
