import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSignature
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSingletonTail
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded

namespace Hypostructure.Fixtures.WindowShadowRows

open Core.Residual Core.Strategy Graph.Strategy.Spine

universe u v

noncomputable section

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data.{u}}

/-- All four publications preserve an arbitrary incoming prefix, including
its selected-object fact. The final exclusion consumes the cycle certificate
published on this very branch. -/
example {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger _ current known)
    [FactKeys.Has (K .selection) known]
    (signatureFresh : K .windowShadowSignature ∉ known)
    (tailFresh : K .windowShadowSingletonTail ∉ known)
    (cycleFresh : K .windowShadowHitCycle ∉ known)
    (excludedFresh : K .windowShadowHitExcluded ∉ known) :
    ExactLedger _ current
      ([K .windowShadowHitExcluded, K .windowShadowHitCycle,
        K .windowShadowSingletonTail, K .windowShadowSignature] ++ known) := by
  let signature := windowShadowSignatureRow.run history
    (by simp [signatureFresh])
  let tail := windowShadowSingletonTailRow.run signature
    (by simp [K_eq_iff, tailFresh])
  let cycle := windowShadowHitCycleRow.run tail
    (by simp [K_eq_iff, cycleFresh])
  exact windowShadowHitExcludedRow.run cycle
    (by simp [K_eq_iff, excludedFresh])

#print axioms windowShadowSignatureRow
#print axioms windowShadowSingletonTailRow
#print axioms windowShadowHitCycleRow
#print axioms windowShadowHitExcludedRow

end

end Hypostructure.Fixtures.WindowShadowRows
