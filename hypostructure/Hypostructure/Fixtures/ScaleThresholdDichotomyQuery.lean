import Hypostructure.Core.Strategy.ScaleThresholdDichotomy

namespace Hypostructure.Fixtures.ScaleThresholdDichotomyQuery

open Hypostructure
open Hypostructure.Core.Strategy

def comparison (value threshold : Nat) :
    Core.Residual.Query Unit fun _ =>
      Core.OrderThresholdSplit.Profile Nat :=
  fun _ => ⟨value, threshold⟩

noncomputable def highProfile :
    ScaleThresholdDichotomy.Profile Unit :=
  ScaleThresholdDichotomy.Profile.ofComparisonQuery (comparison 2 1)

noncomputable def lowProfile :
    ScaleThresholdDichotomy.Profile Unit :=
  ScaleThresholdDichotomy.Profile.ofComparisonQuery (comparison 1 1)

noncomputable def highResult := highProfile.execution.run ()
noncomputable def lowResult := lowProfile.execution.run ()

example : (highProfile.thresholdInput ()).threshold = 1 := by rfl
example : (highProfile.thresholdInput ()).load = 2 := by rfl
example : (lowProfile.thresholdInput ()).threshold = 1 := by rfl
example : (lowProfile.thresholdInput ()).load = 1 := by rfl

example :
    match highProfile.route () with
    | .above _ => True
    | .atOrBelow _ => False := by
  trivial

example :
    match lowProfile.route () with
    | .above _ => False
    | .atOrBelow _ => True := by
  trivial

example : highProfile.execution.checks () = highResult.checks := by rfl
example : highProfile.execution.work () = highResult.checks := by rfl
example : lowProfile.execution.checks () = lowResult.checks := by rfl
example : lowProfile.execution.work () = lowResult.checks := by rfl

end Hypostructure.Fixtures.ScaleThresholdDichotomyQuery
