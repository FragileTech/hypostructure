import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert46A`

Exits `4` on `P` and `6` on `Q`, landings `a ≤ 2`, `b ≤ 6`: no increasing list of 7 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `4` on `P` and `6` on `Q`, landings `a ≤ 2`, `b ≤ 6`: no increasing list of 7 rungs survives. -/
theorem cert46A : ∀ a < 3, ∀ b < 7, certCfg 3 4 a 6 b 7 7 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
