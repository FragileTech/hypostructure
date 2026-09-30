import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert46B`

Exits `4` on `P` and `6` on `Q`, landings `3 ≤ a ≤ 6`, `b ≤ 6`: no increasing list of 7 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `4` on `P` and `6` on `Q`, landings `3 ≤ a ≤ 6`, `b ≤ 6`: no increasing list of 7 rungs survives. -/
theorem cert46B : ∀ a < 7, 3 ≤ a → ∀ b < 7, certCfg 3 4 a 6 b 7 7 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
