import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert69_4`

Exits `6` on `P` and `9` on `Q`, landings `4 ≤ a ≤ b ≤ 6`: no increasing list of 9 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `6` on `P` and `9` on `Q`, landings `4 ≤ a ≤ b ≤ 6`: no increasing list of 9 rungs survives. -/
theorem cert69_4 : ∀ a < 7, 4 ≤ a → ∀ b < 7, a ≤ b → certCfg 5 6 a 9 b 8 9 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
