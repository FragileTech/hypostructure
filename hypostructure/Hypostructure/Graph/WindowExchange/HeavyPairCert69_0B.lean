import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert69_0B`

Exits `6` on `P` and `9` on `Q`, landings `a = 0`, `4 ≤ b ≤ 6`: no increasing list of 9 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `6` on `P` and `9` on `Q`, landings `a = 0`, `4 ≤ b ≤ 6`: no increasing list of 9 rungs survives. -/
theorem cert69_0B : ∀ b < 7, 4 ≤ b → b ≤ 6 → certCfg 5 6 0 9 b 8 9 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
