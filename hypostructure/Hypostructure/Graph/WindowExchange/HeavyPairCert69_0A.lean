import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert69_0A`

Exits `6` on `P` and `9` on `Q`, landings `a = 0`, `0 ≤ b ≤ 3`: no increasing list of 9 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `6` on `P` and `9` on `Q`, landings `a = 0`, `0 ≤ b ≤ 3`: no increasing list of 9 rungs survives. -/
theorem cert69_0A : ∀ b < 7, 0 ≤ b → b ≤ 3 → certCfg 5 6 0 9 b 8 9 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
