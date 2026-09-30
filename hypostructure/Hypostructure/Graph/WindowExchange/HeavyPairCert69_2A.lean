import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Rung certificate, shard `Cert69_2A`

Exits `6` on `P` and `9` on `Q`, landings `a = 2`, `2 ≤ b ≤ 3`: no increasing list of 9 rungs survives.  Checked by `native_decide`; assembled in `HeavyPairCert`.
-/

namespace Hypostructure.Graph.WindowExchange

/-- Exits `6` on `P` and `9` on `Q`, landings `a = 2`, `2 ≤ b ≤ 3`: no increasing list of 9 rungs survives. -/
theorem cert69_2A : ∀ b < 7, 2 ≤ b → b ≤ 3 → certCfg 5 6 2 9 b 8 9 = true := by
  native_decide

end Hypostructure.Graph.WindowExchange
