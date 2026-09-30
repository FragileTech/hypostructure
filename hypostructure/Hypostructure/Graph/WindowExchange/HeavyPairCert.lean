import Hypostructure.Graph.WindowExchange.HeavyPairCert46A
import Hypostructure.Graph.WindowExchange.HeavyPairCert46B
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_0A
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_0B
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_1A
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_1B
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_2A
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_2B
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_3
import Hypostructure.Graph.WindowExchange.HeavyPairCert69_4

/-!
# The rung certificates

* `cert46`: exits `4` on `P` at `a`, `6` on `Q` at `b`, `a, b ≤ 6`: no increasing list of 7
  rungs survives the search (lengths `[3, 14]` of the copy between its exits).
* `cert69`: exits `6` on `P` at `a`, `9` on `Q` at `b`, `a ≤ b ≤ 6`: no increasing list of 9
  rungs survives (lengths `[5, 14]`).

Assembled from the shards `HeavyPairCert46*`, `HeavyPairCert69_*`.
-/

namespace Hypostructure.Graph.WindowExchange

theorem cert46 (a : ℕ) (ha : a ≤ 6) (b : ℕ) (hb : b ≤ 6) : certCfg 3 4 a 6 b 7 7 = true := by
  rcases Nat.lt_or_ge a 3 with h | h
  · exact cert46A a h b (by omega)
  · exact cert46B a (by omega) h b (by omega)

theorem cert69 (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 6) : certCfg 5 6 a 9 b 8 9 = true := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ 4 ≤ a by omega) with rfl | rfl | rfl | rfl | h
  · rcases Nat.lt_or_ge b 4 with h | h
    · exact cert69_0A b (by omega) (by omega) (by omega)
    · exact cert69_0B b (by omega) h hb
  · rcases Nat.lt_or_ge b 4 with h | h
    · exact cert69_1A b (by omega) hab (by omega)
    · exact cert69_1B b (by omega) h hb
  · rcases Nat.lt_or_ge b 4 with h | h
    · exact cert69_2A b (by omega) hab (by omega)
    · exact cert69_2B b (by omega) h hb
  · exact cert69_3 b (by omega) hab hb
  · exact cert69_4 a (by omega) h b (by omega) hab

end Hypostructure.Graph.WindowExchange
