import Hypostructure.Graph.ColdFirstFailure

/-!
# Fixture: `def:cold-window-ledger`'s two thresholds, computed

`def:cold-window-ledger` sets `τ(θ) := 15θ/(1−13θ)` for a packing density
`θ = p₁₃/n` and records

  `τ(θ) < 1/4  ⟺  θ < 1/73`,
  `τ(θ) < 3/13 ⟺  θ < 1/78`,

with `1/78` the route-8 private-carrier threshold and `1/73` the
negative-net-charge threshold.

`Graph.ColdCorridor.tauBelow_quarter` and `tauBelow_routeEight` clear those
comparisons of denominators, in `Nat`, at an arbitrary external-stub count `s`:
they become `(5s − 2)·p < n` and `(16s − 6)·p < 3n`.  This fixture evaluates the
coefficients at the manuscript's own `s = 15` — the external-stub count
`δ·order − 2(order−1) = 3·13 − 24` of `lem:cold-window-stub-excess` — and checks
that they are `73` and `78`.

So neither numeral appears in `Hypostructure.Graph`: both are consequences of
the registered baseline and window order, checked here.
-/

namespace Hypostructure.Fixtures.ColdCorridorLedger

open Hypostructure.Graph.ColdCorridor

/-- The manuscript's external-stub count of an ambient-cubic `P₁₃`:
`δ·order − 2(order − 1) = 3·13 − 2·12 = 15`.  Read off the registered baseline
and order, exactly as node `[28]` reads it. -/
def stubs : Nat := 3 * 13 - 2 * (13 - 1)

example : stubs = 15 := by decide

/-- The branch excess `b(P) = s(P) − 2 = 13`. -/
example : branchExcessOf stubs = 13 := by decide

/-- **`τ(θ) < 1/4 ⟺ θ < 1/73`.**  The cleared coefficient `5s − 2` is `73`. -/
example : 5 * stubs - 2 = 73 := by decide

/-- **`τ(θ) < 3/13 ⟺ θ < 1/78`.**  The cleared comparison is
`234·p < 3n`, which is `78·p < n`. -/
example : 16 * stubs - 6 = 234 := by decide

example (packing order : Nat) : 234 * packing < 3 * order ↔ 78 * packing < order := by
  omega

/-- The `1/4` comparison at the manuscript's stub count, end to end: `τ(θ) < 1/4`
is exactly `73·p < n`. -/
example (packing order : Nat) (saturated : branchExcessOf stubs * packing ≤ order) :
    TauBelow stubs 1 4 packing order ↔ 73 * packing < order := by
  rw [tauBelow_quarter stubs packing order (by decide) saturated]
  norm_num [stubs]

/-- The `3/13` comparison at the same stub count: `τ(θ) < 3/13` is exactly
`78·p < n`. -/
example (packing order : Nat) (saturated : branchExcessOf stubs * packing ≤ order) :
    TauBelow stubs 3 13 packing order ↔ 78 * packing < order := by
  rw [tauBelow_routeEight stubs packing order (by decide) saturated]
  constructor
  · intro below; norm_num [stubs] at below; omega
  · intro below; norm_num [stubs]; omega

end Hypostructure.Fixtures.ColdCorridorLedger
