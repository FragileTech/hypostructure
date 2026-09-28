import Hypostructure.Core.CeilSqrt

/-!
# The density order: a linear lower bound on a packing against a log-scaled cap

A packing of `p` windows in an object of order `n` whose remainder rate reads
the linear lower bound

  `δ·n ≤ A·p + D·T`,

and whose entropy count reads the log-scaled density cap

  `2·(r·L·p) ≤ (L+1)·(δ·n + T) + S·L·T`,   `L = ⌊log₂ n⌋`,

satisfies the single combined bound

  `2·r·L·(δ·n) ≤ A·((L+1)·(δ·n + T)) + L·T·(A·S + 2·r·D)`.

When the rate margin `A < 2r` holds (the density the lower bound forces,
`δ/A`, exceeds the density the cap allows, `δ/(2r)`) and `T = C·⌈√n⌉` is
sublinear, the combined bound fails for every `n` past the explicit cutoff

  `N₀ = max(2^(⌊2A/(2r−A)⌋ + 1), (2·(2A + A·S + 2·r·D)·C + 1)²)`.

This is the exact finite form of "`θ ≥ θ₀` against `θ ≤ θ_win + o(1)` with
`θ_win < θ₀`": below `N₀` nothing is claimed.  Every constant is a parameter;
nothing here knows a graph, a presentation, or a manuscript.
-/

namespace Hypostructure.Graph

/-- The combined coefficient `2A + A·S + 2·r·D` of the order bound. -/
def densityOrderCoefficient (A D r S : Nat) : Nat :=
  2 * A + (A * S + 2 * r * D)

/-- The scale `a = 2·(2A + A·S + 2rD)·C` against which `n ≤ a·⌈√n⌉` is read. -/
def densityOrderScale (A D r S C : Nat) : Nat :=
  2 * densityOrderCoefficient A D r S * C

/-- The binary-logarithm floor `⌊2A/(2r−A)⌋ + 1` of the cutoff. -/
def densityOrderLogFloor (A r : Nat) : Nat :=
  2 * A / (2 * r - A) + 1

/-- **The explicit cutoff `N₀`.** -/
def densityOrderCutoff (A D r S C : Nat) : Nat :=
  max (2 ^ densityOrderLogFloor A r) ((densityOrderScale A D r S C + 1) ^ 2)

/-- **The exact size condition.**  The rate margin `A < 2r`, a positive
baseline, and `N₀ ≤ n`.  The margin and the baseline are statements about the
registered constants alone; at a presentation where they hold, this is exactly
`N₀ ≤ n`. -/
def SufficientlyLargeForDensityOrder (A D r S C δ size : Nat) : Prop :=
  A < 2 * r ∧ 0 < δ ∧ densityOrderCutoff A D r S C ≤ size

instance (A D r S C δ size : Nat) :
    Decidable (SufficientlyLargeForDensityOrder A D r S C δ size) := by
  unfold SufficientlyLargeForDensityOrder
  infer_instance

/-- The single combined bound, read at an order `n`, a packing number `p`, a
scale count `L` and a threshold `T`. -/
def DensityOrderBound (A D r S δ size L T : Nat) : Prop :=
  2 * r * L * (δ * size) ≤
    A * ((L + 1) * (δ * size + T)) + L * T * (A * S + 2 * r * D)

/-- **The combined bound from the lower bound and the cap.**  `2rL·δn ≤
2rL·(Ap + DT) = A·(2rLp) + LT·2rD`, and `2rLp` is the cap. -/
theorem densityOrderBound_of_lower_cap
    {A D r S δ size packing L T : Nat}
    (lower : δ * size ≤ A * packing + D * T)
    (cap : 2 * (r * L * packing) ≤ (L + 1) * (δ * size + T) + S * L * T) :
    DensityOrderBound A D r S δ size L T := by
  unfold DensityOrderBound
  have step1 : 2 * r * L * (δ * size) ≤ 2 * r * L * (A * packing + D * T) :=
    Nat.mul_le_mul_left _ lower
  have step2 : 2 * r * L * (A * packing + D * T) =
      A * (2 * (r * L * packing)) + L * T * (2 * r * D) := by ring
  have step3 : A * (2 * (r * L * packing)) ≤
      A * ((L + 1) * (δ * size + T) + S * L * T) :=
    Nat.mul_le_mul_left _ cap
  have step4 : A * ((L + 1) * (δ * size + T) + S * L * T) + L * T * (2 * r * D) =
      A * ((L + 1) * (δ * size + T)) + L * T * (A * S + 2 * r * D) := by ring
  omega

/-- The cutoff's logarithmic half: `⌊2A/(2r−A)⌋ + 1 ≤ log₂ n` forces
`2A < (2r − A)·log₂ n`. -/
theorem two_mul_lt_margin_mul_log2
    {A r size : Nat} (margin : A < 2 * r)
    (large : 2 ^ densityOrderLogFloor A r ≤ size) :
    2 * A < (2 * r - A) * Nat.log2 size ∧ 1 ≤ Nat.log2 size := by
  have gpos : 0 < 2 * r - A := by omega
  have sizeNe : size ≠ 0 := by
    have := Nat.pow_pos (n := densityOrderLogFloor A r) (by norm_num : 0 < 2)
    omega
  have logLe : densityOrderLogFloor A r ≤ Nat.log2 size := by
    rw [Nat.log2_eq_log_two, Nat.le_log_iff_pow_le (by norm_num) sizeNe]
    exact large
  unfold densityOrderLogFloor at logLe
  refine ⟨?_, le_trans (Nat.le_add_left 1 _) logLe⟩
  have floorLt : 2 * A < (2 * r - A) * (2 * A / (2 * r - A) + 1) := by
    have := Nat.lt_div_mul_add (a := 2 * A) gpos
    calc 2 * A < 2 * A / (2 * r - A) * (2 * r - A) + (2 * r - A) := this
      _ = (2 * r - A) * (2 * A / (2 * r - A) + 1) := by ring
  exact lt_of_lt_of_le floorLt (Nat.mul_le_mul_left _ logLe)

/-- The cutoff's square-root half: `(a+1)² ≤ n` forces `a·⌈√n⌉ < n`. -/
theorem mul_ceilSqrt_lt_of_sq_le {a size : Nat}
    (large : (a + 1) ^ 2 ≤ size) :
    a * Core.ceilSqrt size < size := by
  have root : a + 1 ≤ Nat.sqrt size := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using large
  have ceil := Core.ceilSqrt_le_sqrt_succ size
  have sq : Nat.sqrt size * Nat.sqrt size ≤ size := Nat.sqrt_le size
  calc a * Core.ceilSqrt size ≤ a * (Nat.sqrt size + 1) := Nat.mul_le_mul_left _ ceil
    _ = a * Nat.sqrt size + a := by ring
    _ < a * Nat.sqrt size + Nat.sqrt size := by omega
    _ = (a + 1) * Nat.sqrt size := by ring
    _ ≤ Nat.sqrt size * Nat.sqrt size := Nat.mul_le_mul_right _ root
    _ ≤ size := sq

/-- **The combined bound fails past the cutoff.**  For every order `n` with
`N₀ ≤ n` (and the constant conditions of `SufficientlyLargeForDensityOrder`),
the combined bound at `L = ⌊log₂ n⌋` and `T = C·⌈√n⌉` is false. -/
theorem densityOrderBound_false_of_large
    {A D r S C δ size : Nat}
    (bound : DensityOrderBound A D r S δ size (Nat.log2 size)
      (C * Core.ceilSqrt size))
    (large : SufficientlyLargeForDensityOrder A D r S C δ size) : False := by
  obtain ⟨margin, δpos, cutoff⟩ := large
  unfold densityOrderCutoff at cutoff
  have logPart := two_mul_lt_margin_mul_log2 margin (le_trans (le_max_left _ _) cutoff)
  have rootPart := mul_ceilSqrt_lt_of_sq_le (le_trans (le_max_right _ _) cutoff)
  unfold DensityOrderBound at bound
  set L := Nat.log2 size with hL
  set T := C * Core.ceilSqrt size with hT
  set Q := A * S + 2 * r * D with hQ
  set g := 2 * r - A with hg
  obtain ⟨gL, Lpos⟩ := logPart
  have twoR : 2 * r = A + g := by omega
  -- `(g·L − A)·δn ≤ A(L+1)T + L·T·Q`, cleared of subtraction.
  have core : (A + g) * L * (δ * size) ≤
      A * ((L + 1) * (δ * size + T)) + L * T * Q := by
    rw [← twoR]; exact bound
  have expand : (A + g) * L * (δ * size) = A * L * (δ * size) + g * L * (δ * size) := by
    ring
  have expand2 : A * ((L + 1) * (δ * size + T)) =
      A * L * (δ * size) + A * (δ * size) + A * (L + 1) * T := by ring
  have core2 : g * L * (δ * size) ≤ A * (δ * size) + A * (L + 1) * T + L * T * Q := by
    omega
  -- `2A < gL` doubles the left side against the `A·δn` term.
  have dbl : 2 * (A * (δ * size)) ≤ g * L * (δ * size) := by
    have : 2 * A ≤ g * L := le_of_lt gL
    calc 2 * (A * (δ * size)) = (2 * A) * (δ * size) := by ring
      _ ≤ (g * L) * (δ * size) := Nat.mul_le_mul_right _ this
  have core3 : g * L * (δ * size) ≤ 2 * (A * (L + 1) * T + L * T * Q) := by omega
  -- `L + 1 ≤ 2L`, then divide by `L`.
  have Lbound : A * (L + 1) * T ≤ L * (2 * A * T) := by
    have : A * (L + 1) * T ≤ A * (2 * L) * T :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    calc A * (L + 1) * T ≤ A * (2 * L) * T := this
      _ = L * (2 * A * T) := by ring
  have core4 : L * (g * (δ * size)) ≤ L * (2 * (2 * A * T + T * Q)) := by
    calc L * (g * (δ * size)) = g * L * (δ * size) := by ring
      _ ≤ 2 * (A * (L + 1) * T + L * T * Q) := core3
      _ ≤ 2 * (L * (2 * A * T) + L * T * Q) := by omega
      _ = L * (2 * (2 * A * T + T * Q)) := by ring
  have core5 : g * (δ * size) ≤ 2 * (2 * A * T + T * Q) :=
    Nat.le_of_mul_le_mul_left core4 Lpos
  have gpos : 1 ≤ g := by omega
  have sizeLe : size ≤ g * (δ * size) := by
    have : 1 * (1 * size) ≤ g * (δ * size) :=
      Nat.mul_le_mul gpos (Nat.mul_le_mul_right _ δpos)
    simpa using this
  have final : size ≤ densityOrderScale A D r S C * Core.ceilSqrt size := by
    have : 2 * (2 * A * T + T * Q) = densityOrderScale A D r S C * Core.ceilSqrt size := by
      simp only [densityOrderScale, densityOrderCoefficient, hT, hQ]; ring
    omega
  omega

end Hypostructure.Graph
