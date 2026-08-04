import Mathlib

/-!
# Radial power kernels

Every classical fundamental solution of a constant-coefficient elliptic
operator is a radial power: `‖x‖^{2-n}` for the Laplacian in dimension
`n ≥ 3`, `log‖x‖` in dimension two, `|x|/2` on a line.  Before any of them can
be registered as a `FundamentalSolution` the same fact has to be established:
the kernel is **locally integrable**, so that convolution against it is
defined at all.

That fact is dimension-generic and has nothing to do with any particular
equation, so it belongs here and is proved once.  The statement is the sharp
one: `‖x‖^{-a}` is locally integrable exactly when `a` is below the dimension.

Both halves come from mathlib:

* `MeasureTheory.integrableOn_fun_norm_addHaar` turns an integral of a radial
  function over a ball into a one-dimensional integral carrying the `r^{n-1}`
  Jacobian — integration in polar coordinates, in any dimension;
* `integrableOn_Ioo_rpow_iff` decides the resulting one-dimensional integral.

So nothing analytic is assumed and nothing is proved twice.
-/

namespace Hypostructure.PDE.Solution

open MeasureTheory Metric Set

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]
  [Nontrivial Point] (μ : Measure Point) [μ.IsAddHaarMeasure]

/-- The radial power kernel `x ↦ ‖x‖^{-exponent}`. -/
noncomputable def radialKernel (exponent : ℝ) : Point → ℝ :=
  fun place => ‖place‖ ^ (-exponent)

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The dimension is at least one, so the polar Jacobian exponent `n - 1`
computed with truncated subtraction agrees with the real one. -/
theorem one_le_finrank : 1 ≤ Module.finrank ℝ Point :=
  Module.finrank_pos

omit [MeasurableSpace Point] [BorelSpace Point] in
theorem cast_finrank_sub_one :
    ((Module.finrank ℝ Point - 1 : ℕ) : ℝ) = (Module.finrank ℝ Point : ℝ) - 1 := by
  have := one_le_finrank (Point := Point)
  push_cast [Nat.cast_sub this]
  ring

/--
The sharp local-integrability criterion for a radial power kernel on a ball:
`‖x‖^{-exponent}` is integrable near the origin exactly when `exponent` is
below the dimension.

This is integration in polar coordinates and nothing more; the `r^{n-1}`
Jacobian is what buys the `exponent < n` room.
-/
theorem integrableOn_radialKernel_ball {exponent : ℝ}
    (subcritical : exponent < Module.finrank ℝ Point) (radius : ℝ) :
    IntegrableOn (radialKernel (Point := Point) exponent) (ball 0 radius) μ := by
  rcases le_or_gt radius 0 with degenerate | positive
  · rw [ball_eq_empty.mpr degenerate]
    exact integrableOn_empty
  show IntegrableOn (fun place : Point => ‖place‖ ^ (-exponent)) _ _
  rw [integrableOn_fun_norm_addHaar μ (f := fun y => y ^ (-exponent))]
  rw [integrableOn_congr_fun (g := fun y : ℝ =>
      y ^ (((Module.finrank ℝ Point : ℝ) - 1) + -exponent)) _ measurableSet_Ioo]
  · rw [intervalIntegral.integrableOn_Ioo_rpow_iff positive]
    linarith
  · intro place member
    have place_pos : 0 < place := member.1
    show place ^ (Module.finrank ℝ Point - 1) • place ^ (-exponent) =
      place ^ (((Module.finrank ℝ Point : ℝ) - 1) + -exponent)
    rw [smul_eq_mul, Real.rpow_add place_pos, ← Real.rpow_natCast place,
      cast_finrank_sub_one]

/--
A radial power kernel below the critical exponent is locally integrable, which
is the hypothesis `FundamentalSolution` asks for.

Every point sits inside a ball centred at the origin, so the ball statement
above already covers the whole space.
-/
theorem locallyIntegrable_radialKernel {exponent : ℝ}
    (subcritical : exponent < Module.finrank ℝ Point) :
    LocallyIntegrable (radialKernel (Point := Point) exponent) μ := by
  intro place
  refine ⟨ball 0 (‖place‖ + 1), isOpen_ball.mem_nhds ?_, ?_⟩
  · simp [mem_ball, dist_eq_norm]
  · exact integrableOn_radialKernel_ball μ subcritical _

/--
The Newtonian kernel `‖x‖^{2-n}` is locally integrable in every dimension.

This is the exact hypothesis `FundamentalSolution.locallyIntegrable` asks for
when the operator is the Laplacian, and it holds with room to spare: the
Newtonian exponent `n - 2` is two below the critical one.  No dimension is
special and none is assumed.
-/
theorem locallyIntegrable_newtonianKernel :
    LocallyIntegrable
      (radialKernel (Point := Point) ((Module.finrank ℝ Point : ℝ) - 2)) μ :=
  locallyIntegrable_radialKernel μ (by linarith)

end Hypostructure.PDE.Solution
