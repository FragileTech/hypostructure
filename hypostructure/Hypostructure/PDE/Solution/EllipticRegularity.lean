import Hypostructure.PDE.Solution.Bessel

/-!
# Elliptic regularity for the Laplacian

`PDE/Solution/Bessel.lean` gives a genuine graded solution operator, but for
`1 − (2π)^{-2} Δ` rather than for `Δ` itself.  That is not an accident of
mathlib's conventions: `Δ` has no inverse, because it kills the constants.

The textbook fix is not to invert `Δ` but to **bootstrap**.  A local residual
does not arrive as a bare source; it arrives already satisfying its equation,
and that is exactly the extra information that makes the gain available:

> if a state and its Laplacian both sit at grade `s`, the state sits at grade
> `s + 2`.

That is `memSobolev_add_two_of_laplacian` below, and it is what an elliptic
split actually consumes.  The proof is the standard one and needs no analysis
beyond what mathlib already proves — rewrite `Δ` as `1 − besselPotential 2`,
which is an identity of Fourier multipliers, and then apply the exact inverse
`besselPotential (-2)`.

The one piece mathlib does not state is that identity itself:
`besselPotential 2 = 1 − (2π)^{-2} Δ`.  Mathlib records it only in the
docstring of `besselPotential`; here it is proved, and it is the hinge of the
whole module.

Nothing here mentions a dimension, a domain or an equation beyond `Δ`.
-/

namespace Hypostructure.PDE.Solution.Bessel

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal Real Laplacian

section Hinge

variable {Point Value : Type*}
  [NormedAddCommGroup Point] [NormedAddCommGroup Value]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  [NormedSpace ℂ Value] [CompleteSpace Value]

/-! ## Additivity of Fourier multipliers

mathlib proves additivity over a `Finset`; the two-term case is what the
identity below needs, so it is specialized once here. -/

omit [CompleteSpace Value] in
theorem fourierMultiplier_add {first second : Point → ℂ}
    (temperate_first : first.HasTemperateGrowth)
    (temperate_second : second.HasTemperateGrowth)
    (value : 𝓢'(Point, Value)) :
    fourierMultiplierCLM Value (fun place => first place + second place) value =
      fourierMultiplierCLM Value first value +
        fourierMultiplierCLM Value second value := by
  have temperate : ∀ index ∈ (Finset.univ : Finset (Fin 2)),
      (![first, second] index).HasTemperateGrowth := by
    intro index _
    fin_cases index <;> assumption
  have sum_eq := fourierMultiplierCLM_sum (F := Value)
    (g := ![first, second]) temperate
  have pointwise : (fun place => ∑ index ∈ (Finset.univ : Finset (Fin 2)),
      ![first, second] index place) = fun place => first place + second place := by
    funext place
    simp [Fin.sum_univ_two]
  rw [pointwise] at sum_eq
  rw [sum_eq]
  simp [Fin.sum_univ_two]

/-! ## The hinge identity -/

omit [CompleteSpace Value] in
/--
The Bessel operator of order two **is** `1 − (2π)^{-2} Δ`.

mathlib states this only in prose, in the docstring of `besselPotential`.  It
is an identity of Fourier multipliers: the Bessel symbol at order two is
`1 + ‖ξ‖²`, and the Laplacian's symbol is `−(2π)²‖ξ‖²`.
-/
theorem besselPotential_two_eq (value : 𝓢'(Point, Value)) :
    besselPotential Point Value 2 value =
      value - (((2 * π) ^ 2 : ℝ))⁻¹ • Δ value := by
  have pi_ne : ((2 * π) ^ 2 : ℝ) ≠ 0 := by positivity
  have temperate_one : (fun _ : Point => (1 : ℂ)).HasTemperateGrowth := by
    fun_prop
  have temperate_sq :
      (fun place : Point => (Complex.ofReal (‖place‖ ^ 2))).HasTemperateGrowth := by
    fun_prop
  have multiplier :
      (fun place : Point => ((((1 + ‖place‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ)) : ℂ)) =
        fun place : Point => (1 : ℂ) + Complex.ofReal (‖place‖ ^ 2) := by
    funext place
    rw [show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    push_cast
    ring
  rw [besselPotential, multiplier, fourierMultiplier_add temperate_one temperate_sq,
    laplacian_eq_fourierMultiplierCLM value]
  have identity : fourierMultiplierCLM Value (fun _ : Point => (1 : ℂ)) value =
      value := by
    rw [fourierMultiplierCLM_const]
    simp
  rw [identity, smul_smul]
  rw [show ((2 * π) ^ 2 : ℝ)⁻¹ * (-(2 * π) ^ 2 : ℝ) = -1 by
    field_simp]
  simp

/-- `MemSobolev` is closed under real scalars, not only complex ones: the real
scalar acts through the complex one. -/
theorem memSobolev_real_smul {grade : ℝ} (scalar : ℝ) {value : 𝓢'(Point, Value)}
    (member : MemSobolev grade 2 value) :
    MemSobolev grade 2 (scalar • value) := by
  have transfer : ((scalar : ℂ)) • value = scalar • value :=
    algebraMap_smul ℂ scalar value
  rw [← transfer]
  exact member.smul _

/-! ## The bootstrap

This is the statement an elliptic split consumes.  It is conditional on the
equation — which is precisely what a local residual carries — and that is why
it can gain two grades where a bare inverse of `Δ` cannot exist.
-/

/--
**Elliptic regularity.**  If a tempered distribution and its Laplacian both
lie in `H^s`, the distribution lies in `H^{s+2}`.

No hypothesis names a domain, a dimension or a boundary condition: the gain
comes from the equation the residual already satisfies.
-/
theorem memSobolev_add_two_of_laplacian {grade : ℝ} {value : 𝓢'(Point, Value)}
    (state : MemSobolev grade 2 value)
    (source : MemSobolev grade 2 (Δ value)) :
    MemSobolev (grade + 2) 2 value := by
  have helmholtz_member :
      MemSobolev grade 2 (besselPotential Point Value 2 value) := by
    rw [besselPotential_two_eq]
    exact state.sub (memSobolev_real_smul _ source)
  have inverse : besselPotential Point Value (-2)
      (besselPotential Point Value 2 value) = value := by
    rw [besselPotential_besselPotential_apply]
    norm_num
  have gained := memSobolev_besselPotential_neg_two helmholtz_member
  rwa [inverse] at gained

omit [CompleteSpace Value] in
/--
The Laplacian read off the hinge identity: inverting the identity above
expresses `Δ` in terms of the Bessel operator, with no extra structure on the
value space.
-/
theorem laplacian_eq_of_besselPotential (value : 𝓢'(Point, Value)) :
    Δ value =
      ((2 * π) ^ 2 : ℝ) • (value - besselPotential Point Value 2 value) := by
  have pi_ne : ((2 * π) ^ 2 : ℝ) ≠ 0 := by positivity
  rw [besselPotential_two_eq, sub_sub_cancel, smul_smul,
    mul_inv_cancel₀ pi_ne, one_smul]

/-! ## The graded carrier

Restated on the `sobolev` subgroups of `PDE/Solution/Bessel.lean`, so the
graded elliptic interface can consume the bootstrap directly.
-/

/--
The bootstrap on the graded carrier: a local state whose Laplacian sits at its
own grade is promoted two grades, which is the regularity gain the graded
`ComponentEllipticOperator` demands of a solution step.
-/
theorem sobolev_add_two_of_laplacian {grade : ℝ} {value : 𝓢'(Point, Value)}
    (state : value ∈ sobolev (Point := Point) (Value := Value) grade)
    (source : Δ value ∈ sobolev (Point := Point) (Value := Value) grade) :
    value ∈ sobolev (Point := Point) (Value := Value) (grade + 2) :=
  mem_sobolev.mpr
    (memSobolev_add_two_of_laplacian (mem_sobolev.mp state) (mem_sobolev.mp source))

end Hinge

/-! ## The grade-lowering half

That `Δ` maps `H^s` into `H^{s-2}` is a genuine symbol estimate, and mathlib
proves it — but only where the value space carries a complex inner product,
because the proof runs through `MemSobolev.mono`.  Only this half pays that
cost; the hinge identity and the bootstrap above do not.
-/

section Lowering

variable {Point Value : Type*}
  [NormedAddCommGroup Point] [NormedAddCommGroup Value]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  [InnerProductSpace ℂ Value] [CompleteSpace Value]

/-- **The Laplacian lowers the grade by two**, the grade-lowering half of the
elliptic pair. -/
theorem memSobolev_laplacian_sub_two {grade : ℝ} {value : 𝓢'(Point, Value)}
    (state : MemSobolev grade 2 value) :
    MemSobolev (grade - 2) 2 (Δ value) :=
  MemSobolev.laplacian state

/-- The grade-lowering half on the graded carrier. -/
theorem laplacian_mem_sobolev_sub_two {grade : ℝ} {value : 𝓢'(Point, Value)}
    (state : value ∈ sobolev (Point := Point) (Value := Value) grade) :
    Δ value ∈ sobolev (Point := Point) (Value := Value) (grade - 2) :=
  mem_sobolev.mpr (memSobolev_laplacian_sub_two (mem_sobolev.mp state))

/--
The two halves compose: a state two grades up has its Laplacian exactly at the
lower grade.  This is what makes an elliptic split non-degenerate — the solved
part genuinely sits two grades above the source it was built from.
-/
theorem sobolev_laplacian_round_trip {grade : ℝ} {value : 𝓢'(Point, Value)}
    (state : value ∈ sobolev (Point := Point) (Value := Value) (grade + 2)) :
    Δ value ∈ sobolev (Point := Point) (Value := Value) grade := by
  have lowered := laplacian_mem_sobolev_sub_two state
  rwa [show grade + 2 - 2 = grade by ring] at lowered

end Lowering

end Hypostructure.PDE.Solution.Bessel
