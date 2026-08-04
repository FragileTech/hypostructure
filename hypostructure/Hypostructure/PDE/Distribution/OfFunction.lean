import Mathlib
import Hypostructure.PDE.Distribution.Local

/-!
# Distributions represented by functions

Mathlib provides the space of distributions, its topology and its
derivatives, but no way to *build* one from a function: there is no
`ofLocallyIntegrable`, so every concrete distribution has to be assembled
from the universal property of the LF topology by hand.

This module is that missing constructor, written once so the rest of the PDE
layer can rely on it.  It is the building block every concrete elliptic
datum needs --- a kernel element, a source, a fundamental solution --- and it
is deliberately stated for a general normed space and a general measure
rather than for any one equation.

The assembly is the standard one:

* `TestFunction.mkCLM` reduces continuity on `𝓓^{n}(Ω, F)` to continuity on
  each `𝓓^{n}_{K}(E, F)`;
* `ContDiffMapSupportedIn.withSeminorms` presents that topology by the
  sup-norms of the iterated derivatives;
* pairing against a locally integrable weight is bounded by the zeroth of
  those seminorms, with constant the `L¹` norm of the weight on `K`.
-/

namespace Hypostructure.PDE.Distribution

open MeasureTheory TopologicalSpace
open scoped Distributions

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [NormedSpace ℝ Point] [MeasurableSpace Point] [OpensMeasurableSpace Point]
  {domain : Opens Point} {μ : Measure Point}

/-- Pairing a test function against a weight. -/
noncomputable def pairing (weight : Point → ℝ) (μ : Measure Point)
    (test : 𝓓(domain, ℝ)) : ℝ :=
  ∫ place, test place * weight place ∂μ

@[simp] theorem pairing_apply (weight : Point → ℝ) (μ : Measure Point)
    (test : 𝓓(domain, ℝ)) :
    pairing weight μ test = ∫ place, test place * weight place ∂μ :=
  rfl

/-- A test function paired against a locally integrable weight is
integrable: the test function is bounded with compact support. -/
theorem integrable_pairing (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ)
    (test : 𝓓(domain, ℝ)) :
    Integrable (fun place => test place * weight place) μ :=
  locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    test.contDiff.continuous test.hasCompactSupport

/-! ## Linearity of the pairing

These are the `map_add` and `map_smul` obligations of `TestFunction.mkCLM`.
Both reduce to linearity of the integral once `integrable_pairing` supplies
the integrability side conditions.
-/

theorem pairing_add (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ)
    (left right : 𝓓(domain, ℝ)) :
    pairing weight μ (left + right) =
      pairing weight μ left + pairing weight μ right := by
  have expand : ∀ place : Point,
      (left + right) place * weight place =
        left place * weight place + right place * weight place := by
    intro place
    simp [add_mul]
  simp only [pairing, expand]
  exact integral_add (integrable_pairing weight locallyIntegrable left)
    (integrable_pairing weight locallyIntegrable right)

theorem pairing_smul (weight : Point → ℝ) (scalar : ℝ)
    (test : 𝓓(domain, ℝ)) :
    pairing weight μ (scalar • test) = scalar * pairing weight μ test := by
  have expand : ∀ place : Point,
      (scalar • test) place * weight place =
        scalar * (test place * weight place) := by
    intro place
    simp [mul_assoc]
  simp only [pairing, expand]
  exact integral_const_mul scalar _

/-! ## Boundedness on each compactly-supported piece

This is the `cont` obligation of `TestFunction.mkCLM`.  Pairing against a
locally integrable weight is bounded on `𝓓_{K}` by the `L¹` norm of the
weight on `K` times the sup-norm seminorm, which is the standard estimate.
-/

theorem norm_pairing_ofSupportedIn_le (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ)
    {K : Compacts Point} (K_sub_domain : (K : Set Point) ⊆ domain)
    (f : 𝓓_{K}(Point, ℝ)) :
    ‖pairing weight μ (TestFunction.ofSupportedIn K_sub_domain f)‖ ≤
      (∫ place in (K : Set Point), ‖weight place‖ ∂μ) *
        ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ K 0 f := by
  have weightOn : IntegrableOn weight (K : Set Point) μ :=
    locallyIntegrable.integrableOn_isCompact K.isCompact
  have normOn : IntegrableOn (fun place => ‖weight place‖) (K : Set Point) μ :=
    weightOn.norm
  have vanish : ∀ place ∉ (K : Set Point),
      ‖(f : Point → ℝ) place * weight place‖ = 0 := by
    intro place notMem
    have : (f : Point → ℝ) place = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun mem => notMem (f.tsupport_subset mem))
    simp [this]
  calc ‖pairing weight μ (TestFunction.ofSupportedIn K_sub_domain f)‖
      = ‖∫ place, (f : Point → ℝ) place * weight place ∂μ‖ := by
        simp [pairing]
    _ ≤ ∫ place, ‖(f : Point → ℝ) place * weight place‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ place in (K : Set Point), ‖(f : Point → ℝ) place * weight place‖ ∂μ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero vanish).symm
    _ ≤ ∫ place in (K : Set Point),
          ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ K 0 f *
            ‖weight place‖ ∂μ := by
        refine setIntegral_mono_on ?_ ?_ K.isCompact.measurableSet ?_
        · exact ((integrable_pairing weight locallyIntegrable
            (TestFunction.ofSupportedIn K_sub_domain f)).norm).integrableOn
        · exact normOn.const_mul _
        · intro place _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ) (norm_nonneg _)
    _ = (∫ place in (K : Set Point), ‖weight place‖ ∂μ) *
          ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ K 0 f := by
        rw [integral_const_mul]
        ring

/-! ## The constructor -/

/-- The pairing as a linear map on test functions. -/
noncomputable def pairingLM (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ) :
    𝓓(domain, ℝ) →ₗ[ℝ] ℝ where
  toFun := pairing weight μ
  map_add' := pairing_add weight locallyIntegrable
  map_smul' := fun scalar test => pairing_smul weight scalar test

/-- Continuity on each compactly-supported piece, from the `L¹` bound. -/
theorem continuous_pairing_ofSupportedIn (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ)
    (K : Compacts Point) (K_sub_domain : (K : Set Point) ⊆ domain) :
    Continuous (pairing weight μ ∘ TestFunction.ofSupportedIn K_sub_domain) := by
  have bounded :
      Seminorm.IsBounded (ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ K)
        (fun _ : Fin 1 => normSeminorm ℝ ℝ)
        (((pairingLM weight locallyIntegrable).comp
          (TestFunction.ofSupportedInCLM ℝ K_sub_domain).toLinearMap)) := by
    refine Seminorm.IsBounded.of_real fun _index => ?_
    refine ⟨{0}, ∫ place in (K : Set Point), ‖weight place‖ ∂μ, fun f => ?_⟩
    rw [Finset.sup_singleton]
    exact norm_pairing_ofSupportedIn_le weight locallyIntegrable K_sub_domain f
  exact WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℝ Point ℝ ⊤ K)
    (norm_withSeminorms ℝ ℝ) _ bounded

/--
The distribution represented by a locally integrable function.

This is the constructor mathlib does not provide.  Every concrete
distribution the PDE layer needs --- a source, a kernel element, a
fundamental solution --- is built from it.
-/
noncomputable def ofLocallyIntegrable (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ) : 𝓓'(domain, ℝ) :=
  TestFunction.mkCLM ℝ (pairing weight μ)
    (pairing_add weight locallyIntegrable)
    (fun scalar test => pairing_smul weight scalar test)
    (continuous_pairing_ofSupportedIn weight locallyIntegrable)

@[simp] theorem ofLocallyIntegrable_apply (weight : Point → ℝ)
    (locallyIntegrable : LocallyIntegrable weight μ) (test : 𝓓(domain, ℝ)) :
    ofLocallyIntegrable weight locallyIntegrable test =
      ∫ place, test place * weight place ∂μ :=
  rfl

/-! ## The constant distribution and its vanishing derivative

The first concrete distribution the constructor gives us, together with the
fact that makes it a kernel element of every Laplace-type operator: the
integral of a directional derivative of a compactly supported smooth
function vanishes.
-/

section Constant

variable [BorelSpace Point] [FiniteDimensional ℝ Point]
  [MeasureTheory.Measure.IsAddHaarMeasure μ]

/-- The integral of a directional derivative of a compactly supported smooth
function vanishes.  Integration by parts against the constant function. -/
theorem integral_lineDeriv_eq_zero {g : Point → ℝ}
    (smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (compact : HasCompactSupport g) (direction : Point) :
    ∫ place, lineDeriv ℝ g place direction ∂μ = 0 := by
  obtain ⟨D, lipschitz⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport compact smooth (by simp)
  have parts :=
    LipschitzWith.integral_lineDeriv_mul_eq (μ := μ) (C := 0)
      (f := fun _ => (1 : ℝ)) (LipschitzWith.const 1) lipschitz compact
      (-direction)
  have constDeriv : ∀ place : Point,
      lineDeriv ℝ (fun _ => (1 : ℝ)) place (-direction) = 0 := by
    intro place
    simp [lineDeriv]
  simp only [constDeriv, zero_mul, integral_zero, mul_one, neg_neg] at parts
  exact parts.symm

/-- The distribution represented by the constant function `1`. -/
noncomputable def constant (domain : Opens Point) (μ : Measure Point)
    [IsLocallyFiniteMeasure μ] : 𝓓'(domain, ℝ) :=
  ofLocallyIntegrable (fun _ => (1 : ℝ)) (locallyIntegrable_const (μ := μ) 1)

@[simp] theorem constant_apply (domain : Opens Point) (μ : Measure Point)
    [IsLocallyFiniteMeasure μ] (test : 𝓓(domain, ℝ)) :
    constant domain μ test = ∫ place, test place ∂μ := by
  simp [constant]

/-- One direction of the duality computation: two distributional derivatives
of the constant distribution annihilate every test function. -/
theorem constant_lineDeriv_lineDeriv (direction : Point)
    (test : 𝓓(domain, ℝ)) :
    (((Distribution.lineDerivCLM direction :
        Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤).comp
      (Distribution.lineDerivCLM direction :
        Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤))
        (constant domain μ)) test = 0 := by
  rw [ContinuousLinearMap.comp_apply, Distribution.lineDerivCLM_apply,
    Distribution.lineDerivCLM_apply, neg_neg, constant_apply]
  have pointwise : ∀ place : Point,
      ((TestFunction.lineDerivCLM ℝ direction
        (TestFunction.lineDerivCLM ℝ direction test) : 𝓓(domain, ℝ)) :
          Point → ℝ) place =
        lineDeriv ℝ
          ((TestFunction.lineDerivCLM ℝ direction test : 𝓓(domain, ℝ)) :
            Point → ℝ) place direction :=
    fun _place => TestFunction.lineDerivCLM_apply_of_le le_top
  simp only [pointwise]
  exact integral_lineDeriv_eq_zero
    (TestFunction.lineDerivCLM ℝ direction test).contDiff
    (TestFunction.lineDerivCLM ℝ direction test).hasCompactSupport direction

/--
The constant distribution is annihilated by every Laplace-type operator.

This is the first non-zero kernel element the framework can prove, and it is
what makes a Laplace-type split genuinely two-term.  It is pure duality: the
operator moves onto the test function, and the integral of a second
directional derivative of a test function vanishes.
-/
theorem laplaceTypeCLM_constant {Index : Type uIndex} [Fintype Index]
    (directions : Index → Point) :
    laplaceTypeCLM domain directions (constant domain μ) = 0 := by
  ext test
  simp only [laplaceTypeCLM, ContinuousLinearMap.sum_apply,
    constant_lineDeriv_lineDeriv, Finset.sum_const_zero]
  rfl

end Constant

end Hypostructure.PDE.Distribution
