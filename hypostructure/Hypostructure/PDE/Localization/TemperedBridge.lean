import Hypostructure.PDE.Localization.Cutoff

/-!
# From a distribution on a window to a tempered distribution

The framework carries two different distributional carriers, and until now
nothing joined them:

* a *local* object lives on a window, and is an element of `𝓓'(Ω, V)` --- a
  continuous functional on test functions supported inside the window;
* every *solve* the framework proves --- the graded inverse of
  `PDE/Solution/Bessel.lean` --- acts on `𝓢'(Point, V)`, the tempered
  distributions of the whole space.

There is no map from the first to the second, because a distribution on a
window says nothing at all about what happens outside it.  A *cut-off*
distribution does: multiply by a smooth compactly supported weight `χ`
supported inside the window, and the resulting functional makes sense on every
Schwartz function, because `χ · φ` is a legitimate test function of the window
no matter how `φ` behaves at infinity.

That is the bridge built here:

* `cutoffMulCLM` --- multiplication by `χ` as a *continuous* linear map
  `𝓢(Point, ℝ) →L[ℝ] 𝓓_{K}(Point, ℝ)`.  This is the analytic content: the
  Leibniz rule expands a derivative of `χ · φ` into finitely many products, and
  each factor is bounded by a Schwartz seminorm of `φ` times a fixed
  `𝓓_{K}`-seminorm of `χ`.  No decay of `φ` is used, only its derivatives on
  the fixed compact `K`; this is why the zeroth Schwartz weight `k = 0`
  suffices.
* `temperedOfLocal` --- the transpose: `T ↦ (φ ↦ T (χ · φ))`, delivered as an
  element of `𝓢'(Point, Value)`.
* `temperedOfLocal_apply_of_eqOn_one` --- **the property that makes the bridge
  usable.**  Where `χ ≡ 1`, cutting off changes nothing: the bridge applied to
  a test function supported there returns exactly what the original local
  object said.  This is the tempered-side analogue of `cutoffSmul_eq_of_mem`,
  and it is what lets a question asked about the cut-off object be answered
  about the original one on the inner window.

## Why the values are complex

mathlib's `𝓢'(E, F)` is `𝓢(E, ℂ) →L[ℂ] F`: tempered distributions are tested
against *complex* Schwartz functions and take values in a complex vector
space.  `𝓓'(Ω, F)` instead uses *real* test functions.  So the bridge is not a
plain transposition: it is the complexification of one, and the target has to
be a complex vector space.  We keep `Value` general with `[NormedSpace ℂ Value]`
because that is exactly the shape the solution library
(`PDE/Solution/Bessel.lean`, whose graded carrier is `𝓢'(Point, Value)` with
`[NormedSpace ℂ Value] [CompleteSpace Value]`) consumes; a real-valued local
object is carried over by composing with `Complex.ofRealCLM` first.

Nothing here names an equation, a dimension or a problem.
-/

namespace Hypostructure.PDE.Localization

open TopologicalSpace
open scoped Distributions SchwartzMap

universe uPoint uValue

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {domain : Opens Point} {window : Compacts Point}

/-! ## Multiplying a Schwartz function by a cutoff

A cutoff here is any smooth function vanishing off a fixed compact set, i.e.
an element of `𝓓_{window}(Point, ℝ)`; `Localization/Cutoff.lean` produces one
from a pair of nested balls, but nothing below needs it to be a bump.
-/

/--
The Schwartz function `test`, cut off by `cutoff`.

The product is smooth because both factors are, and it vanishes off `window`
because the cutoff does --- so it is a test function of the *window*, which is
the whole point: a Schwartz function is not compactly supported, and only after
multiplication is it something a local distribution can be asked about.
-/
noncomputable def cutoffMulTest (cutoff : 𝓓_{window}(Point, ℝ))
    (test : 𝓢(Point, ℝ)) : 𝓓_{window}(Point, ℝ) where
  toFun := fun place => cutoff place * test place
  contDiff' := cutoff.contDiff.mul (test.smooth ⊤)
  zero_on_compl' := by
    intro place outside
    simp [cutoff.zero_on_compl outside]

@[simp] theorem cutoffMulTest_apply (cutoff : 𝓓_{window}(Point, ℝ))
    (test : 𝓢(Point, ℝ)) (place : Point) :
    (cutoffMulTest cutoff test : Point → ℝ) place = cutoff place * test place :=
  rfl

/-- Cutting off is linear in the Schwartz function. -/
noncomputable def cutoffMulLM (cutoff : 𝓓_{window}(Point, ℝ)) :
    𝓢(Point, ℝ) →ₗ[ℝ] 𝓓_{window}(Point, ℝ) where
  toFun := cutoffMulTest cutoff
  map_add' := by
    intro left right
    refine DFunLike.ext _ _ fun place => ?_
    simp [mul_add]
  map_smul' := by
    intro scalar test
    refine DFunLike.ext _ _ fun place => ?_
    simp [mul_comm, mul_left_comm]

@[simp] theorem cutoffMulLM_apply (cutoff : 𝓓_{window}(Point, ℝ))
    (test : 𝓢(Point, ℝ)) :
    cutoffMulLM cutoff test = cutoffMulTest cutoff test :=
  rfl

/-! ### The Leibniz estimate

This is the analytic heart of the module.  The `order`-th derivative of a
product is a sum of `order + 1` terms, each a derivative of the cutoff against
a derivative of the test function.  The cutoff derivatives are bounded by the
`𝓓_{window}`-seminorms of the cutoff itself --- fixed constants --- and the
test-function derivatives by the Schwartz seminorms of weight zero.  The
resulting constant is the following finite sum.
-/

/-- The constant of the Leibniz estimate: the binomially weighted sum of the
first `order` seminorms of the cutoff.  It depends on the cutoff and the order
only, never on the test function, which is what makes the estimate a
continuity statement. -/
noncomputable def cutoffMulBound (cutoff : 𝓓_{window}(Point, ℝ)) (order : ℕ) :
    ℝ :=
  ∑ split ∈ Finset.range (order + 1), (order.choose split : ℝ) *
    ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ window split cutoff

theorem cutoffMulBound_nonneg (cutoff : 𝓓_{window}(Point, ℝ)) (order : ℕ) :
    0 ≤ cutoffMulBound cutoff order := by
  refine Finset.sum_nonneg fun split _ => ?_
  exact mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)

/-- Every Schwartz seminorm of weight zero and order at most `order` is
dominated by the supremum of the finitely many seminorms indexed by
`Finset.Iic (0, order)`.  This is the finite family the Leibniz estimate is
allowed to use. -/
theorem schwartzSeminorm_le_sup (test : 𝓢(Point, ℝ)) {order derivative : ℕ}
    (le : derivative ≤ order) :
    SchwartzMap.seminorm ℝ 0 derivative test ≤
      (Finset.Iic ((0 : ℕ), order)).sup
        (schwartzSeminormFamily ℝ Point ℝ) test := by
  have member : ((0 : ℕ), derivative) ∈ Finset.Iic ((0 : ℕ), order) :=
    Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr ⟨le_rfl, le⟩)
  exact Seminorm.le_def.mp
    (Finset.le_sup (f := schwartzSeminormFamily ℝ Point ℝ) member) test

/--
**The Leibniz estimate.**

Every `𝓓_{window}`-seminorm of the cut-off test function is bounded by a fixed
constant times the Schwartz seminorms of weight zero and order at most
`order`.  Only finitely many Schwartz seminorms appear, and the constant does
not depend on the test function: this is exactly the boundedness condition
that the seminorm presentation of both topologies turns into continuity.
-/
theorem seminorm_cutoffMulTest_le (cutoff : 𝓓_{window}(Point, ℝ)) (order : ℕ)
    (test : 𝓢(Point, ℝ)) :
    ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ window order
        (cutoffMulTest cutoff test) ≤
      cutoffMulBound cutoff order *
        (Finset.Iic ((0 : ℕ), order)).sup
          (schwartzSeminormFamily ℝ Point ℝ) test := by
  set schwartzBound :=
    (Finset.Iic ((0 : ℕ), order)).sup (schwartzSeminormFamily ℝ Point ℝ) test
    with schwartzBound_def
  have schwartzBound_nonneg : 0 ≤ schwartzBound := apply_nonneg _ _
  have product_nonneg : 0 ≤ cutoffMulBound cutoff order * schwartzBound :=
    mul_nonneg (cutoffMulBound_nonneg cutoff order) schwartzBound_nonneg
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ product_nonneg]
  intro place _
  have coeFun : (cutoffMulTest cutoff test : Point → ℝ) =
      fun candidate => (cutoff : Point → ℝ) candidate *
        (test : Point → ℝ) candidate := rfl
  rw [coeFun]
  calc ‖iteratedFDeriv ℝ order
        (fun candidate => (cutoff : Point → ℝ) candidate *
          (test : Point → ℝ) candidate) place‖
      ≤ ∑ split ∈ Finset.range (order + 1), (order.choose split : ℝ) *
          ‖iteratedFDeriv ℝ split (cutoff : Point → ℝ) place‖ *
          ‖iteratedFDeriv ℝ (order - split) (test : Point → ℝ) place‖ :=
        norm_iteratedFDeriv_mul_le cutoff.contDiff (test.smooth ⊤) place
          (by exact_mod_cast le_top)
    _ ≤ ∑ split ∈ Finset.range (order + 1), ((order.choose split : ℝ) *
          ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ window split cutoff) *
          schwartzBound := by
        refine Finset.sum_le_sum fun split _ => ?_
        have cutoffFactor :
            ‖iteratedFDeriv ℝ split (cutoff : Point → ℝ) place‖ ≤
              ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ window split cutoff :=
          ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
        have testFactor :
            ‖iteratedFDeriv ℝ (order - split) (test : Point → ℝ) place‖ ≤
              SchwartzMap.seminorm ℝ 0 (order - split) test :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ test _ place
        have supBound :
            SchwartzMap.seminorm ℝ 0 (order - split) test ≤ schwartzBound := by
          rw [schwartzBound_def]
          exact schwartzSeminorm_le_sup test (Nat.sub_le _ _)
        have testTotal :
            ‖iteratedFDeriv ℝ (order - split) (test : Point → ℝ) place‖ ≤
              schwartzBound := testFactor.trans supBound
        have chooseNonneg : (0 : ℝ) ≤ (order.choose split : ℝ) :=
          Nat.cast_nonneg _
        have seminormNonneg : (0 : ℝ) ≤
            ContDiffMapSupportedIn.seminorm ℝ Point ℝ ⊤ window split cutoff :=
          apply_nonneg _ _
        refine mul_le_mul ?_ testTotal (norm_nonneg _)
          (mul_nonneg chooseNonneg seminormNonneg)
        exact mul_le_mul_of_nonneg_left cutoffFactor chooseNonneg
    _ = cutoffMulBound cutoff order * schwartzBound := by
        rw [cutoffMulBound, Finset.sum_mul]

/-- Multiplication by the cutoff is continuous from the Schwartz space to the
test functions supported in `window`.  This is the Leibniz estimate read
through the seminorm presentations of the two topologies. -/
theorem continuous_cutoffMulLM (cutoff : 𝓓_{window}(Point, ℝ)) :
    Continuous (cutoffMulLM cutoff) := by
  refine WithSeminorms.continuous_of_isBounded
    (schwartz_withSeminorms ℝ Point ℝ)
    (ContDiffMapSupportedIn.withSeminorms ℝ Point ℝ ⊤ window) _ ?_
  refine Seminorm.IsBounded.of_real fun order => ?_
  exact ⟨Finset.Iic ((0 : ℕ), order), cutoffMulBound cutoff order,
    fun test => seminorm_cutoffMulTest_le cutoff order test⟩

/-- **Multiplication by a cutoff, as a continuous linear map.**  A Schwartz
function becomes a test function of the window, continuously. -/
noncomputable def cutoffMulCLM (cutoff : 𝓓_{window}(Point, ℝ)) :
    𝓢(Point, ℝ) →L[ℝ] 𝓓_{window}(Point, ℝ) where
  toLinearMap := cutoffMulLM cutoff
  cont := continuous_cutoffMulLM cutoff

@[simp] theorem cutoffMulCLM_apply (cutoff : 𝓓_{window}(Point, ℝ))
    (test : 𝓢(Point, ℝ)) :
    cutoffMulCLM cutoff test = cutoffMulTest cutoff test :=
  rfl

/-- The cut-off Schwartz function, seen as a test function of the open set
`domain`.  This is the map that a local distribution is fed. -/
noncomputable def cutoffTestCLM (cutoff : 𝓓_{window}(Point, ℝ))
    (inside : (window : Set Point) ⊆ domain) :
    𝓢(Point, ℝ) →L[ℝ] 𝓓(domain, ℝ) :=
  (TestFunction.ofSupportedInCLM ℝ inside).comp (cutoffMulCLM cutoff)

@[simp] theorem cutoffTestCLM_apply (cutoff : 𝓓_{window}(Point, ℝ))
    (inside : (window : Set Point) ⊆ domain) (test : 𝓢(Point, ℝ)) :
    cutoffTestCLM cutoff inside test =
      TestFunction.ofSupportedIn inside (cutoffMulTest cutoff test) :=
  rfl

/-! ## The bridge

A local object is a continuous functional on `𝓓(domain, ℝ)`.  Composing with
`cutoffTestCLM` turns it into a continuous functional on *real* Schwartz
functions; mathlib's tempered distributions want complex ones, so the last step
is the standard complexification `φ ↦ T (χ · Re φ) + i · T (χ · Im φ)`, whose
complex linearity is the only genuinely new computation.
-/

section Bridge

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- The real part of a complex Schwartz function, as a real Schwartz function.
Post-composition with a fixed continuous linear map is continuous. -/
noncomputable def schwartzRealPart : 𝓢(Point, ℂ) →L[ℝ] 𝓢(Point, ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM

/-- The imaginary part of a complex Schwartz function. -/
noncomputable def schwartzImagPart : 𝓢(Point, ℂ) →L[ℝ] 𝓢(Point, ℝ) :=
  SchwartzMap.postcompCLM Complex.imCLM

@[simp] theorem schwartzRealPart_apply (test : 𝓢(Point, ℂ)) (place : Point) :
    (schwartzRealPart test : Point → ℝ) place = (test place).re :=
  rfl

@[simp] theorem schwartzImagPart_apply (test : 𝓢(Point, ℂ)) (place : Point) :
    (schwartzImagPart test : Point → ℝ) place = (test place).im :=
  rfl

/-- The real-linear functional underlying the bridge: pair the local object
against the cut-off real part, and against the cut-off imaginary part rotated
by `i`. -/
noncomputable def temperedOfLocalRealCLM (local_ : 𝓓'(domain, Value)) :
    𝓢(Point, ℂ) →L[ℝ] Value :=
  (local_.comp (cutoffTestCLM cutoff inside)).comp schwartzRealPart +
    Complex.I •
      (local_.comp (cutoffTestCLM cutoff inside)).comp schwartzImagPart

@[simp] theorem temperedOfLocalRealCLM_apply (local_ : 𝓓'(domain, Value))
    (test : 𝓢(Point, ℂ)) :
    temperedOfLocalRealCLM cutoff inside local_ test =
      local_ (cutoffTestCLM cutoff inside (schwartzRealPart test)) +
        Complex.I •
          local_ (cutoffTestCLM cutoff inside (schwartzImagPart test)) :=
  rfl

/-- The bridge is complex linear: this is the identity `Re (c φ) = c.re Re φ −
c.im Im φ`, `Im (c φ) = c.re Im φ + c.im Re φ` recombined by `i · i = −1`. -/
theorem temperedOfLocalRealCLM_map_smul (local_ : 𝓓'(domain, Value))
    (scalar : ℂ) (test : 𝓢(Point, ℂ)) :
    temperedOfLocalRealCLM cutoff inside local_ (scalar • test) =
      scalar • temperedOfLocalRealCLM cutoff inside local_ test := by
  have realSplit : schwartzRealPart (scalar • test) =
      scalar.re • schwartzRealPart test - scalar.im • schwartzImagPart test := by
    refine DFunLike.ext _ _ fun place => ?_
    simp [Complex.mul_re]
  have imagSplit : schwartzImagPart (scalar • test) =
      scalar.re • schwartzImagPart test + scalar.im • schwartzRealPart test := by
    refine DFunLike.ext _ _ fun place => ?_
    simp [Complex.mul_im]
  simp only [temperedOfLocalRealCLM_apply, realSplit, imagSplit, map_add,
    map_sub, map_smul, smul_add, smul_smul]
  set realValue := local_ (cutoffTestCLM cutoff inside (schwartzRealPart test))
    with realValue_def
  set imagValue := local_ (cutoffTestCLM cutoff inside (schwartzImagPart test))
    with imagValue_def
  conv_rhs => rw [← Complex.re_add_im scalar]
  simp only [add_smul, smul_smul, ← Complex.coe_smul]
  match_scalars
  · ring
  · linear_combination (-(scalar.im : ℂ)) * Complex.I_sq

/--
**The bridge.**

A distribution on the window becomes a tempered distribution once cut off:
`T ↦ (φ ↦ T (χ · φ))`.  This is the map the framework was missing, and it is
what lets a local object be handed to the whole-space graded solve.
-/
noncomputable def temperedOfLocal (local_ : 𝓓'(domain, Value)) :
    𝓢'(Point, Value) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (𝓢(Point, ℂ))
    Value
    { toFun := temperedOfLocalRealCLM cutoff inside local_
      map_add' := fun left right => by
        simp [map_add]
      map_smul' := fun scalar test =>
        temperedOfLocalRealCLM_map_smul cutoff inside local_ scalar test
      cont := (temperedOfLocalRealCLM cutoff inside local_).continuous }

@[simp] theorem temperedOfLocal_apply (local_ : 𝓓'(domain, Value))
    (test : 𝓢(Point, ℂ)) :
    temperedOfLocal cutoff inside local_ test =
      local_ (cutoffTestCLM cutoff inside (schwartzRealPart test)) +
        Complex.I •
          local_ (cutoffTestCLM cutoff inside (schwartzImagPart test)) :=
  rfl

/-! ### Linearity of the bridge in the local object -/

theorem temperedOfLocal_add (first second : 𝓓'(domain, Value)) :
    temperedOfLocal cutoff inside (first + second) =
      temperedOfLocal cutoff inside first +
        temperedOfLocal cutoff inside second := by
  ext test
  simp [temperedOfLocal_apply, smul_add]
  abel

theorem temperedOfLocal_smul (scalar : ℝ) (local_ : 𝓓'(domain, Value)) :
    temperedOfLocal cutoff inside (scalar • local_) =
      scalar • temperedOfLocal cutoff inside local_ := by
  ext test
  simp [temperedOfLocal_apply, smul_add, smul_comm scalar Complex.I]

theorem temperedOfLocal_zero :
    temperedOfLocal cutoff inside (0 : 𝓓'(domain, Value)) = 0 := by
  ext test
  simp [temperedOfLocal_apply]

end Bridge

/-! ## Nothing is lost where the cutoff is one

The bridge is only worth having if the cut-off object still answers questions
about the original one.  It does, on the set where `χ ≡ 1`: there the cut-off
test function *is* the test function, so the two objects agree.  This is the
tempered-side analogue of `cutoffSmul_eq_of_mem`.
-/

section InnerWindow

/-- A Schwartz function that happens to be supported in the compact `window`,
seen as a test function of the window.  This is the object the bridge must
reproduce on the inner window. -/
noncomputable def schwartzSupportedIn (test : 𝓢(Point, ℝ))
    (supported : tsupport (test : Point → ℝ) ⊆ window) :
    𝓓_{window}(Point, ℝ) where
  toFun := test
  contDiff' := test.smooth ⊤
  zero_on_compl' := by
    intro place outside
    exact image_eq_zero_of_notMem_tsupport fun mem => outside (supported mem)

@[simp] theorem schwartzSupportedIn_apply (test : 𝓢(Point, ℝ))
    (supported : tsupport (test : Point → ℝ) ⊆ window) (place : Point) :
    (schwartzSupportedIn test supported : Point → ℝ) place = test place :=
  rfl

/-- **Cutting off changes nothing where the cutoff is one.**  On a test
function whose support meets only the region where `χ ≡ 1`, multiplication by
`χ` is the identity. -/
theorem cutoffMulTest_eq_of_eqOn_one (cutoff : 𝓓_{window}(Point, ℝ))
    (test : 𝓢(Point, ℝ))
    (supported : tsupport (test : Point → ℝ) ⊆ window)
    (unit : ∀ place ∈ tsupport (test : Point → ℝ), cutoff place = 1) :
    cutoffMulTest cutoff test = schwartzSupportedIn test supported := by
  refine DFunLike.ext _ _ fun place => ?_
  by_cases mem : place ∈ tsupport (test : Point → ℝ)
  · simp [unit place mem]
  · have vanishes : (test : Point → ℝ) place = 0 :=
      image_eq_zero_of_notMem_tsupport mem
    simp [vanishes]

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- The real part of a complex Schwartz function is supported where the
function is. -/
theorem tsupport_schwartzRealPart_subset (test : 𝓢(Point, ℂ)) :
    tsupport (schwartzRealPart test : Point → ℝ) ⊆
      tsupport (test : Point → ℂ) := by
  refine closure_mono (Function.support_subset_iff.mpr fun place nonzero => ?_)
  intro absurd_zero
  exact nonzero (by simp [schwartzRealPart_apply, absurd_zero])

/-- The imaginary part of a complex Schwartz function is supported where the
function is. -/
theorem tsupport_schwartzImagPart_subset (test : 𝓢(Point, ℂ)) :
    tsupport (schwartzImagPart test : Point → ℝ) ⊆
      tsupport (test : Point → ℂ) := by
  refine closure_mono (Function.support_subset_iff.mpr fun place nonzero => ?_)
  intro absurd_zero
  exact nonzero (by simp [schwartzImagPart_apply, absurd_zero])

/--
**The bridge is the identity on the inner window.**

If the Schwartz function is supported where the cutoff is one, the tempered
distribution produced by the bridge returns exactly the value the original
local object gives on that test function.  Nothing the local object knew about
its own window is lost by cutting off --- which is why a statement proved for
the cut-off object is a statement about the original one there.
-/
theorem temperedOfLocal_apply_of_eqOn_one (local_ : 𝓓'(domain, Value))
    (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ tsupport (test : Point → ℂ), cutoff place = 1) :
    temperedOfLocal cutoff inside local_ test =
      local_ (TestFunction.ofSupportedIn inside
          (schwartzSupportedIn (schwartzRealPart test)
            ((tsupport_schwartzRealPart_subset test).trans supported))) +
        Complex.I • local_ (TestFunction.ofSupportedIn inside
          (schwartzSupportedIn (schwartzImagPart test)
            ((tsupport_schwartzImagPart_subset test).trans supported))) := by
  have realPart := cutoffMulTest_eq_of_eqOn_one cutoff (schwartzRealPart test)
    ((tsupport_schwartzRealPart_subset test).trans supported)
    (fun place mem => unit place (tsupport_schwartzRealPart_subset test mem))
  have imagPart := cutoffMulTest_eq_of_eqOn_one cutoff (schwartzImagPart test)
    ((tsupport_schwartzImagPart_subset test).trans supported)
    (fun place mem => unit place (tsupport_schwartzImagPart_subset test mem))
  rw [temperedOfLocal_apply, cutoffTestCLM_apply, cutoffTestCLM_apply,
    realPart, imagPart]

end InnerWindow

/-! ## The bridge carries derivatives

The bridge would be useless to a *differential* equation if it did not commute
with differentiation, and in general it does not: `χ · T` and `T` have
different derivatives, by exactly `(∂χ) · T`.  But `∂χ` vanishes wherever
`χ ≡ 1`, so on the inner window the two agree --- which is the only place the
framework ever reads the bridged object.

This is the connector between the framework's two distributional carriers.  A
baseline states its equation in `𝓓'(Ω, V)` with `Distribution.lineDerivCLM`;
every solve the framework owns acts on `𝓢'(Point, V)` with `lineDerivOp`.
Without the lemma below a represented equation cannot be handed to a solve at
all, and with it a local balance becomes a tempered one on the inner window,
where the parabolic bootstrap consumes it.

Both sides are read only against test functions supported where the cutoff is
one, so the statement is exactly as local as the window it is about.
-/

section Derivative

open scoped LineDeriv

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- **Reading a real part commutes with differentiating.**  Both operations are
post-composition with a continuous linear map --- one on values, one inside
`fderiv` --- so this is the chain rule for a linear outer map. -/
theorem schwartzRealPart_lineDerivOp (direction : Point) (test : 𝓢(Point, ℂ)) :
    schwartzRealPart (∂_{direction} test) =
      ∂_{direction} (schwartzRealPart test) := by
  refine DFunLike.ext _ _ fun place => ?_
  rw [schwartzRealPart_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have chain : fderiv ℝ (schwartzRealPart test : Point → ℝ) place =
      Complex.reCLM.comp (fderiv ℝ (test : Point → ℂ) place) :=
    (Complex.reCLM.hasFDerivAt.comp place
      (test.differentiable.differentiableAt.hasFDerivAt)).fderiv
  rw [chain]
  rfl

/-- The imaginary part, identically. -/
theorem schwartzImagPart_lineDerivOp (direction : Point) (test : 𝓢(Point, ℂ)) :
    schwartzImagPart (∂_{direction} test) =
      ∂_{direction} (schwartzImagPart test) := by
  refine DFunLike.ext _ _ fun place => ?_
  rw [schwartzImagPart_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have chain : fderiv ℝ (schwartzImagPart test : Point → ℝ) place =
      Complex.imCLM.comp (fderiv ℝ (test : Point → ℂ) place) :=
    (Complex.imCLM.hasFDerivAt.comp place
      (test.differentiable.differentiableAt.hasFDerivAt)).fderiv
  rw [chain]
  rfl

/-- Differentiating a window test function that happens to be Schwartz is
differentiating it as a Schwartz function.  Both sides are `lineDeriv` of the
same underlying map, so the identity is `TestFunction.lineDerivCLM_apply_of_le`
against `SchwartzMap.lineDerivOp_apply`. -/
theorem lineDerivCLM_ofSupportedIn_schwartzSupportedIn
    (direction : Point) (test : 𝓢(Point, ℝ))
    (supported : tsupport (test : Point → ℝ) ⊆ window)
    (derivative_supported :
      tsupport ((∂_{direction} test : 𝓢(Point, ℝ)) : Point → ℝ) ⊆ window) :
    (TestFunction.lineDerivCLM ℝ direction
        (TestFunction.ofSupportedIn inside
          (schwartzSupportedIn test supported)) : 𝓓(domain, ℝ)) =
      TestFunction.ofSupportedIn inside
        (schwartzSupportedIn (∂_{direction} test) derivative_supported) := by
  refine TestFunction.ext fun place => ?_
  rw [TestFunction.lineDerivCLM_apply_of_le le_top]
  exact (SchwartzMap.lineDerivOp_apply direction test place).symm

/--
**The bridge commutes with differentiation on the inner window.**

Read against a test function supported where the cutoff is one, differentiating
the bridged object and bridging the differentiated one give the same value.
The proof is the transpose on both sides --- each derivative is `T ↦ −T (∂φ)`
--- followed by `temperedOfLocal_apply_of_eqOn_one`, which is applicable to
`∂φ` because `tsupport (∂φ) ⊆ tsupport φ`.

This is the statement that lets a baseline's represented equation be handed to
a whole-space solve: no smoothness, no estimate and no global hypothesis enters
it.
-/
theorem temperedOfLocal_lineDerivOp_apply_of_eqOn_one
    (local_ : 𝓓'(domain, Value)) (direction : Point) (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    (∂_{direction} (temperedOfLocal cutoff inside local_) :
        𝓢'(Point, Value)) test =
      temperedOfLocal cutoff inside
        (Distribution.lineDerivCLM direction local_) test := by
  have derivative_supported :
      tsupport ((-∂_{direction} test : 𝓢(Point, ℂ)) : Point → ℂ) ⊆ window := by
    refine subset_trans (subset_trans ?_
      (SchwartzMap.tsupport_lineDerivOp_subset direction test)) supported
    exact subset_of_eq (tsupport_neg _)
  -- The left side: differentiate, then bridge.
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    temperedOfLocal_apply_of_eqOn_one cutoff inside local_ _ derivative_supported
      (fun place mem => unit place (derivative_supported mem)),
    temperedOfLocal_apply_of_eqOn_one cutoff inside _ test supported
      (fun place mem => unit place (supported mem))]
  -- The right side: bridge, then differentiate; each summand is a transpose.
  rw [Distribution.lineDerivCLM_apply, Distribution.lineDerivCLM_apply,
    lineDerivCLM_ofSupportedIn_schwartzSupportedIn inside direction _ _
      ((SchwartzMap.tsupport_lineDerivOp_subset direction _).trans
        ((tsupport_schwartzRealPart_subset test).trans supported)),
    lineDerivCLM_ofSupportedIn_schwartzSupportedIn inside direction _ _
      ((SchwartzMap.tsupport_lineDerivOp_subset direction _).trans
        ((tsupport_schwartzImagPart_subset test).trans supported))]
  -- What is left is that reading a part commutes with differentiating.
  have realPart : (schwartzRealPart (-∂_{direction} test) : 𝓢(Point, ℝ)) =
      -∂_{direction} (schwartzRealPart test) := by
    rw [map_neg, schwartzRealPart_lineDerivOp]
  have imagPart : (schwartzImagPart (-∂_{direction} test) : 𝓢(Point, ℝ)) =
      -∂_{direction} (schwartzImagPart test) := by
    rw [map_neg, schwartzImagPart_lineDerivOp]
  have realArgument :
      (TestFunction.ofSupportedIn inside
        (schwartzSupportedIn (schwartzRealPart (-∂_{direction} test))
          ((tsupport_schwartzRealPart_subset _).trans derivative_supported)) :
        𝓓(domain, ℝ)) =
      -TestFunction.ofSupportedIn inside
        (schwartzSupportedIn (∂_{direction} (schwartzRealPart test))
          ((SchwartzMap.tsupport_lineDerivOp_subset direction _).trans
            ((tsupport_schwartzRealPart_subset test).trans supported))) := by
    refine TestFunction.ext fun place => ?_
    simpa using congrFun (congrArg (fun weight : 𝓢(Point, ℝ) =>
      (weight : Point → ℝ)) realPart) place
  have imagArgument :
      (TestFunction.ofSupportedIn inside
        (schwartzSupportedIn (schwartzImagPart (-∂_{direction} test))
          ((tsupport_schwartzImagPart_subset _).trans derivative_supported)) :
        𝓓(domain, ℝ)) =
      -TestFunction.ofSupportedIn inside
        (schwartzSupportedIn (∂_{direction} (schwartzImagPart test))
          ((SchwartzMap.tsupport_lineDerivOp_subset direction _).trans
            ((tsupport_schwartzImagPart_subset test).trans supported))) := by
    refine TestFunction.ext fun place => ?_
    simpa using congrFun (congrArg (fun weight : 𝓢(Point, ℝ) =>
      (weight : Point → ℝ)) imagPart) place
  rw [realArgument, imagArgument, map_neg, map_neg, smul_neg]

/--
**The same for a second derivative.**

Applying the connector twice: the inner one to the already-differentiated test
function --- legitimate because `tsupport (∂φ) ⊆ tsupport φ`, so it is still
supported where the cutoff is one --- and the outer one to `φ` itself.  A
Laplacian is a finite sum of these, which is what a heat operator needs.
-/
theorem temperedOfLocal_lineDerivOp_lineDerivOp_apply_of_eqOn_one
    (local_ : 𝓓'(domain, Value)) (first second : Point) (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    (∂_{first} (∂_{second} (temperedOfLocal cutoff inside local_)) :
        𝓢'(Point, Value)) test =
      temperedOfLocal cutoff inside
        ((Distribution.lineDerivCLM first :
            𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
          ((Distribution.lineDerivCLM second :
            𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) local_)) test := by
  have derivative_supported :
      tsupport ((-∂_{first} test : 𝓢(Point, ℂ)) : Point → ℂ) ⊆ window :=
    subset_trans (subset_trans (subset_of_eq (tsupport_neg _))
      (SchwartzMap.tsupport_lineDerivOp_subset first test)) supported
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    temperedOfLocal_lineDerivOp_apply_of_eqOn_one cutoff inside local_ second _
      derivative_supported unit,
    ← TemperedDistribution.lineDerivOp_apply_apply,
    temperedOfLocal_lineDerivOp_apply_of_eqOn_one cutoff inside _ first test
      supported unit]

/-! ### Any finite string of derivatives

A curl of a heat operator differentiates three times, a heat operator of a curl
likewise, and neither is a special case of the other.  Rather than name each
arity, the connector is stated once for an arbitrary list of directions: both
carriers fold their own derivative over the list, and the bridge carries the
fold.  The single and double forms above are the one- and two-element cases.
-/

/-- A string of derivatives on the tempered carrier, in the order the list
gives them. -/
noncomputable def temperedLineDerivs (directions : List Point)
    (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  directions.foldr (fun direction accumulated => ∂_{direction} accumulated) state

/-- The same string on the local carrier. -/
noncomputable def localLineDerivs (directions : List Point)
    (local_ : 𝓓'(domain, Value)) : 𝓓'(domain, Value) :=
  directions.foldr
    (fun direction accumulated =>
      (Distribution.lineDerivCLM direction :
        𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) accumulated)
    local_

@[simp] theorem temperedLineDerivs_nil (state : 𝓢'(Point, Value)) :
    temperedLineDerivs [] state = state := rfl

@[simp] theorem temperedLineDerivs_cons (direction : Point)
    (directions : List Point) (state : 𝓢'(Point, Value)) :
    temperedLineDerivs (direction :: directions) state =
      ∂_{direction} (temperedLineDerivs directions state) := rfl

@[simp] theorem localLineDerivs_nil (local_ : 𝓓'(domain, Value)) :
    localLineDerivs [] local_ = local_ := rfl

@[simp] theorem localLineDerivs_cons (direction : Point)
    (directions : List Point) (local_ : 𝓓'(domain, Value)) :
    localLineDerivs (direction :: directions) local_ =
      (Distribution.lineDerivCLM direction :
        𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
        (localLineDerivs directions local_) := rfl

/--
**The bridge carries any string of derivatives on the inner window.**

Induction on the list: the outermost derivative is peeled off by the transpose,
leaving the inductive hypothesis to be applied to `∂φ`, which is still
supported where the cutoff is one; the single-derivative connector then closes
the step.

This is the general form of the connector between the framework's two
distributional carriers.  Every differential operator the regularity theory
uses --- gradient, divergence, curl, Laplacian, heat --- is a finite linear
combination of these strings, so each of them transports by this lemma plus
linearity of the bridge, and none of them needs its own argument.
-/
theorem temperedOfLocal_lineDerivs_apply_of_eqOn_one
    (local_ : 𝓓'(domain, Value)) (directions : List Point)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    ∀ (test : 𝓢(Point, ℂ)), tsupport (test : Point → ℂ) ⊆ window →
      temperedLineDerivs directions
          (temperedOfLocal cutoff inside local_) test =
        temperedOfLocal cutoff inside
          (localLineDerivs directions local_) test := by
  induction directions with
  | nil => intro test _; rfl
  | cons direction rest inductive_hypothesis =>
    intro test supported
    have derivative_supported :
        tsupport ((-∂_{direction} test : 𝓢(Point, ℂ)) : Point → ℂ) ⊆ window :=
      subset_trans (subset_trans (subset_of_eq (tsupport_neg _))
        (SchwartzMap.tsupport_lineDerivOp_subset direction test)) supported
    rw [temperedLineDerivs_cons, TemperedDistribution.lineDerivOp_apply_apply,
      inductive_hypothesis _ derivative_supported,
      ← TemperedDistribution.lineDerivOp_apply_apply,
      temperedOfLocal_lineDerivOp_apply_of_eqOn_one cutoff inside _ direction
        test supported unit,
      localLineDerivs_cons]

end Derivative

/-! ### The bridge is linear in the local object, continued

`temperedOfLocal_add` above is enough for a first derivative; a Laplacian is a
finite sum and a heat operator a difference, so both are recorded here.
-/

section Linear

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

theorem temperedOfLocal_sub (first second : 𝓓'(domain, Value)) :
    temperedOfLocal cutoff inside (first - second) =
      temperedOfLocal cutoff inside first -
        temperedOfLocal cutoff inside second := by
  ext test
  simp only [temperedOfLocal_apply, ContinuousLinearMap.sub_apply, map_sub,
    smul_sub]
  abel

theorem temperedOfLocal_sum {Coordinate : Type*} (indices : Finset Coordinate)
    (family : Coordinate → 𝓓'(domain, Value)) :
    temperedOfLocal cutoff inside (∑ index ∈ indices, family index) =
      ∑ index ∈ indices, temperedOfLocal cutoff inside (family index) := by
  classical
  induction indices using Finset.induction with
  | empty => simp [temperedOfLocal_zero]
  | insert head rest notMem inductive_hypothesis =>
    rw [Finset.sum_insert notMem, temperedOfLocal_add, inductive_hypothesis,
      Finset.sum_insert notMem]

end Linear

/-! ## The framework's own cutoff

Everything above is stated for an arbitrary smooth weight supported in a
compact set, because that is all the analysis needs.  The framework already
manufactures such a weight from a pair of nested balls in
`Localization/Cutoff.lean`; bundling it here is what lets a window --- a centre
and two radii --- be handed to the bridge directly, and it is what turns the
abstract "where `χ ≡ 1`" hypothesis into the concrete "on the inner ball".
-/

section Bump

open Metric

variable [HasContDiffBump Point] [FiniteDimensional ℝ Point]

/-- The compact set the framework's cutoff is supported in. -/
noncomputable def cutoffCompacts (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) : Compacts Point where
  carrier := tsupport (cutoff center inner_pos nested)
  isCompact' := cutoff_hasCompactSupport center inner_pos nested

/-- The framework's cutoff, bundled as a smooth function supported in the
compact `cutoffCompacts`, which is the form the bridge consumes. -/
noncomputable def cutoffTest (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    𝓓_{cutoffCompacts center inner_pos nested}(Point, ℝ) where
  toFun := cutoff center inner_pos nested
  contDiff' := cutoff_contDiff center inner_pos nested
  zero_on_compl' := fun _place outside =>
    image_eq_zero_of_notMem_tsupport outside

@[simp] theorem cutoffTest_apply (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (place : Point) :
    (cutoffTest center inner_pos nested : Point → ℝ) place =
      cutoff center inner_pos nested place :=
  rfl

/-- The inner ball sits inside the support of the cutoff, because the cutoff
is one there.  This is what makes the inner-window hypothesis of the bridge
satisfiable by the framework's own cutoff. -/
theorem closedBall_subset_cutoffCompacts (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    closedBall center inner ⊆
      (cutoffCompacts center inner_pos nested : Set Point) := by
  intro place mem
  refine subset_tsupport _ ?_
  rw [Function.mem_support, cutoff_eq_one center inner_pos nested mem]
  exact one_ne_zero

/--
**The framework's bridge is the identity on the inner window.**

A test function that lives on the inner ball is answered by the cut-off object
exactly as the original local object would answer it: the cutoff is one there,
so the two agree.  This is `cutoffSmul_eq_of_mem` for the tempered bridge, and
it is the reason a solve performed against the cut-off object is a statement
about the original one on the inner window.
-/
theorem temperedOfLocal_cutoffTest_apply_of_subset (center : Point)
    {inner outer : ℝ} (inner_pos : 0 < inner) (nested : inner < outer)
    (inside : (cutoffCompacts center inner_pos nested : Set Point) ⊆ domain)
    (local_ : 𝓓'(domain, Value)) (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ closedBall center inner) :
    temperedOfLocal (cutoffTest center inner_pos nested) inside local_ test =
      local_ (TestFunction.ofSupportedIn inside
          (schwartzSupportedIn (schwartzRealPart test)
            ((tsupport_schwartzRealPart_subset test).trans
              (supported.trans
                (closedBall_subset_cutoffCompacts center inner_pos nested))))) +
        Complex.I • local_ (TestFunction.ofSupportedIn inside
          (schwartzSupportedIn (schwartzImagPart test)
            ((tsupport_schwartzImagPart_subset test).trans
              (supported.trans
                (closedBall_subset_cutoffCompacts center inner_pos
                  nested))))) :=
  temperedOfLocal_apply_of_eqOn_one _ inside local_ test
    (supported.trans (closedBall_subset_cutoffCompacts center inner_pos nested))
    (fun _place mem =>
      cutoff_eq_one center inner_pos nested (supported mem))

end Bump

end Hypostructure.PDE.Localization

