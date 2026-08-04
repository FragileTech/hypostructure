import Mathlib

/-!
# Local solution operator on an interval window

The framework's elliptic split needs one thing it cannot derive: a *solution
operator* for the local source.  This module proves the first instance, in
one dimension, on a window.

Working locally is what makes it elementary.  On a window with left endpoint
`base` the operator is

```text
solution base f x = x * ∫_base^x f - ∫_base^x t * f t
```

which is the usual `∫_base^x (x - t) f t` written so that no integrand
depends on the upper limit, and its second derivative is `f` by the
fundamental theorem of calculus applied twice.  No fundamental solution, no
surface measure, and no global statement is involved.
-/

namespace Hypostructure.PDE.Solution

open intervalIntegral

/-- The smoothness exponent for infinitely differentiable functions. -/
abbrev smoothIndex : WithTop ENat := ((⊤ : ENat) : WithTop ENat)

/-- The local solution operator on a window with left endpoint `base`. -/
noncomputable def interval (base : ℝ) (source : ℝ → ℝ) : ℝ → ℝ :=
  fun place =>
    place * (∫ t in base..place, source t) - ∫ t in base..place, t * source t

variable (base : ℝ) {source : ℝ → ℝ}

/-- The first derivative of the local solution is the primitive of the
source. -/
theorem hasDerivAt_interval (continuous : Continuous source) (place : ℝ) :
    HasDerivAt (interval base source) (∫ t in base..place, source t) place := by
  unfold interval
  have primitive :
      HasDerivAt (fun upper => ∫ t in base..upper, source t) (source place)
        place :=
    (continuous.integral_hasStrictDerivAt base place).hasDerivAt
  have weighted :
      HasDerivAt (fun upper => ∫ t in base..upper, t * source t)
        (place * source place) place :=
    ((continuous_id.mul continuous).integral_hasStrictDerivAt base place).hasDerivAt
  have product := (hasDerivAt_id place).mul primitive
  simp only [id_eq, one_mul] at product
  have combined := product.sub weighted
  have value :
      (∫ t in base..place, source t) + place * source place -
          place * source place =
        ∫ t in base..place, source t := by ring
  rwa [value] at combined

theorem deriv_interval (continuous : Continuous source) (place : ℝ) :
    deriv (interval base source) place = ∫ t in base..place, source t :=
  (hasDerivAt_interval base continuous place).deriv

theorem deriv_interval_eq (continuous : Continuous source) :
    deriv (interval base source) =
      fun place => ∫ t in base..place, source t :=
  funext fun place => deriv_interval base continuous place

/--
The local solution operator solves the equation: its second derivative is the
source.

This is the one-dimensional instance of the datum the elliptic split cannot
derive, and it is proved here rather than assumed.
-/
theorem deriv_deriv_interval (continuous : Continuous source) (place : ℝ) :
    deriv (deriv (interval base source)) place = source place := by
  rw [deriv_interval_eq base continuous]
  exact (continuous.integral_hasStrictDerivAt base place).hasDerivAt.deriv


/-! ## The smooth carrier

The framework's `Carrier` must be an additive group on which the operator is
an endomorphism.  Smooth functions are the natural choice in one dimension:
they are closed under the second derivative, which `C²` is not.
-/

/-- Smooth real functions on the line, as an additive subgroup. -/
def smoothFunctions : AddSubgroup (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ smoothIndex f}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ContDiff.add ha hb
  zero_mem' := show ContDiff ℝ smoothIndex (0 : ℝ → ℝ) from contDiff_const
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ContDiff.neg ha

@[simp] theorem mem_smoothFunctions {f : ℝ → ℝ} :
    f ∈ smoothFunctions ↔ ContDiff ℝ smoothIndex f := Iff.rfl

/-- Smoothness is inherited by the primitive of a smooth function. -/
theorem contDiff_primitive (base : ℝ) {source : ℝ → ℝ}
    (smooth : ContDiff ℝ smoothIndex source) :
    ContDiff ℝ smoothIndex fun place => ∫ t in base..place, source t := by
  have derivative :
      deriv (fun place => ∫ t in base..place, source t) = source := by
    funext place
    exact (smooth.continuous.integral_hasStrictDerivAt base place).hasDerivAt.deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun place => ?_, ?_⟩
  · exact (smooth.continuous.integral_hasStrictDerivAt base place).hasDerivAt.differentiableAt
  · rw [derivative]; exact smooth

/-- The local solution of a smooth source is smooth. -/
theorem contDiff_interval (base : ℝ) {source : ℝ → ℝ}
    (smooth : ContDiff ℝ smoothIndex source) : ContDiff ℝ smoothIndex (interval base source) := by
  have weightedSmooth : ContDiff ℝ smoothIndex fun t => t * source t := contDiff_id.mul smooth
  exact (contDiff_id.mul (contDiff_primitive base smooth)).sub
    (contDiff_primitive base weightedSmooth)


/-! ## The operator and its solution, as framework data

`secondDeriv` is the elliptic operator as an endomorphism of the carrier, and
`solutionOn` is the local solution operator.  The base point is an argument,
so a model passes the *window's own* base and never recenters by hand.
-/

theorem smoothIndex_ne_zero : smoothIndex ≠ 0 := by
  simp [smoothIndex]

theorem deriv_add_smooth {f g : ℝ → ℝ}
    (hf : ContDiff ℝ smoothIndex f) (hg : ContDiff ℝ smoothIndex g) :
    deriv (f + g) = deriv f + deriv g := by
  funext place
  exact deriv_add (hf.differentiable smoothIndex_ne_zero place)
    (hg.differentiable smoothIndex_ne_zero place)

theorem contDiff_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ smoothIndex f) :
    ContDiff ℝ smoothIndex (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

/-- The second derivative as an endomorphism of the smooth carrier. -/
noncomputable def secondDeriv : smoothFunctions →+ smoothFunctions where
  toFun f := ⟨deriv (deriv f.val), contDiff_deriv (contDiff_deriv f.2)⟩
  map_zero' := by
    apply Subtype.ext
    show deriv (deriv (0 : ℝ → ℝ)) = 0
    simp
  map_add' := by
    intro f g
    apply Subtype.ext
    show deriv (deriv (f.val + g.val)) = deriv (deriv f.val) + deriv (deriv g.val)
    rw [deriv_add_smooth f.2 g.2,
      deriv_add_smooth (contDiff_deriv f.2) (contDiff_deriv g.2)]

@[simp] theorem secondDeriv_val (f : smoothFunctions) :
    (secondDeriv f).val = deriv (deriv f.val) := rfl

/-- The local solution operator on the carrier, based at the window's own
left endpoint. -/
noncomputable def solutionOn (base : ℝ) (f : smoothFunctions) :
    smoothFunctions :=
  ⟨interval base f.val, contDiff_interval base f.2⟩

/--
The local solution operator solves the equation, on the carrier.

This is the datum the elliptic split cannot derive, now available as
framework data with its law proved.
-/
theorem secondDeriv_solutionOn (base : ℝ) (f : smoothFunctions) :
    secondDeriv (solutionOn base f) = f := by
  have smooth : ContDiff ℝ smoothIndex f.val := f.2
  apply Subtype.ext
  show deriv (deriv (interval base f.val)) = f.val
  funext place
  exact deriv_deriv_interval base smooth.continuous place

/-! ## The graded carrier

A solution operator is only worth having if it *gains regularity*.  Grading
the carrier makes that a typing constraint rather than a side condition: the
elliptic operator lowers the grade by two and the solution operator raises it
by two, so an entry that gains nothing --- the identity, or anything obtained
by adding a kernel element --- cannot even be stated.
-/

/-- The `C^grade` functions on the line, as an additive subgroup. -/
def contDiffFunctions (grade : ℕ) : AddSubgroup (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) f}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ContDiff.add ha hb
  zero_mem' :=
    show ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) (0 : ℝ → ℝ) from contDiff_const
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ContDiff.neg ha

@[simp] theorem mem_contDiffFunctions {grade : ℕ} {f : ℝ → ℝ} :
    f ∈ contDiffFunctions grade ↔
      ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) f := Iff.rfl

/-- Differentiating drops the grade by one. -/
theorem contDiff_deriv_of_succ {grade : ℕ} {f : ℝ → ℝ}
    (smooth : ContDiff ℝ (((grade + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) (deriv f) := by
  have cast : (((grade + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
      ((grade : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
  rw [cast, contDiff_succ_iff_deriv] at smooth
  exact smooth.2.2

/-- Integrating raises the grade by one. -/
theorem contDiff_primitive_succ (base : ℝ) {grade : ℕ} {source : ℝ → ℝ}
    (smooth : ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) source) :
    ContDiff ℝ ((((grade + 1 : ℕ)) : ℕ∞) : WithTop ℕ∞)
      (fun place => ∫ t in base..place, source t) := by
  have cast : ((((grade + 1 : ℕ)) : ℕ∞) : WithTop ℕ∞) =
      ((grade : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
  have derivative :
      deriv (fun place => ∫ t in base..place, source t) = source := by
    funext place
    exact (smooth.continuous.integral_hasStrictDerivAt base place).hasDerivAt.deriv
  rw [cast, contDiff_succ_iff_deriv]
  refine ⟨fun place => ?_, ?_, ?_⟩
  · exact (smooth.continuous.integral_hasStrictDerivAt base
      place).hasDerivAt.differentiableAt
  · intro analytic
    exact absurd analytic (by simp)
  · rw [derivative]; exact smooth

/-- The local solution gains two grades: this is the content of the
solution operator, and it is what a fake entry cannot supply. -/
theorem contDiff_interval_add_two (base : ℝ) {grade : ℕ} {source : ℝ → ℝ}
    (smooth : ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) source) :
    ContDiff ℝ ((((grade + 2 : ℕ)) : ℕ∞) : WithTop ℕ∞)
      (interval base source) := by
  have cast : ((((grade + 2 : ℕ)) : ℕ∞) : WithTop ℕ∞) =
      ((((grade + 1 : ℕ)) : ℕ∞) : WithTop ℕ∞) + 1 := by
    push_cast
    abel
  rw [cast, contDiff_succ_iff_deriv]
  refine ⟨fun place => ?_, ?_, ?_⟩
  · exact (hasDerivAt_interval base smooth.continuous place).differentiableAt
  · intro analytic
    exact absurd analytic (by simp)
  · rw [deriv_interval_eq base smooth.continuous]
    exact contDiff_primitive_succ base smooth

/-! ## The graded operator and solution

The signatures are the whole point.  `secondDerivGraded` goes down two
grades, `solutionOnGraded` goes up two, and their composite is the identity.
An entry that gains nothing would have to inhabit
`contDiffFunctions grade → contDiffFunctions (grade + 2)` by doing nothing,
which is a type error --- so `identity` and "component minus a kernel
element" are not expressible here.
-/

/-- The second derivative, lowering the grade by two. -/
noncomputable def secondDerivGraded (grade : ℕ) :
    contDiffFunctions (grade + 2) →+ contDiffFunctions grade where
  toFun f := ⟨deriv (deriv f.val), by
    have first : ContDiff ℝ (((grade + 1 : ℕ) : ℕ∞) : WithTop ℕ∞)
        (deriv f.val) := contDiff_deriv_of_succ f.2
    exact contDiff_deriv_of_succ first⟩
  map_zero' := by
    apply Subtype.ext
    show deriv (deriv (0 : ℝ → ℝ)) = 0
    simp
  map_add' := by
    intro f g
    apply Subtype.ext
    show deriv (deriv (f.val + g.val)) =
      deriv (deriv f.val) + deriv (deriv g.val)
    have differentiableOnce : ∀ h : ℝ → ℝ,
        ContDiff ℝ ((((grade + 2 : ℕ)) : ℕ∞) : WithTop ℕ∞) h →
          Differentiable ℝ h := by
      intro h hh
      exact hh.differentiable (by simp)
    have step : deriv (f.val + g.val) = deriv f.val + deriv g.val := by
      funext place
      exact deriv_add ((differentiableOnce f.val f.2) place)
        ((differentiableOnce g.val g.2) place)
    rw [step]
    funext place
    exact deriv_add
      (((contDiff_deriv_of_succ f.2).differentiable (by simp)) place)
      (((contDiff_deriv_of_succ g.2).differentiable (by simp)) place)

/-- The local solution operator, raising the grade by two. -/
noncomputable def solutionOnGraded (base : ℝ) (grade : ℕ)
    (source : contDiffFunctions grade) : contDiffFunctions (grade + 2) :=
  ⟨interval base source.val, contDiff_interval_add_two base source.2⟩

/--
The graded solution operator solves the equation.

Together with the signatures above, this is the honest statement of what a
solution operator is: it produces a solution *and* gains two grades.
-/
theorem secondDerivGraded_solutionOnGraded (base : ℝ) (grade : ℕ)
    (source : contDiffFunctions grade) :
    secondDerivGraded grade (solutionOnGraded base grade source) = source := by
  have smooth : ContDiff ℝ ((grade : ℕ∞) : WithTop ℕ∞) source.val := source.2
  apply Subtype.ext
  show deriv (deriv (interval base source.val)) = source.val
  funext place
  exact deriv_deriv_interval base smooth.continuous place

end Hypostructure.PDE.Solution
