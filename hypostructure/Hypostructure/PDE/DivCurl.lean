import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The div–curl step: recovering a field from its curl

A first-order rotational datum determines a first-order field once two things
are supplied: the divergence, and a normalization against the fields that carry
no first-order datum at all.  This file records the two facts that make that
recovery work, and nothing else.

## The vector identity

Everything rests on one algebraic identity between the three classical
first/second-order operators:

> `-Δ v = curl (curl v) - grad (div v)`.

For a divergence-free field it degenerates to `-Δ v = curl (curl v)`.  This is
the whole reason a rotational datum controls the field: the field satisfies a
*vector Poisson equation whose right-hand side is built from the rotational
datum alone*.  Regularity of the datum is therefore inherited by the field
through whatever elliptic theory is available for `Δ`, and the identity is the
only step of that argument which is specific to the operators involved.

The identity is proved twice here, at two different altitudes:

* `CurlDivergenceCalculus` — an abstract triple `(curl, div, Δ)` together with
  a gradient, carrying the identity as a field.  Consumers that only need the
  consequences of the identity should take this structure as a hypothesis, so
  that they are insensitive to how the operators are realized.
* `curl_curl` — the identity for the concrete coordinate operators on a
  three-dimensional real space, proved from the symmetry of second derivatives
  and nothing else.  This is what makes the abstract layer non-vacuous:
  `smoothCalculus` assembles it into a `CurlDivergenceCalculus`.

The identity is genuinely three-dimensional in its statement (`curl` maps
fields to fields only in dimension three) but not in its proof: every step is
the commutation of two coordinate derivatives.

## The kernel of both operators

The fields with vanishing divergence *and* vanishing curl are exactly the ones
invisible to the recovery: they can be added to any solution.  So the recovered
field is only well defined modulo that kernel, and a normalization has to pick
a representative.  `harmonicKernel` is that kernel, formulated for an abstract
Hilbert state space with continuous divergence and curl operators — the
continuity is exactly what the analytic realization supplies (divergence and
curl of a square-integrable field are continuous into a negative-order space).

Two facts are proved about it:

* `isClosed_harmonicKernel` — it is a closed subspace, because it is an
  intersection of kernels of continuous linear maps.  Closedness is what buys
  the orthogonal projection, via the Hilbert projection theorem already in
  mathlib.
* `harmonicComplement` and its theorems — subtracting the projection changes
  neither the divergence nor the curl, and produces the *unique* field with
  prescribed divergence and curl orthogonal to the kernel.  That uniqueness is
  the precise sense in which the rotational datum determines the field.

Members of the kernel are annihilated by the Laplacian
(`laplacian_eq_zero_of_curl_eq_zero`), which is the abstract identity applied
to the normalization: the discarded component is harmonic, hence as regular as
the elliptic theory for `Δ` allows, and never an obstruction to regularity.

## What is *not* here

The quantitative interior elliptic estimate for the vector Poisson equation —
the inequality bounding derivatives of the field on an inner ball by the datum
on an outer ball — is not formalized.  It is a statement about the elliptic
operator `Δ`, not about the div–curl structure, and it is orthogonal to
everything proved here: this file supplies exactly the reduction that makes
such an estimate applicable.
-/

namespace Hypostructure.PDE.DivCurl

open scoped ContDiff

/-! ## The identity, abstractly -/

/-- An abstract first-order vector calculus: the four operators that appear in
the div–curl identity, together with the identity itself.

Only the group structure of the field space and the zero of the scalar space
are used, so this can be instantiated by smooth fields, by distributions, by
formal symbol calculi, or by any algebraic model of the operators.  The point
of the abstraction is that every consequence below follows from
`curl_curl_eq` alone; no analysis enters.

The sign convention is the classical one, `-Δ = curl ∘ curl - grad ∘ div`,
rearranged so that the composite of the two curls sits on the left. -/
structure CurlDivergenceCalculus (VectorField ScalarField : Type*)
    [AddCommGroup VectorField] [Zero ScalarField] where
  /-- The rotational first-order operator. -/
  curl : VectorField → VectorField
  /-- The trace of the first-order derivative. -/
  divergence : VectorField → ScalarField
  /-- The first-order operator producing fields from scalars. -/
  gradient : ScalarField → VectorField
  /-- The second-order operator whose regularity theory is being invoked. -/
  laplacian : VectorField → VectorField
  /-- The identity `curl (curl v) = grad (div v) - Δ v`, equivalently
  `-Δ v = curl (curl v) - grad (div v)`.  This is the entire mathematical
  content of the div–curl reduction. -/
  curl_curl_eq : ∀ field, curl (curl field) = gradient (divergence field) - laplacian field
  /-- The rotational operator annihilates the zero field. -/
  curl_zero : curl 0 = 0
  /-- The gradient annihilates the zero scalar. -/
  gradient_zero : gradient 0 = 0

namespace CurlDivergenceCalculus

variable {VectorField ScalarField : Type*} [AddCommGroup VectorField] [Zero ScalarField]
  (calculus : CurlDivergenceCalculus VectorField ScalarField) {field : VectorField}

/-- **The div–curl reduction.**  For a divergence-free field the identity
collapses to a vector Poisson equation whose right-hand side is built from the
rotational datum alone: `-Δ v = curl (curl v)`.

This is the step that turns a regularity statement about `curl v` into a
regularity statement about `v`, because the right-hand side is one derivative
of data that is already known. -/
theorem neg_laplacian_eq_curl_curl (divergence_free : calculus.divergence field = 0) :
    -calculus.laplacian field = calculus.curl (calculus.curl field) := by
  rw [calculus.curl_curl_eq field, divergence_free, calculus.gradient_zero, zero_sub]

/-- The same reduction with the Laplacian isolated on the left. -/
theorem laplacian_eq_neg_curl_curl (divergence_free : calculus.divergence field = 0) :
    calculus.laplacian field = -calculus.curl (calculus.curl field) := by
  rw [← calculus.neg_laplacian_eq_curl_curl divergence_free, neg_neg]

/-- A field that is invisible to both first-order operators is harmonic.

This is why the normalization discarded by the div–curl recovery is never an
obstruction: whatever elliptic theory is available for `Δ` applies to it.  It
is also the reason the kernel deserves the name *harmonic*. -/
theorem laplacian_eq_zero_of_curl_eq_zero (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0) : calculus.laplacian field = 0 := by
  rw [calculus.laplacian_eq_neg_curl_curl divergence_free, curl_free, calculus.curl_zero, neg_zero]

/-- Two fields with the same divergence and the same curl have the same
Laplacian *difference*: their difference is harmonic.  This is the uniqueness
half of the recovery, before any normalization is imposed. -/
theorem laplacian_sub_eq_zero_of_curl_eq
    (additive_curl : ∀ first second : VectorField,
      calculus.curl (first - second) = calculus.curl first - calculus.curl second)
    (additive_divergence : ∀ first second : VectorField,
      calculus.divergence (first - second) = 0 ↔ calculus.divergence first =
        calculus.divergence second)
    {first second : VectorField}
    (same_divergence : calculus.divergence first = calculus.divergence second)
    (same_curl : calculus.curl first = calculus.curl second) :
    calculus.laplacian (first - second) = 0 :=
  calculus.laplacian_eq_zero_of_curl_eq_zero ((additive_divergence first second).2 same_divergence)
    (by rw [additive_curl, same_curl, sub_self])

end CurlDivergenceCalculus

/-! ## Directional derivatives

The concrete realization needs three facts about directional derivatives, all
of them generic in the domain: they are additive, they preserve smoothness,
and they commute.  Only the last is a real theorem, and it is the symmetry of
the second derivative. -/

section Directional

variable {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  {weight first second : Domain → ℝ}

/-- The derivative of a scalar weight along a fixed direction, as a weight
again.  Junk (zero) at points of non-differentiability, as usual for
`fderiv`; every statement below carries the smoothness it needs. -/
noncomputable def directionalDeriv (direction : Domain) (weight : Domain → ℝ) : Domain → ℝ :=
  fun place => fderiv ℝ weight place direction

/-- Directional differentiation is additive on differentiable weights. -/
theorem directionalDeriv_add (direction : Domain) (first_differentiable : Differentiable ℝ first)
    (second_differentiable : Differentiable ℝ second) :
    directionalDeriv direction (first + second) =
      directionalDeriv direction first + directionalDeriv direction second := by
  funext place
  have expand : fderiv ℝ (first + second) place = fderiv ℝ first place + fderiv ℝ second place :=
    fderiv_add (first_differentiable place) (second_differentiable place)
  simp [directionalDeriv, expand]

/-- Directional differentiation is subtractive on differentiable weights. -/
theorem directionalDeriv_sub (direction : Domain) (first_differentiable : Differentiable ℝ first)
    (second_differentiable : Differentiable ℝ second) :
    directionalDeriv direction (first - second) =
      directionalDeriv direction first - directionalDeriv direction second := by
  funext place
  have expand : fderiv ℝ (first - second) place = fderiv ℝ first place - fderiv ℝ second place :=
    fderiv_sub (first_differentiable place) (second_differentiable place)
  simp [directionalDeriv, expand]

/-- Directional differentiation annihilates the zero weight. -/
@[simp] theorem directionalDeriv_zero (direction : Domain) :
    directionalDeriv direction (0 : Domain → ℝ) = 0 := by
  funext place
  simp [directionalDeriv]

/-- A smooth weight has a smooth derivative in any fixed direction: the
derivative map is smooth, and evaluating a continuous linear map at a fixed
argument is itself continuous linear. -/
theorem contDiff_directionalDeriv (direction : Domain)
    (smooth : ContDiff ℝ ∞ weight) : ContDiff ℝ ∞ (directionalDeriv direction weight) :=
  (ContinuousLinearMap.apply ℝ ℝ direction).contDiff.comp
    (contDiff_infty_iff_fderiv.1 smooth).2

/-- A smooth map is differentiable. -/
theorem differentiable_of_contDiff {Codomain : Type*} [NormedAddCommGroup Codomain]
    [NormedSpace ℝ Codomain] {map : Domain → Codomain} (smooth : ContDiff ℝ ∞ map) :
    Differentiable ℝ map := smooth.differentiable (by simp)

/-- Iterated directional differentiation is the second derivative evaluated at
the two directions.  Separating this out is what lets the symmetry theorem for
the second derivative be applied to a nest of two `directionalDeriv`s. -/
theorem directionalDeriv_directionalDeriv_apply (smooth : ContDiff ℝ ∞ weight)
    (outer inner : Domain) (place : Domain) :
    directionalDeriv outer (directionalDeriv inner weight) place =
      fderiv ℝ (fderiv ℝ weight) place outer inner := by
  have derivative_differentiable : DifferentiableAt ℝ (fderiv ℝ weight) place :=
    (differentiable_of_contDiff (contDiff_infty_iff_fderiv.1 smooth).2) place
  have expand := fderiv_clm_apply (c := fderiv ℝ weight) (u := fun _ : Domain => inner)
    derivative_differentiable (differentiableAt_const inner)
  show fderiv ℝ (fun point => fderiv ℝ weight point inner) place outer = _
  rw [expand]
  simp

/-- **Directional derivatives commute on smooth weights.**  This is the
symmetry of the second derivative, and it is the only analytic input to the
div–curl identity. -/
theorem directionalDeriv_comm (smooth : ContDiff ℝ ∞ weight) (outer inner : Domain) :
    directionalDeriv outer (directionalDeriv inner weight) =
      directionalDeriv inner (directionalDeriv outer weight) := by
  funext place
  have differentiable : Differentiable ℝ weight := differentiable_of_contDiff smooth
  have derivative_differentiable : Differentiable ℝ (fderiv ℝ weight) :=
    differentiable_of_contDiff (contDiff_infty_iff_fderiv.1 smooth).2
  have symmetry := second_derivative_symmetric (𝕜 := ℝ) (f := weight) (f' := fderiv ℝ weight)
    (x := place) (fun point => (differentiable point).hasFDerivAt)
    (derivative_differentiable place).hasFDerivAt outer inner
  rw [directionalDeriv_directionalDeriv_apply smooth, directionalDeriv_directionalDeriv_apply smooth,
    symmetry]

end Directional

/-! ## The identity, concretely

The concrete operators live on fields on a three-dimensional real inner
product space.  The three components of the curl are the three cyclic
rotations of one formula, which is what makes the identity provable once and
for all in the index rather than three times by cases. -/

/-- The three-dimensional domain. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- Scalar weights on the domain. -/
abbrev ScalarField : Type := Space → ℝ

/-- Vector fields on the domain, in coordinates. -/
abbrev VectorField : Type := Space → Fin 3 → ℝ

/-- The coordinate direction of a given axis. -/
noncomputable def axisDirection (axis : Fin 3) : Space := EuclideanSpace.single axis (1 : ℝ)

/-- Differentiation along a coordinate axis. -/
noncomputable def coordinateDeriv (axis : Fin 3) (weight : ScalarField) : ScalarField :=
  directionalDeriv (axisDirection axis) weight

/-- One coordinate of a vector field, as a scalar weight. -/
def component (index : Fin 3) (field : VectorField) : ScalarField := fun place => field place index

/-- The antisymmetric two-index derivative combination out of which the curl is
built.  Writing the curl through this makes each of its components a *single*
instance of one formula. -/
noncomputable def curlComponent (first second : Fin 3) (field : VectorField) : ScalarField :=
  coordinateDeriv first (component second field) - coordinateDeriv second (component first field)

/-- The rotational operator.  The `index`-th component is the cyclic
combination at `index + 1` and `index + 2`; in `Fin 3` those are exactly the
other two axes in the standard orientation, so this is the classical curl. -/
noncomputable def curl (field : VectorField) : VectorField :=
  fun place index => curlComponent (index + 1) (index + 2) field place

/-- The trace of the first derivative. -/
noncomputable def divergence (field : VectorField) : ScalarField :=
  coordinateDeriv 0 (component 0 field) + coordinateDeriv 1 (component 1 field)
    + coordinateDeriv 2 (component 2 field)

/-- The gradient of a scalar weight. -/
noncomputable def gradient (weight : ScalarField) : VectorField :=
  fun place index => coordinateDeriv index weight place

/-- The Laplacian of a scalar weight. -/
noncomputable def scalarLaplacian (weight : ScalarField) : ScalarField :=
  coordinateDeriv 0 (coordinateDeriv 0 weight) + coordinateDeriv 1 (coordinateDeriv 1 weight)
    + coordinateDeriv 2 (coordinateDeriv 2 weight)

/-- The Laplacian of a vector field, componentwise. -/
noncomputable def laplacian (field : VectorField) : VectorField :=
  fun place index => scalarLaplacian (component index field) place

section Concrete

variable {field : VectorField} {weight : ScalarField}

/-- Components of a smooth field are smooth. -/
theorem contDiff_component (smooth : ContDiff ℝ ∞ field) (index : Fin 3) :
    ContDiff ℝ ∞ (component index field) := contDiff_pi.1 smooth index

/-- Coordinate differentiation preserves smoothness. -/
theorem contDiff_coordinateDeriv (axis : Fin 3) (smooth : ContDiff ℝ ∞ weight) :
    ContDiff ℝ ∞ (coordinateDeriv axis weight) :=
  contDiff_directionalDeriv _ smooth

/-- Coordinate differentiation is subtractive on smooth weights. -/
theorem coordinateDeriv_sub (axis : Fin 3) {first second : ScalarField}
    (first_smooth : ContDiff ℝ ∞ first) (second_smooth : ContDiff ℝ ∞ second) :
    coordinateDeriv axis (first - second) =
      coordinateDeriv axis first - coordinateDeriv axis second :=
  directionalDeriv_sub _ (differentiable_of_contDiff first_smooth)
    (differentiable_of_contDiff second_smooth)

/-- Coordinate differentiation is additive on smooth weights. -/
theorem coordinateDeriv_add (axis : Fin 3) {first second : ScalarField}
    (first_smooth : ContDiff ℝ ∞ first) (second_smooth : ContDiff ℝ ∞ second) :
    coordinateDeriv axis (first + second) =
      coordinateDeriv axis first + coordinateDeriv axis second :=
  directionalDeriv_add _ (differentiable_of_contDiff first_smooth)
    (differentiable_of_contDiff second_smooth)

/-- Coordinate derivatives commute on smooth weights. -/
theorem coordinateDeriv_comm (smooth : ContDiff ℝ ∞ weight) (outer inner : Fin 3) :
    coordinateDeriv outer (coordinateDeriv inner weight) =
      coordinateDeriv inner (coordinateDeriv outer weight) :=
  directionalDeriv_comm smooth _ _

/-- Any axis together with its two successors exhausts the three axes, in
order.  This is the only `Fin 3` fact the identity below needs, and it is what
allows the generic statements to be proved in the index rather than three
times over. -/
theorem axisRotation (axis : Fin 3) :
    (axis = 0 ∧ axis + 1 = 1 ∧ axis + 2 = 2) ∨ (axis = 1 ∧ axis + 1 = 2 ∧ axis + 2 = 0)
      ∨ (axis = 2 ∧ axis + 1 = 0 ∧ axis + 2 = 1) := by
  revert axis
  decide

/-- The divergence, summed starting from any axis.  The sum ranges over all
three axes whichever axis it starts at, so this is a reindexing; stating it
generically is what removes the case split from the identity's proof. -/
theorem divergence_eq_from (field : VectorField) (axis : Fin 3) :
    divergence field = coordinateDeriv axis (component axis field)
      + coordinateDeriv (axis + 1) (component (axis + 1) field)
      + coordinateDeriv (axis + 2) (component (axis + 2) field) := by
  rcases axisRotation axis with ⟨here, next, last⟩ | ⟨here, next, last⟩ | ⟨here, next, last⟩ <;>
    rw [next, last, here] <;> simp only [divergence] <;> funext place <;>
      simp only [Pi.add_apply] <;> ring

/-- The scalar Laplacian, summed starting from any axis. -/
theorem scalarLaplacian_eq_from (weight : ScalarField) (axis : Fin 3) :
    scalarLaplacian weight = coordinateDeriv axis (coordinateDeriv axis weight)
      + coordinateDeriv (axis + 1) (coordinateDeriv (axis + 1) weight)
      + coordinateDeriv (axis + 2) (coordinateDeriv (axis + 2) weight) := by
  rcases axisRotation axis with ⟨here, next, last⟩ | ⟨here, next, last⟩ | ⟨here, next, last⟩ <;>
    rw [next, last, here] <;> simp only [scalarLaplacian] <;> funext place <;>
      simp only [Pi.add_apply] <;> ring

/-- Smoothness is inherited by the curl. -/
theorem contDiff_curl (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (curl field) :=
  contDiff_pi.2 fun _ =>
    (contDiff_coordinateDeriv _ (contDiff_component smooth _)).sub
      (contDiff_coordinateDeriv _ (contDiff_component smooth _))

/-- Smoothness is inherited by the divergence. -/
theorem contDiff_divergence (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (divergence field) :=
  ((contDiff_coordinateDeriv _ (contDiff_component smooth 0)).add
    (contDiff_coordinateDeriv _ (contDiff_component smooth 1))).add
    (contDiff_coordinateDeriv _ (contDiff_component smooth 2))

/-- Smoothness is inherited by the gradient. -/
theorem contDiff_gradient (smooth : ContDiff ℝ ∞ weight) : ContDiff ℝ ∞ (gradient weight) :=
  contDiff_pi.2 fun index => contDiff_coordinateDeriv index smooth

/-- Smoothness is inherited by the scalar Laplacian. -/
theorem contDiff_scalarLaplacian (smooth : ContDiff ℝ ∞ weight) :
    ContDiff ℝ ∞ (scalarLaplacian weight) :=
  ((contDiff_coordinateDeriv _ (contDiff_coordinateDeriv 0 smooth)).add
    (contDiff_coordinateDeriv _ (contDiff_coordinateDeriv 1 smooth))).add
    (contDiff_coordinateDeriv _ (contDiff_coordinateDeriv 2 smooth))

/-- Smoothness is inherited by the vector Laplacian. -/
theorem contDiff_laplacian (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (laplacian field) :=
  contDiff_pi.2 fun index => contDiff_scalarLaplacian (contDiff_component smooth index)

/-- The `index + 2` component of a curl, rewritten so that its two derivatives
are taken along `index` and `index + 1`.  Pure `Fin 3` bookkeeping. -/
theorem component_curl_shift_two (field : VectorField) (index : Fin 3) :
    component (index + 2) (curl field) =
      coordinateDeriv index (component (index + 1) field)
        - coordinateDeriv (index + 1) (component index field) := by
  have first : index + 2 + 1 = index := by fin_cases index <;> rfl
  have second : index + 2 + 2 = index + 1 := by fin_cases index <;> rfl
  show curlComponent (index + 2 + 1) (index + 2 + 2) field = _
  rw [first, second, curlComponent]

/-- The `index + 1` component of a curl, rewritten the same way. -/
theorem component_curl_shift_one (field : VectorField) (index : Fin 3) :
    component (index + 1) (curl field) =
      coordinateDeriv (index + 2) (component index field)
        - coordinateDeriv index (component (index + 2) field) := by
  have first : index + 1 + 1 = index + 2 := by fin_cases index <;> rfl
  have second : index + 1 + 2 = index := by fin_cases index <;> rfl
  show curlComponent (index + 1 + 1) (index + 1 + 2) field = _
  rw [first, second, curlComponent]

/-- One component of the double curl, fully expanded into second derivatives.
Every derivative here is taken of a component of the original field. -/
theorem component_curl_curl (smooth : ContDiff ℝ ∞ field) (index : Fin 3) :
    component index (curl (curl field)) =
      (coordinateDeriv (index + 1) (coordinateDeriv index (component (index + 1) field))
        - coordinateDeriv (index + 1)
            (coordinateDeriv (index + 1) (component index field)))
      - (coordinateDeriv (index + 2) (coordinateDeriv (index + 2) (component index field))
        - coordinateDeriv (index + 2)
            (coordinateDeriv index (component (index + 2) field))) := by
  show curlComponent (index + 1) (index + 2) (curl field) = _
  rw [curlComponent, component_curl_shift_two field index, component_curl_shift_one field index,
    coordinateDeriv_sub _ (contDiff_coordinateDeriv _ (contDiff_component smooth _))
      (contDiff_coordinateDeriv _ (contDiff_component smooth _)),
    coordinateDeriv_sub _ (contDiff_coordinateDeriv _ (contDiff_component smooth _))
      (contDiff_coordinateDeriv _ (contDiff_component smooth _))]

/-- **The vector identity**, concretely:
`curl (curl v) = grad (div v) - Δ v`, that is `-Δ v = curl (curl v) - grad (div v)`.

The proof is the same computation in every component, done once in the index:
expand both curls, expand the divergence and the Laplacian starting from the
same axis, and commute the two mixed second derivatives.  The two pure second
derivatives `∂ᵢ∂ᵢ vᵢ` cancel between the gradient of the divergence and the
Laplacian, which is why the identity has no zeroth-order terms. -/
theorem curl_curl (smooth : ContDiff ℝ ∞ field) :
    curl (curl field) = gradient (divergence field) - laplacian field := by
  funext place index
  have doubleCurl := congrFun (component_curl_curl smooth index) place
  have divergenceExpansion :
      coordinateDeriv index (divergence field) =
        coordinateDeriv index (coordinateDeriv index (component index field))
          + coordinateDeriv index (coordinateDeriv (index + 1) (component (index + 1) field))
          + coordinateDeriv index (coordinateDeriv (index + 2) (component (index + 2) field)) := by
    have hereSmooth : ContDiff ℝ ∞ (coordinateDeriv index (component index field)) :=
      contDiff_coordinateDeriv _ (contDiff_component smooth index)
    have nextSmooth : ContDiff ℝ ∞ (coordinateDeriv (index + 1) (component (index + 1) field)) :=
      contDiff_coordinateDeriv _ (contDiff_component smooth (index + 1))
    have lastSmooth : ContDiff ℝ ∞ (coordinateDeriv (index + 2) (component (index + 2) field)) :=
      contDiff_coordinateDeriv _ (contDiff_component smooth (index + 2))
    have pairSmooth : ContDiff ℝ ∞ (coordinateDeriv index (component index field)
        + coordinateDeriv (index + 1) (component (index + 1) field)) := hereSmooth.add nextSmooth
    rw [divergence_eq_from field index, coordinateDeriv_add _ pairSmooth lastSmooth,
      coordinateDeriv_add _ hereSmooth nextSmooth]
  have laplacianExpansion := congrFun (scalarLaplacian_eq_from (component index field) index) place
  have mixedFirst := congrFun
    (coordinateDeriv_comm (contDiff_component smooth (index + 1)) (index + 1) index) place
  have mixedSecond := congrFun
    (coordinateDeriv_comm (contDiff_component smooth (index + 2)) (index + 2) index) place
  have divergenceApplied := congrFun divergenceExpansion place
  show curl (curl field) place index = _
  have goalLeft : curl (curl field) place index = component index (curl (curl field)) place := rfl
  rw [goalLeft, doubleCurl]
  show _ = coordinateDeriv index (divergence field) place - scalarLaplacian
    (component index field) place
  rw [divergenceApplied, laplacianExpansion]
  simp only [Pi.add_apply, Pi.sub_apply] at *
  rw [mixedFirst, mixedSecond]
  ring

/-- `div ∘ grad = Δ` on scalar weights: the two second-order operators agree by
construction.  This pins down the relative normalization of `divergence`,
`gradient` and `scalarLaplacian`, so the vector identity above cannot be an
artefact of a mismatched convention. -/
theorem divergence_gradient (weight : ScalarField) :
    divergence (gradient weight) = scalarLaplacian weight := rfl

/-- `curl ∘ grad = 0` on smooth weights: a gradient carries no rotational
datum.  Like the identity itself this is exactly the commutation of two
coordinate derivatives, and it certifies that the cyclic definition of `curl`
is the classical one rather than a degenerate combination. -/
theorem curl_gradient (smooth : ContDiff ℝ ∞ weight) : curl (gradient weight) = 0 := by
  funext place index
  have componentGradient : ∀ axis : Fin 3,
      component axis (gradient weight) = coordinateDeriv axis weight := fun _ => rfl
  show curlComponent (index + 1) (index + 2) (gradient weight) place = 0
  rw [curlComponent, componentGradient, componentGradient,
    coordinateDeriv_comm smooth (index + 1) (index + 2)]
  simp

end Concrete

/-! ## The concrete calculus as an instance of the abstract one

The abstract structure asks for operators on a group of fields; the identity
only holds for smooth fields, so the group is the submodule of smooth fields
rather than all fields.  Assembling this is what certifies that the abstract
layer is about something. -/

/-- The smooth vector fields, as a submodule. -/
noncomputable def smoothVectorFields : Submodule ℝ VectorField where
  carrier := {field | ContDiff ℝ ∞ field}
  add_mem' := by
    intro first second first_smooth second_smooth
    simp only [Set.mem_setOf_eq] at first_smooth second_smooth ⊢
    exact first_smooth.add second_smooth
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact contDiff_const
  smul_mem' := by
    intro scalar _ smooth
    simp only [Set.mem_setOf_eq] at smooth ⊢
    exact smooth.const_smul scalar

/-- The smooth scalar weights, as a submodule. -/
noncomputable def smoothScalarFields : Submodule ℝ ScalarField where
  carrier := {weight | ContDiff ℝ ∞ weight}
  add_mem' := by
    intro first second first_smooth second_smooth
    simp only [Set.mem_setOf_eq] at first_smooth second_smooth ⊢
    exact first_smooth.add second_smooth
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact contDiff_const
  smul_mem' := by
    intro scalar _ smooth
    simp only [Set.mem_setOf_eq] at smooth ⊢
    exact smooth.const_smul scalar

@[simp] theorem mem_smoothVectorFields {field : VectorField} :
    field ∈ smoothVectorFields ↔ ContDiff ℝ ∞ field := Iff.rfl

@[simp] theorem mem_smoothScalarFields {weight : ScalarField} :
    weight ∈ smoothScalarFields ↔ ContDiff ℝ ∞ weight := Iff.rfl

/-- The rotational operator annihilates the zero field. -/
@[simp] theorem curl_zero_field : curl (0 : VectorField) = 0 := by
  funext place index
  have componentZero : ∀ axis : Fin 3, component axis (0 : VectorField) = 0 := by
    intro axis; funext point; rfl
  show curlComponent (index + 1) (index + 2) (0 : VectorField) place = 0
  rw [curlComponent, componentZero, componentZero]
  simp [coordinateDeriv]

/-- The gradient annihilates the zero weight. -/
@[simp] theorem gradient_zero_weight : gradient (0 : ScalarField) = 0 := by
  funext place index
  simp [gradient, coordinateDeriv]

/-- **The concrete div–curl calculus.**  The coordinate operators on smooth
three-dimensional fields realize the abstract structure, so every consequence
of `curl_curl_eq` applies to them. -/
noncomputable def smoothCalculus : CurlDivergenceCalculus smoothVectorFields smoothScalarFields where
  curl field := ⟨curl field.1, contDiff_curl field.2⟩
  divergence field := ⟨divergence field.1, contDiff_divergence field.2⟩
  gradient weight := ⟨gradient weight.1, contDiff_gradient weight.2⟩
  laplacian field := ⟨laplacian field.1, contDiff_laplacian field.2⟩
  curl_curl_eq field := Subtype.ext (curl_curl field.2)
  curl_zero := Subtype.ext (by simp)
  gradient_zero := Subtype.ext (by simp)

/-! ## The kernel of both first-order operators

For the recovery problem the relevant structure is Hilbertian, and the only
property of the operators that is used is continuity.  So the statements below
take an abstract Hilbert state space together with continuous divergence and
curl operators into arbitrary normed target spaces — in the analytic
realization the targets are negative-order spaces and continuity is the
standard duality bound. -/

section HarmonicKernel

variable {State DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]
  (divergence : State →L[ℝ] DivergenceValue) (curl : State →L[ℝ] CurlValue)

/-- The states annihilated by both first-order operators: `div h = 0` and
`curl h = 0`.  These are exactly the states invisible to a div–curl recovery,
so the recovered state is only determined modulo this subspace. -/
def harmonicKernel : Submodule ℝ State :=
  LinearMap.ker (divergence : State →ₗ[ℝ] DivergenceValue)
    ⊓ LinearMap.ker (curl : State →ₗ[ℝ] CurlValue)

variable {divergence curl}

@[simp] theorem mem_harmonicKernel {state : State} :
    state ∈ harmonicKernel divergence curl ↔ divergence state = 0 ∧ curl state = 0 := Iff.rfl

/-- The divergence vanishes on the kernel. -/
theorem divergence_eq_zero_of_mem {state : State} (mem : state ∈ harmonicKernel divergence curl) :
    divergence state = 0 := mem.1

/-- The curl vanishes on the kernel. -/
theorem curl_eq_zero_of_mem {state : State} (mem : state ∈ harmonicKernel divergence curl) :
    curl state = 0 := mem.2

/-- **Uniqueness of the normalized representative.**  Two states with the same
divergence and the same curl, both orthogonal to the kernel, are equal: their
difference lies in the kernel and in its orthogonal complement at once.

This is the precise sense in which a rotational datum determines a state: not
outright, but after the kernel has been normalized away. -/
theorem eq_of_orthogonal_of_curl_eq {first second : State}
    (first_orthogonal : first ∈ (harmonicKernel divergence curl)ᗮ)
    (second_orthogonal : second ∈ (harmonicKernel divergence curl)ᗮ)
    (same_divergence : divergence first = divergence second)
    (same_curl : curl first = curl second) : first = second := by
  have difference_kernel : first - second ∈ harmonicKernel divergence curl := by
    refine ⟨?_, ?_⟩ <;> simp [LinearMap.mem_ker, map_sub, same_divergence, same_curl]
  have difference_orthogonal : first - second ∈ (harmonicKernel divergence curl)ᗮ :=
    Submodule.sub_mem _ first_orthogonal second_orthogonal
  have vanishes : first - second ∈ (⊥ : Submodule ℝ State) := by
    rw [← Submodule.inf_orthogonal_eq_bot (harmonicKernel divergence curl)]
    exact ⟨difference_kernel, difference_orthogonal⟩
  exact sub_eq_zero.1 (Submodule.mem_bot ℝ |>.1 vanishes)

variable (divergence curl)

/-- **The kernel is closed.**  Both conditions defining it are kernels of
continuous linear maps, hence preserved under limits; the intersection of two
closed sets is closed.

This is the entire analytic content of the projection statement: it is
continuity of the first-order operators into their (negative-order) targets
that lets the two vanishing conditions pass to limits. -/
theorem isClosed_harmonicKernel :
    IsClosed (harmonicKernel divergence curl : Set State) := by
  have kernels : (harmonicKernel divergence curl : Set State) =
      (LinearMap.ker (divergence : State →ₗ[ℝ] DivergenceValue) : Set State) ∩
        (LinearMap.ker (curl : State →ₗ[ℝ] CurlValue) : Set State) := rfl
  rw [kernels]
  exact (divergence.isClosed_ker).inter (curl.isClosed_ker)

variable [CompleteSpace State]

/-- A closed subspace of a complete space is complete. -/
instance completeSpace_harmonicKernel :
    CompleteSpace (harmonicKernel divergence curl) :=
  (isClosed_harmonicKernel divergence curl).completeSpace_coe

/-- **The Hilbert projection theorem applies**: because the kernel is closed
in a complete inner product space, the orthogonal projection onto it exists as
a bounded operator.  This is what makes the normalization below well defined. -/
instance hasOrthogonalProjection_harmonicKernel :
    (harmonicKernel divergence curl).HasOrthogonalProjection :=
  inferInstance

/-- The normalized state: the part of a state orthogonal to the kernel.  This
is the representative that a div–curl recovery returns. -/
noncomputable def harmonicComplement (state : State) : State :=
  state - (harmonicKernel divergence curl).starProjection state

variable {divergence curl}

/-- The normalized state is orthogonal to the kernel — the normalization
condition itself. -/
theorem harmonicComplement_mem_orthogonal (state : State) :
    harmonicComplement divergence curl state ∈ (harmonicKernel divergence curl)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal state

/-- Normalizing does not change the divergence: the discarded part has none. -/
theorem divergence_harmonicComplement (state : State) :
    divergence (harmonicComplement divergence curl state) = divergence state := by
  have discarded : divergence ((harmonicKernel divergence curl).starProjection state) = 0 :=
    divergence_eq_zero_of_mem (Submodule.starProjection_apply_mem _ state)
  simp [harmonicComplement, map_sub, discarded]

/-- Normalizing does not change the curl: the discarded part has none.  This is
what makes the normalization compatible with the recovery problem — the
rotational datum is untouched. -/
theorem curl_harmonicComplement (state : State) :
    curl (harmonicComplement divergence curl state) = curl state := by
  have discarded : curl ((harmonicKernel divergence curl).starProjection state) = 0 :=
    curl_eq_zero_of_mem (Submodule.starProjection_apply_mem _ state)
  simp [harmonicComplement, map_sub, discarded]

/-- **The recovery is exactly the normalization.**  Any state orthogonal to the
kernel with the prescribed divergence and curl is the normalization of any
state carrying that same data.  Existence is the projection; uniqueness is the
theorem above. -/
theorem eq_harmonicComplement_of_orthogonal {state candidate : State}
    (candidate_orthogonal : candidate ∈ (harmonicKernel divergence curl)ᗮ)
    (same_divergence : divergence candidate = divergence state)
    (same_curl : curl candidate = curl state) :
    candidate = harmonicComplement divergence curl state :=
  eq_of_orthogonal_of_curl_eq candidate_orthogonal (harmonicComplement_mem_orthogonal state)
    (by rw [same_divergence, divergence_harmonicComplement])
    (by rw [same_curl, curl_harmonicComplement])

/-- The normalization is idempotent on already-normalized states. -/
theorem harmonicComplement_of_mem_orthogonal {state : State}
    (orthogonal : state ∈ (harmonicKernel divergence curl)ᗮ) :
    harmonicComplement divergence curl state = state :=
  (eq_harmonicComplement_of_orthogonal orthogonal rfl rfl).symm

end HarmonicKernel

/-! ## The local normalization on a window

The section above works inside a single Hilbert space with two continuous
first-order operators.  This section says how a space of states equipped with a
`CurlDivergenceCalculus` is *realized* in such a Hilbert space: a restriction
map onto the `L²` of a window, together with the divergence and the curl read on
that window.

That realization is what turns the algebraic splitting of a state into the local
Helmholtz/Hodge decomposition

> `u = u^⊥ + h`,   `u^⊥ = (1 - proj_𝓗)u`,   `h = proj_𝓗 u`,

and it is why the material belongs here rather than in any application.  On the
window's own `L²` the harmonic kernel `𝓗` is the intersection of the kernels of
two *continuous* maps, hence closed (`isClosed_harmonicKernel`), hence — the
window's `L²` being complete — the target of an orthogonal projection
(`hasOrthogonalProjection_harmonicKernel`).  So the decomposition is a
**construction**, not a hypothesis: `harmonicComplement` builds it, and the
properties that an application would otherwise have to assume about it
(orthogonality of the quotient part, vanishing of the curl on the harmonic part,
preservation of the divergence) are theorems below.

Everything here is parametric in the state space, the window's `L²`, and the two
operator targets.  No dimension, no domain, and no particular equation enters.
-/

/--
**The `L²(window)` realization of a state space.**

The data that turns the algebraic decomposition of a local residual into an
*orthogonal* one: the local Hilbert space of a window, the restriction of a
state to it, and the two first-order operators on it whose common kernel is the
window's harmonic kernel.

The operators are continuous linear maps, and continuity is the entire analytic
content of the projection: it is what makes the harmonic kernel closed
(`isClosed_harmonicKernel`) and hence the orthogonal projection onto it exist.
-/
structure LocalNormalization {Field ScalarField : Type*} [AddCommGroup Field]
    [Zero ScalarField] (calculus : CurlDivergenceCalculus Field ScalarField)
    (Slice DivergenceValue CurlValue : Type*)
    [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
    [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
    [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue] where
  /-- Restriction of a state to the window, landing in its `L²`. -/
  restrict : Field → Slice
  /-- The divergence on the window, continuous into a negative-order space. -/
  sliceDivergence : Slice →L[ℝ] DivergenceValue
  /-- The curl on the window, continuous into a negative-order space. -/
  sliceCurl : Slice →L[ℝ] CurlValue
  /-- Restricting a divergence-free state to the window leaves it
  divergence-free: restriction does not create divergence. -/
  restrict_divergence : ∀ field, calculus.divergence field = 0 →
    sliceDivergence (restrict field) = 0
  /-- Restricting a curl-free state to the window leaves it curl-free. -/
  restrict_curl : ∀ field, calculus.curl field = 0 → sliceCurl (restrict field) = 0

namespace LocalNormalization

variable {Field ScalarField : Type*} [AddCommGroup Field] [Zero ScalarField]
  {calculus : CurlDivergenceCalculus Field ScalarField}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]
  (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue)

/--
**The normalization condition**: the restricted state is orthogonal to the
window's harmonic kernel, which is the defining property of the quotient
representative `u^⊥ = (1 - proj_𝓗)u`.

This is a condition on the restriction of a state to its own window, stated
against the window's own `L²`.  Nothing global enters.
-/
def Normalized (field : Field) : Prop :=
  normalization.restrict field ∈
    (harmonicKernel normalization.sliceDivergence normalization.sliceCurl)ᗮ

/--
**The rotational datum determines the normalized representative.**

Two normalized states carrying the same divergence and the same curl on the
window restrict to the same element of the window's `L²`.  The proof is
`eq_of_orthogonal_of_curl_eq` verbatim: the difference lies in the kernel and in
its orthogonal complement at once, and a Hilbert space has no such nonzero
vector.
-/
theorem restrict_eq_of_normalized {first second : Field}
    (first_normalized : normalization.Normalized first)
    (second_normalized : normalization.Normalized second)
    (same_divergence : normalization.sliceDivergence (normalization.restrict first) =
      normalization.sliceDivergence (normalization.restrict second))
    (same_curl : normalization.sliceCurl (normalization.restrict first) =
      normalization.sliceCurl (normalization.restrict second)) :
    normalization.restrict first = normalization.restrict second :=
  eq_of_orthogonal_of_curl_eq first_normalized second_normalized same_divergence same_curl

/--
**A normalized state invisible to the calculus restricts to zero.**

A normalized state which is itself divergence-free *and* curl-free lies in the
window's harmonic kernel; being also orthogonal to it, it restricts to `0`.
This is what excludes the apparent counterexamples to a div–curl recovery: a
state that is both divergence-free and curl-free is never a legal normalized
representative of anything nonzero on the window.

The proof is the uniqueness theorem above against the zero state, which is
trivially normalized and trivially carries no divergence and no curl.
-/
theorem restrict_eq_zero_of_normalized {field : Field}
    (normalized : normalization.Normalized field)
    (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0) :
    normalization.restrict field = 0 := by
  refine eq_of_orthogonal_of_curl_eq normalized (Submodule.zero_mem _) ?_ ?_
  · rw [normalization.restrict_divergence field divergence_free, map_zero]
  · rw [normalization.restrict_curl field curl_free, map_zero]

/--
**The contrapositive**: a divergence-free curl-free state that is nonzero on a
window is *not* a legal quotient representative on that window.
-/
theorem not_normalized_of_restrict_ne_zero {field : Field}
    (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0)
    (nonzero : normalization.restrict field ≠ 0) :
    ¬ normalization.Normalized field := fun normalized =>
  nonzero (normalization.restrict_eq_zero_of_normalized normalized divergence_free curl_free)

/-! ### The decomposition is constructed, not assumed

Everything above treats `Normalized` as a *condition* to be checked.  It need
not be: on the window's own `L²` the decomposition

> `u = u^⊥ + h`,   `u^⊥ = (1 - proj_𝓗)u`,   `h = proj_𝓗 u`

**exists**, because the harmonic kernel is the intersection of the kernels of
two *continuous* linear maps, hence closed (`isClosed_harmonicKernel`), hence —
the window's `L²` being complete — the target of an orthogonal projection
(`hasOrthogonalProjection_harmonicKernel`, the Hilbert projection theorem).
`harmonicComplement` is that construction, and the three properties that an
algebraic decomposition would take as *data* are its theorems:

| assumed as data | proved here | framework theorem |
| --- | --- | --- |
| `decomposition : u = u^⊥ + h` | `restrict_eq_quotientSlicePart_add_harmonicSlicePart` | definition of `harmonicComplement` |
| `harmonic_curl_free : curl h = 0` | `sliceCurl_harmonicSlicePart` | `curl_eq_zero_of_mem` |
| `quotient_divergence_free : div u^⊥ = 0` | `sliceDivergence_quotientSlicePart_eq_zero` | `divergence_harmonicComplement` |
| `Normalized u^⊥` | `quotientSlicePart_mem_orthogonal` | `harmonicComplement_mem_orthogonal` |

and the harmonic part carries no divergence either
(`sliceDivergence_harmonicSlicePart`), which the algebraic data never records.

**Where the construction lives, and why it stops there.**  `harmonicComplement`
is a map `Slice → Slice`.  So what is constructed is the decomposition of
`restrict field`, an element of the window's `L²` — not a decomposition of
`field`, an element of `Field`.  Transporting it back would need a right inverse
of `restrict` together with the *converse* of `restrict_curl`, and that converse
is false: `restrict_curl` says restriction does not create curl, while the
converse would say the window sees all of it.  A state supported away from the
window restricts to `0` and has arbitrary curl.  So on `Field` the three items
above remain hypotheses; what this section proves is that any state satisfying
them restricts to exactly the constructed object
(`restrict_eq_quotientSlicePart_of_decomposition`), so the assumed data is not an
extra degree of freedom — it is a description of something that already exists
and is unique.
-/

section Construction

variable [CompleteSpace Slice]

/--
**The harmonic part** `h = proj_𝓗 u`.

The orthogonal projection of the restricted state onto the local harmonic
kernel.  It exists because the kernel is closed and the window's `L²` is
complete; no choice and no hypothesis is involved beyond continuity of the two
first-order operators.
-/
noncomputable def harmonicSlicePart (field : Field) : Slice :=
  (harmonicKernel normalization.sliceDivergence normalization.sliceCurl).starProjection
    (normalization.restrict field)

/--
**The quotient part** `u^⊥ = (1 - proj_𝓗)u`.

This is `harmonicComplement` at the restricted state: the *constructed* quotient
representative, whose three defining properties are the theorems below.
-/
noncomputable def quotientSlicePart (field : Field) : Slice :=
  harmonicComplement normalization.sliceDivergence normalization.sliceCurl
    (normalization.restrict field)

/--
**The decomposition itself**, `u = u^⊥ + h` — proved, not assumed.  It is the
definition of `harmonicComplement` read forwards.
-/
theorem restrict_eq_quotientSlicePart_add_harmonicSlicePart (field : Field) :
    normalization.restrict field =
      normalization.quotientSlicePart field + normalization.harmonicSlicePart field := by
  simp [quotientSlicePart, harmonicSlicePart, harmonicComplement]

/-- The harmonic part is the difference, which is the same statement rearranged. -/
theorem harmonicSlicePart_eq_sub (field : Field) :
    normalization.harmonicSlicePart field =
      normalization.restrict field - normalization.quotientSlicePart field := by
  simp [quotientSlicePart, harmonicSlicePart, harmonicComplement]

/--
**The harmonic part carries no rotational datum**, `curl h = 0`.  This is the
hypothesis `harmonic_curl_free` of the theorems above, proved: the projection
lands in the kernel of the curl by construction.
-/
theorem sliceCurl_harmonicSlicePart (field : Field) :
    normalization.sliceCurl (normalization.harmonicSlicePart field) = 0 :=
  curl_eq_zero_of_mem (Submodule.starProjection_apply_mem _ _)

/--
**The harmonic part carries no divergence either**, `div h = 0`.  The algebraic
decomposition never records this — it is what makes the discarded component
harmonic rather than merely irrotational.
-/
theorem sliceDivergence_harmonicSlicePart (field : Field) :
    normalization.sliceDivergence (normalization.harmonicSlicePart field) = 0 :=
  divergence_eq_zero_of_mem (Submodule.starProjection_apply_mem _ _)

/-- **Normalizing does not change the rotational datum**, `curl u^⊥ = curl u`.
This is `curl_harmonicComplement`, and it is the identity the whole recovery
rests on. -/
theorem sliceCurl_quotientSlicePart (field : Field) :
    normalization.sliceCurl (normalization.quotientSlicePart field) =
      normalization.sliceCurl (normalization.restrict field) :=
  curl_harmonicComplement _

/-- **Normalizing does not change the divergence**, `div u^⊥ = div u`. -/
theorem sliceDivergence_quotientSlicePart (field : Field) :
    normalization.sliceDivergence (normalization.quotientSlicePart field) =
      normalization.sliceDivergence (normalization.restrict field) :=
  divergence_harmonicComplement _

/--
**The quotient part of a divergence-free state is divergence-free**,
`div u^⊥ = 0`.  This is the hypothesis `quotient_divergence_free` of the
theorems above, proved: normalizing does not change the divergence, and
restriction does not create one.
-/
theorem sliceDivergence_quotientSlicePart_eq_zero {field : Field}
    (divergence_free : calculus.divergence field = 0) :
    normalization.sliceDivergence (normalization.quotientSlicePart field) = 0 := by
  rw [normalization.sliceDivergence_quotientSlicePart,
    normalization.restrict_divergence field divergence_free]

/--
**The constructed quotient part is normalized**, `u^⊥ ⊥ 𝓗`.  This is
`Normalized` proved rather than imposed, by `harmonicComplement_mem_orthogonal`.
-/
theorem quotientSlicePart_mem_orthogonal (field : Field) :
    normalization.quotientSlicePart field ∈
      (harmonicKernel normalization.sliceDivergence normalization.sliceCurl)ᗮ :=
  harmonicComplement_mem_orthogonal _

/--
**`Normalized` is exactly "already equal to your own quotient part"**.

The forward direction is `eq_harmonicComplement_of_orthogonal` — the
normalization is idempotent — and the backward direction is the previous
theorem.  So the orthogonality condition is not an extra structure imposed on
the states: it names the fixed points of a construction that always exists.
-/
theorem normalized_iff_restrict_eq_quotientSlicePart (field : Field) :
    normalization.Normalized field ↔
      normalization.restrict field = normalization.quotientSlicePart field := by
  constructor
  · intro normalized
    exact eq_harmonicComplement_of_orthogonal normalized rfl rfl
  · intro restrict_eq
    show normalization.restrict field ∈ _
    rw [restrict_eq]
    exact normalization.quotientSlicePart_mem_orthogonal field

/--
**The constructed representative is the only one.**

A normalized state carrying the same divergence and the same curl as `field` on
the window restricts to the constructed quotient part of `field`.
-/
theorem restrict_eq_quotientSlicePart_of_normalized {field quotientField : Field}
    (normalized : normalization.Normalized quotientField)
    (same_divergence : normalization.sliceDivergence (normalization.restrict quotientField) =
      normalization.sliceDivergence (normalization.restrict field))
    (same_curl : normalization.sliceCurl (normalization.restrict quotientField) =
      normalization.sliceCurl (normalization.restrict field)) :
    normalization.restrict quotientField = normalization.quotientSlicePart field :=
  eq_harmonicComplement_of_orthogonal normalized same_divergence same_curl

/--
**An assumed decomposition is the constructed one.**

If a state is split as `u = u^⊥ + h` with `h` curl-free, with `u` and `u^⊥`
divergence-free, and with `u^⊥` normalized, then on the window `u^⊥` *is* the
constructed quotient part of `u`.  So carrying that data adds no freedom: it
describes an object that already exists and is unique.

Additivity of `restrict` is the one thing `LocalNormalization` does not carry —
it is a property of the realization, true for every `L²(window)` restriction —
so it is taken as an explicit argument rather than added to the structure, which
would change the statements of the theorems above.
-/
theorem restrict_eq_quotientSlicePart_of_decomposition
    (restrict_add : ∀ first second : Field,
      normalization.restrict (first + second) =
        normalization.restrict first + normalization.restrict second)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (harmonic_curl_free : calculus.curl harmonicField = 0)
    (divergence_free : calculus.divergence field = 0)
    (quotient_divergence_free : calculus.divergence quotientField = 0)
    (normalized : normalization.Normalized quotientField) :
    normalization.restrict quotientField = normalization.quotientSlicePart field := by
  have restrictSplit : normalization.restrict field =
      normalization.restrict quotientField + normalization.restrict harmonicField := by
    rw [decomposition, restrict_add]
  refine normalization.restrict_eq_quotientSlicePart_of_normalized normalized ?_ ?_
  · rw [normalization.restrict_divergence quotientField quotient_divergence_free,
      normalization.restrict_divergence field divergence_free]
  · rw [restrictSplit, map_add, normalization.restrict_curl harmonicField harmonic_curl_free,
      add_zero]

/-- The companion statement for the discarded component: an assumed harmonic
part restricts to the constructed one. -/
theorem restrict_eq_harmonicSlicePart_of_decomposition
    (restrict_add : ∀ first second : Field,
      normalization.restrict (first + second) =
        normalization.restrict first + normalization.restrict second)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (harmonic_curl_free : calculus.curl harmonicField = 0)
    (divergence_free : calculus.divergence field = 0)
    (quotient_divergence_free : calculus.divergence quotientField = 0)
    (normalized : normalization.Normalized quotientField) :
    normalization.restrict harmonicField = normalization.harmonicSlicePart field := by
  have restrictSplit : normalization.restrict field =
      normalization.restrict quotientField + normalization.restrict harmonicField := by
    rw [decomposition, restrict_add]
  have quotientEq := normalization.restrict_eq_quotientSlicePart_of_decomposition restrict_add
    decomposition harmonic_curl_free divergence_free quotient_divergence_free normalized
  rw [normalization.harmonicSlicePart_eq_sub, ← quotientEq, restrictSplit]
  abel

end Construction

end LocalNormalization

end Hypostructure.PDE.DivCurl
