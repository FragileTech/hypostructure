import Mathlib
import Hypostructure.PDE.Distribution.Local

/-!
# Taking the curl to eliminate the pressure

The classical Stokes argument opens with a step that is usually written in
three lines:

> Apply `curl` to `∂_t u - Δu + ∇p = f`.  Constant-coefficient differentiation
> commutes with `∂_t` and `Δ`, and `curl ∇p = 0`.  Hence `ω = curl u` satisfies
> `(∂_t - Δ)ω = curl f`.

Those three lines mix two entirely different kinds of content, and this module
separates them.

* **The algebra.**  `vorticity_of_balance` is the whole argument.  It takes an
  *additive* operator `curl`, together with the three structural facts that
  `curl` annihilates gradients and intertwines the time derivative and the
  Laplacian, and reads the equation.  It knows nothing about dimension three,
  about Stokes, about distributions, or even about derivatives: the hypotheses
  are the definition of what it means to be a curl, and the conclusion is the
  vorticity equation.  Any model that can supply those three facts gets the
  pressure eliminated for free.

* **The symmetry.**  The three facts are not analytic content --- no estimate,
  no regularity, no boundary condition is involved.  Every one of them is
  Clairaut's theorem: mixed partial derivatives commute.  The second half of
  this module proves exactly that, once, for distributions
  (`derivativeCLM_comm`), and then hands the concrete three-dimensional curl
  its three facts (`curl_gradientField`, `curl_derivativeCLM`,
  `curl_laplaceTypeCLM`).

The concrete layer is still deliberately unattached to a problem.  The ambient
space is any real normed space --- in the parabolic application it is
`ℝ × Space`, so that `∂_t` and the spatial derivatives are *the same* operator
`derivativeCLM` applied to different directions, which is precisely why a
single commutation lemma discharges all three hypotheses.  The three curl
directions are an arbitrary family `Fin 3 → Point`, and the Laplacian is any
`laplaceTypeCLM`, over any finite family of directions, not necessarily the
ones the curl uses.
-/

namespace Hypostructure.PDE.Vorticity

open TopologicalSpace
open scoped Distributions

universe uPoint uIndex

/-! ## The algebraic layer

The vorticity equation is a consequence of three closure properties of `curl`
and nothing else.  Only `curl` itself is required to be additive: the time
derivative, the Laplacian and the gradient enter the argument only through
their images under `curl`, so they may be arbitrary functions.  The pressure
lives in an unconstrained type, since the only thing the argument ever does
with it is feed it to `gradient` and watch the result be annihilated.
-/

section Abstract

variable {VectorField ScalarField Vorticity : Type*}
  [AddCommGroup VectorField] [AddCommGroup Vorticity]

/--
**The vorticity equation.**

If a velocity, a pressure and a forcing satisfy the balance
`∂_t u - Δu + ∇p = f`, and `curl` is an additive operator that annihilates
gradients and intertwines the time derivative and the Laplacian with their
counterparts on vorticities, then the vorticity `curl u` satisfies
`(∂_t - Δ)(curl u) = curl f`.

The pressure has disappeared.  That is the entire point of the step: the
unknown that is *not* determined by an evolution equation is removed from the
system, and what remains is a heat equation for the vorticity with a known
right-hand side.

The three hypotheses are structural rather than analytic.  A model supplies
them definitionally --- for the concrete curl of this file they are all
instances of the symmetry of second derivatives --- and never has to supply an
estimate to use this theorem.
-/
theorem vorticity_of_balance
    (curl : VectorField →+ Vorticity)
    {gradient : ScalarField → VectorField}
    {timeDeriv laplacian : VectorField → VectorField}
    {vorticityTimeDeriv vorticityLaplacian : Vorticity → Vorticity}
    (curl_gradient : ∀ pressure, curl (gradient pressure) = 0)
    (curl_timeDeriv : ∀ field,
      curl (timeDeriv field) = vorticityTimeDeriv (curl field))
    (curl_laplacian : ∀ field,
      curl (laplacian field) = vorticityLaplacian (curl field))
    {velocity : VectorField} {pressure : ScalarField} {forcing : VectorField}
    (equation :
      timeDeriv velocity - laplacian velocity + gradient pressure = forcing) :
    vorticityTimeDeriv (curl velocity) - vorticityLaplacian (curl velocity) =
      curl forcing := by
  rw [← equation, map_add, map_sub, curl_gradient, curl_timeDeriv,
    curl_laplacian, add_zero]

end Abstract

/-! ## Clairaut's theorem for line derivatives

Everything the concrete layer needs is the commutation of two directional
derivatives, and that is the symmetry of the second Fréchet derivative read
through the identification `lineDeriv = fderiv ∘ evaluation`.
-/

section Symmetry

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]

/--
Two line derivatives of a twice continuously differentiable function commute.

Mathlib states the symmetry of the second derivative for `fderiv`; this is the
same statement in the `lineDeriv` form that the test-function and distribution
API uses.  The translation is in two steps: a line derivative of a
differentiable function is its Fréchet derivative evaluated at the direction,
and differentiating an evaluation is evaluating the differential, which is
`HasFDerivAt.clm_apply` against a constant.
-/
theorem lineDeriv_lineDeriv_comm {weight : Point → ℝ}
    (smooth : ContDiff ℝ (2 : ℕ) weight) (place first second : Point) :
    lineDeriv ℝ (fun other => lineDeriv ℝ weight other second) place first =
      lineDeriv ℝ (fun other => lineDeriv ℝ weight other first) place second := by
  have differentiable : Differentiable ℝ weight := smooth.differentiable (by norm_num)
  have rewriteLine : ∀ direction : Point,
      (fun other => lineDeriv ℝ weight other direction) =
        fun other => fderiv ℝ weight other direction := by
    intro direction
    funext other
    exact (differentiable other).lineDeriv_eq_fderiv
  have secondSmooth : ContDiff ℝ (1 : ℕ) (fderiv ℝ weight) := by
    apply smooth.fderiv_right
    norm_num
  have secondDeriv : HasFDerivAt (fderiv ℝ weight)
      (fderiv ℝ (fderiv ℝ weight) place) place :=
    (secondSmooth.differentiable (by norm_num) place).hasFDerivAt
  have evaluate : ∀ direction : Point,
      lineDeriv ℝ (fun other => fderiv ℝ weight other direction) place =
        fun other => fderiv ℝ (fderiv ℝ weight) place other direction := by
    intro direction
    funext other
    have applied :
        HasFDerivAt (fun candidate => (fderiv ℝ weight candidate) direction)
          ((fderiv ℝ weight place).comp 0 +
            (fderiv ℝ (fderiv ℝ weight) place).flip direction) place :=
      secondDeriv.clm_apply (hasFDerivAt_const direction place)
    simpa using (applied.hasLineDerivAt other).lineDeriv
  rw [rewriteLine second, rewriteLine first,
    congrFun (evaluate second) first, congrFun (evaluate first) second]
  exact (smooth.contDiffAt.isSymmSndFDerivAt (by norm_num)) first second

end Symmetry

/-! ## Commuting derivatives of a distribution

A distributional derivative is defined by moving the derivative onto the test
function, at the cost of a sign.  Two of them therefore cost two signs, which
cancel, so the commutation of distributional derivatives is *exactly* the
commutation of test-function derivatives, with no analytic hypothesis
whatsoever: a test function is smooth by construction.
-/

section DistributionSymmetry

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {domain : Opens Point}

/-- Test functions are smooth, so their line derivatives commute. -/
theorem testFunction_lineDerivCLM_comm (first second : Point) (test : 𝓓(domain, ℝ)) :
    (TestFunction.lineDerivCLM ℝ first
        (TestFunction.lineDerivCLM ℝ second test : 𝓓(domain, ℝ)) : 𝓓(domain, ℝ)) =
      TestFunction.lineDerivCLM ℝ second
        (TestFunction.lineDerivCLM ℝ first test : 𝓓(domain, ℝ)) := by
  have smoothness : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have smooth : ContDiff ℝ (2 : ℕ) (test : Point → ℝ) := by
    refine test.contDiff.of_le ?_
    simpa using smoothness
  have coe_line : ∀ direction : Point,
      ((TestFunction.lineDerivCLM ℝ direction test : 𝓓(domain, ℝ)) : Point → ℝ) =
        fun other => lineDeriv ℝ (test : Point → ℝ) other direction := by
    intro direction
    funext other
    exact TestFunction.lineDerivCLM_apply_of_le le_top
  refine DFunLike.ext _ _ fun place => ?_
  rw [TestFunction.lineDerivCLM_apply_of_le le_top,
    TestFunction.lineDerivCLM_apply_of_le le_top, coe_line, coe_line]
  exact lineDeriv_lineDeriv_comm smooth place first second

/--
The distributional derivative along `direction`, as an operator on the
distributions of a fixed domain.

This is `Distribution.lineDerivCLM` with its two order parameters pinned to
`⊤`, which is the only case this module uses.  Pinning them is not cosmetic:
`lineDerivCLM` maps order-`k` distributions to order-`n` ones, so without the
ascription no iterated expression has an inferrable type.
-/
noncomputable def derivativeCLM (domain : Opens Point) (direction : Point) :
    Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤ :=
  Distribution.lineDerivCLM direction

theorem derivativeCLM_eq_lineDerivCLM (domain : Opens Point) (direction : Point) :
    derivativeCLM domain direction =
      (Distribution.lineDerivCLM direction :
        Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤) :=
  rfl

/--
**Distributional derivatives commute.**

The two minus signs of the duality definition cancel, leaving the commutation
of two derivatives of a test function, which is Clairaut's theorem.  This is
the single fact from which all three hypotheses of `vorticity_of_balance` are
obtained below.
-/
theorem derivativeCLM_comm (first second : Point) (value : Distribution domain ℝ ⊤) :
    derivativeCLM domain first (derivativeCLM domain second value) =
      derivativeCLM domain second (derivativeCLM domain first value) := by
  ext test
  show -(-(value _)) = -(-(value _))
  exact congrArg (fun moved => -(-(value moved)))
    (testFunction_lineDerivCLM_comm second first test)

/--
A Laplace-type operator commutes with every directional derivative.

It is a finite sum of doubled directional derivatives, so this is
`derivativeCLM_comm` applied twice inside a sum.  Note that the directions of
the Laplacian are unrelated to the direction being commuted past it: in the
parabolic application the latter is the *time* direction, and the argument is
the same.
-/
theorem laplaceTypeCLM_derivativeCLM_comm {Index : Type uIndex} [Fintype Index]
    (directions : Index → Point) (direction : Point)
    (value : Distribution domain ℝ ⊤) :
    Distribution.laplaceTypeCLM domain directions
        (derivativeCLM domain direction value) =
      derivativeCLM domain direction
        (Distribution.laplaceTypeCLM domain directions value) := by
  simp only [Distribution.laplaceTypeCLM, sum_apply,
    ContinuousLinearMap.comp_apply, ← derivativeCLM_eq_lineDerivCLM, map_sum]
  refine Finset.sum_congr rfl fun index _ => ?_
  rw [derivativeCLM_comm (directions index) direction,
    derivativeCLM_comm (directions index) direction]

end DistributionSymmetry

/-! ## The concrete three-dimensional curl

The only place in the file where the number three appears.  The curl is the
antisymmetric combination of derivatives along a family of three directions,
indexed cyclically by `Fin 3`, and the gradient is the family of derivatives
along the same three directions.  Nothing else about them is assumed: they
need not be orthonormal, and the ambient space need not be three-dimensional
--- in the parabolic application it is `ℝ × Space`, with the three directions
spatial and a fourth, time direction handled by the same `derivativeCLM`.
-/

section Curl

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {domain : Opens Point} {directions : Fin 3 → Point}

/-- The `index`-th component of the curl: `(curl u)_i = ∂_{i+1} u_{i+2} -
∂_{i+2} u_{i+1}`, with the indices read cyclically in `Fin 3`. -/
noncomputable def curlComponent (domain : Opens Point) (directions : Fin 3 → Point)
    (field : Fin 3 → Distribution domain ℝ ⊤) (index : Fin 3) :
    Distribution domain ℝ ⊤ :=
  derivativeCLM domain (directions (index + 1)) (field (index + 2)) -
    derivativeCLM domain (directions (index + 2)) (field (index + 1))

/-- The curl of a three-component field of distributions, bundled with its
additivity --- the only algebraic property `vorticity_of_balance` asks for. -/
noncomputable def curl (domain : Opens Point) (directions : Fin 3 → Point) :
    (Fin 3 → Distribution domain ℝ ⊤) →+ (Fin 3 → Distribution domain ℝ ⊤) :=
  AddMonoidHom.mk' (curlComponent domain directions) <| by
    intro first second
    funext index
    simp only [curlComponent, Pi.add_apply, map_add]
    abel

@[simp] theorem curl_apply (field : Fin 3 → Distribution domain ℝ ⊤) (index : Fin 3) :
    curl domain directions field index =
      derivativeCLM domain (directions (index + 1)) (field (index + 2)) -
        derivativeCLM domain (directions (index + 2)) (field (index + 1)) :=
  rfl

/-- The gradient of a scalar distribution along the same three directions. -/
noncomputable def gradientField (domain : Opens Point) (directions : Fin 3 → Point)
    (pressure : Distribution domain ℝ ⊤) : Fin 3 → Distribution domain ℝ ⊤ :=
  fun index => derivativeCLM domain (directions index) pressure

/--
**`curl ∘ grad = 0`.**

The first hypothesis of `vorticity_of_balance`.  Each component is a
difference of the two orders of the same pair of derivatives, so it vanishes
by `derivativeCLM_comm`.  This is the step that eliminates the pressure.
-/
theorem curl_gradientField (pressure : Distribution domain ℝ ⊤) :
    curl domain directions (gradientField domain directions pressure) = 0 := by
  funext index
  simp only [curl_apply, gradientField, Pi.zero_apply]
  rw [derivativeCLM_comm]
  exact sub_self _

/-- An operator on scalar distributions applied to each component of a field.
Both the time derivative and the Laplacian of a vector field are of this
shape, which is why one lemma discharges both remaining hypotheses. -/
noncomputable def componentwise
    (operator : Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤)
    (field : Fin 3 → Distribution domain ℝ ⊤) : Fin 3 → Distribution domain ℝ ⊤ :=
  fun index => operator (field index)

/--
The curl commutes with any operator that is applied componentwise and itself
commutes with the three directional derivatives.

Both remaining hypotheses of `vorticity_of_balance` are instances of this: the
time derivative and the Laplacian both act one component at a time, and both
commute with derivatives.  Additivity of the operator is what lets it pass
through the difference defining a component of the curl.
-/
theorem curl_componentwise
    (operator : Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤)
    (commutes : ∀ (direction : Point) (value : Distribution domain ℝ ⊤),
      operator (derivativeCLM domain direction value) =
        derivativeCLM domain direction (operator value))
    (field : Fin 3 → Distribution domain ℝ ⊤) :
    curl domain directions (componentwise operator field) =
      componentwise operator (curl domain directions field) := by
  funext index
  simp only [curl_apply, componentwise, map_sub, commutes]

/--
**The curl commutes with the time derivative.**

The second hypothesis of `vorticity_of_balance`.  In the parabolic setting the
time derivative is `derivativeCLM` along the time direction of `ℝ × Space`, so
this is `derivativeCLM_comm` componentwise.
-/
theorem curl_derivativeCLM (direction : Point)
    (field : Fin 3 → Distribution domain ℝ ⊤) :
    curl domain directions (componentwise (derivativeCLM domain direction) field) =
      componentwise (derivativeCLM domain direction) (curl domain directions field) :=
  curl_componentwise (derivativeCLM domain direction)
    (fun other value => derivativeCLM_comm direction other value) field

/--
**The curl commutes with the Laplacian.**

The third hypothesis of `vorticity_of_balance`, for any Laplace-type operator
over any finite family of directions.
-/
theorem curl_laplaceTypeCLM {Index : Type uIndex} [Fintype Index]
    (spatial : Index → Point) (field : Fin 3 → Distribution domain ℝ ⊤) :
    curl domain directions
        (componentwise (Distribution.laplaceTypeCLM domain spatial) field) =
      componentwise (Distribution.laplaceTypeCLM domain spatial)
        (curl domain directions field) :=
  curl_componentwise (Distribution.laplaceTypeCLM domain spatial)
    (fun direction value =>
      laplaceTypeCLM_derivativeCLM_comm spatial direction value) field

/--
**The vorticity equation, concretely.**

A velocity, a pressure and a forcing --- all distributions on a single domain,
which in the application is a parabolic window in `ℝ × Space` --- satisfying
the local equation `∂_t u - Δu + ∇p = f` yield a vorticity `ω = curl u`
satisfying the heat equation `∂_t ω - Δω = curl f`.

The proof is the abstract theorem, fed the three symmetry facts.  Nothing else
happens: the pressure is eliminated because mixed partials commute.
-/
theorem vorticity_equation {Index : Type uIndex} [Fintype Index]
    (timeDirection : Point) (spatial : Index → Point)
    {velocity forcing : Fin 3 → Distribution domain ℝ ⊤}
    {pressure : Distribution domain ℝ ⊤}
    (equation :
      componentwise (derivativeCLM domain timeDirection) velocity -
          componentwise (Distribution.laplaceTypeCLM domain spatial) velocity +
          gradientField domain directions pressure =
        forcing) :
    componentwise (derivativeCLM domain timeDirection)
          (curl domain directions velocity) -
        componentwise (Distribution.laplaceTypeCLM domain spatial)
          (curl domain directions velocity) =
      curl domain directions forcing :=
  vorticity_of_balance (curl domain directions) curl_gradientField
    (curl_derivativeCLM timeDirection) (curl_laplaceTypeCLM spatial) equation

end Curl

end Hypostructure.PDE.Vorticity
