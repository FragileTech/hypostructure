import Hypostructure.PDE.Singularity
import Hypostructure.PDE.LocalSolution
import Hypostructure.PDE.NoSingularityTarget
import Hypostructure.PDE.EuclideanParabolicAtlas
import Hypostructure.PDE.Distribution.SmoothRepresentative
import Hypostructure.PDE.Strategy.RegularityStratification
import Hypostructure.PDE.Distribution.CurlCalculus
import Hypostructure.PDE.LocalTail

/-!
# The global-regularity backend of a balanced system

Every interior-regularity problem for a balance `∂_t u − Δ_x u + ∇p = f` has
the same shape:

* the target asserts that the velocity is smooth **and** that the pressure
  gradient is represented by a smooth field;
* the baseline supplies the momentum identity, the two representations, and
  smoothness of the forcing;
* the equation then names the gradient, so the second half of the target is a
  *consequence* of the first.

That last step is the only place an application would otherwise have to prove
something, and it is problem-independent: it is
`Distribution.exists_contDiffOn_representative_of_balance`.  This module packages
it, so a problem registers its balance as data and receives its
`SingularityProfile` --- and hence a localization centred on the singularity ---
with no proof of its own.

Nothing here is Stokes.  A problem supplies the fields of `BalancedRegularity`
and gets the whole opening of a global-regularity proof.
-/

namespace Hypostructure.PDE.Strategy

open MeasureTheory TopologicalSpace
open Hypostructure.PDE.Distribution
open scoped Distributions ContDiff

universe u v w x

/--
**A registered global-regularity problem for a balanced system.**

Every field is data or a reading of the baseline; none of them is a regularity
claim.  `target_of_regularity` is the only field that mentions the target, and
it receives *both* halves --- the smooth velocity and the smooth represented
gradient --- so it is pure repackaging.
-/
structure BalancedRegularity (M : LocalModel.{u}) (T : Core.Target M.problem)
    (Place : Type v) [NormedAddCommGroup Place] [NormedSpace ℝ Place]
    [MeasurableSpace Place] [BorelSpace Place] [FiniteDimensional ℝ Place]
    (Value : Type w) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure Place) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ] where
  /-- Where the object's fields live. -/
  domain : M.problem.Ambient → Opens Place
  /-- How a point of the domain names a point of the atlas. -/
  place : Place → M.atlas.Point
  /-- The velocity, as a function. -/
  velocityField : M.problem.Ambient → Place → Value
  /-- The forcing, as a function. -/
  forcingField : M.problem.Ambient → Place → Value
  /-- The velocity, as a distribution.  It is read off the baseline, because
  that is where a represented equation keeps its distributional presentation. -/
  velocity : (object : M.problem.Ambient) → M.problem.Baseline object →
    𝓓'(domain object, Value)
  /-- The forcing, as a distribution. -/
  forcing : (object : M.problem.Ambient) → M.problem.Baseline object →
    𝓓'(domain object, Value)
  /-- The pressure, as a distribution. -/
  pressure : (object : M.problem.Ambient) → M.problem.Baseline object →
    𝓓'(domain object, ℝ)
  /-- How a coordinate of a vector value is read. -/
  reader : Index → (Value →L[ℝ] ℝ)
  /-- The time direction of the balance. -/
  timeDirection : Place
  /-- The spatial directions of the balance. -/
  spatialDirection : Index → Place
  /-- The baseline says the velocity function represents the velocity
  distribution. -/
  velocityRepresents : ∀ (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object), ∀ test : 𝓓(domain object, ℝ),
      velocity object baseline test =
        ∫ place, test place • velocityField object place ∂μ
  /-- The baseline says the same of the forcing. -/
  forcingRepresents : ∀ (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object), ∀ test : 𝓓(domain object, ℝ),
      forcing object baseline test =
        ∫ place, test place • forcingField object place ∂μ
  /-- The baseline says the forcing is smooth. -/
  forcingSmooth : ∀ (object : M.problem.Ambient),
    M.problem.Baseline object →
      ContDiffOn ℝ ∞ (forcingField object) (domain object)
  /-- The baseline carries the momentum identity. -/
  momentum : ∀ (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object),
    ∀ (test : 𝓓(domain object, ℝ)) (coordinate : Index),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection (velocity object baseline) :
            𝓓'(domain object, Value)) test) -
          reader coordinate
            ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(domain object, Value) →L[ℝ] 𝓓'(domain object, Value))
                  ((Distribution.lineDerivCLM (spatialDirection axis) :
                    𝓓'(domain object, Value) →L[ℝ] 𝓓'(domain object, Value))
                      (velocity object baseline))) test) +
          (Distribution.lineDerivCLM (spatialDirection coordinate)
            (pressure object baseline) : 𝓓'(domain object, ℝ)) test =
        reader coordinate (forcing object baseline test)
  /-- The registered target, assembled from the two halves.  Pure repackaging:
  both halves are handed to it. -/
  target_of_regularity : ∀ (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object),
    ContDiffOn ℝ ∞ (velocityField object) (domain object) →
    (∃ gradientField : Place → Index → ℝ,
      (∀ coordinate : Index,
        ContDiffOn ℝ ∞ (fun place => gradientField place coordinate)
          (domain object)) ∧
      ∀ (test : 𝓓(domain object, ℝ)) (coordinate : Index),
        (Distribution.lineDerivCLM (spatialDirection coordinate)
            (pressure object baseline) : 𝓓'(domain object, ℝ)) test =
          ∫ place, test place * gradientField place coordinate ∂μ) →
    T.Predicate object

namespace BalancedRegularity

variable {M : LocalModel.{u}} {T : Core.Target M.problem}
  {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  [MeasurableSpace Place] [BorelSpace Place] [FiniteDimensional ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]
  {Index : Type x} [Fintype Index]
  {μ : Measure Place} [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ]
  (system : BalancedRegularity M T Place Value Index μ)

/--
**The equation names the gradient.**

Given a smooth velocity, the pressure gradient of a balanced system is
represented by a smooth field --- the field `f − ∂_t u + Δ_x u` the balance
leaves over.  This is the framework's
`Distribution.exists_contDiffOn_representative_of_balance`, read at the
registered system.
-/
theorem exists_gradient (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object)
    (smooth : ContDiffOn ℝ ∞ (system.velocityField object) (system.domain object)) :
    ∃ gradientField : Place → Index → ℝ,
      (∀ coordinate : Index,
        ContDiffOn ℝ ∞ (fun place => gradientField place coordinate)
          (system.domain object)) ∧
      ∀ (test : 𝓓(system.domain object, ℝ)) (coordinate : Index),
        (Distribution.lineDerivCLM (system.spatialDirection coordinate)
            (system.pressure object baseline) :
              𝓓'(system.domain object, ℝ)) test =
          ∫ place, test place * gradientField place coordinate ∂μ :=
  exists_contDiffOn_representative_of_balance (μ := μ)
    (system.velocity object baseline) (system.forcing object baseline)
    (system.pressure object baseline)
    system.reader system.timeDirection system.spatialDirection
    (system.velocityRepresents object baseline)
    (system.forcingRepresents object baseline) smooth
    (system.forcingSmooth object baseline)
    (system.momentum object baseline)

/--
**The registered target follows from smoothness of the velocity alone.**

This is the whole point of the module: an application never proves it, and the
gradient half never becomes an application obligation.
-/
theorem target_of_velocity_smooth (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object)
    (smooth : ContDiffOn ℝ ∞ (system.velocityField object) (system.domain object)) :
    T.Predicate object :=
  system.target_of_regularity object baseline smooth
    (system.exists_gradient object baseline smooth)

/--
**The singularity profile of a balanced system**, derived.

Its `regularity_of_smooth` is `target_of_velocity_smooth`, so the localization
this profile induces is centred on a genuine point of non-smoothness of the
velocity --- the singularity --- rather than on an arbitrary point of the
domain.
-/
def singularityProfile : PDE.SingularityProfile M T Place Value where
  field := system.velocityField
  region := fun object => (system.domain object : Set Place)
  place := system.place
  regularity_of_smooth := fun object baseline smooth =>
    system.target_of_velocity_smooth object baseline smooth

@[simp] theorem singularityProfile_field :
    system.singularityProfile.field = system.velocityField := rfl

@[simp] theorem singularityProfile_region (object : M.problem.Ambient) :
    system.singularityProfile.region object =
      (system.domain object : Set Place) := rfl

/-- The site of an active residual: a point at which the velocity is not
smooth.  This is the value a `PointLocalization` built from this system
returns. -/
noncomputable def site (residual : PDE.ActiveResidual M) : M.atlas.Point :=
  system.singularityProfile.site residual

/-- The site really is a singularity of the velocity. -/
theorem site_singular (residual : PDE.ActiveResidual M)
    (reads : ∀ object, residual.Target object ↔ T.Predicate object) :
    system.singularityProfile.singularPoint residual.object ∈
      PDE.singularSet (system.velocityField residual.object)
        (system.domain residual.object : Set Place) :=
  system.singularityProfile.site_singular residual reads

/--
**The point localization centred on the singularity.**

This is the replacement for a localization whose site is an arbitrary point of
the domain: `site` is `system.site`, which `site_singular` shows is a point at
which the velocity fails to be smooth.  The two geometric obligations are the
atlas', not the analysis': a base window per residual, and the fact that the
site sits inside its double core.
-/
noncomputable def pointLocalization
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (base : PDE.ActiveResidual M → M.atlas.Window)
    (point_mem : ∀ residual : PDE.ActiveResidual M,
      M.atlas.contains (system.site residual)
        (M.atlas.core (M.atlas.core (base residual))))
    (base_admissible : ∀ residual : PDE.ActiveResidual M,
      Admissible residual.object (base residual)) :
    PDE.PointLocalization M where
  Admissible := Admissible
  site := system.site
  base := base
  point_mem_core_core := point_mem
  base_admissible := base_admissible

@[simp] theorem pointLocalization_site
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (base : PDE.ActiveResidual M → M.atlas.Window)
    (point_mem) (base_admissible) (residual : PDE.ActiveResidual M) :
    (system.pointLocalization Admissible base point_mem base_admissible).site
      residual = system.site residual := rfl

/-- The outer window of the derived focus is the base window, and it is
centred on the singularity. -/
@[simp] theorem pointLocalization_focus_outer
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (base : PDE.ActiveResidual M → M.atlas.Window)
    (point_mem) (base_admissible) (residual : PDE.ActiveResidual M) :
    ((system.pointLocalization Admissible base point_mem base_admissible).focus
      residual).outer = base residual := rfl

/-! ## The six ordered alternatives, generic

`stokes:prop:finite-state-stratification` names six states.  None of them is
about any particular equation: they are "no singularity", "the represented
equation is available", "the rotational datum has a smooth representative",
"the potential splits with an annihilated tail", "the field is smooth modulo
the harmonic kernel", and "the potential's gradient is smooth".  Stated over a
`BalancedRegularity` they are problem-independent, so a second global-regularity
problem registers the same six by instantiating this section.
-/

section Stratification

open Hypostructure.PDE.Distribution.CurlCalculus

/-- **Alternative 1.**  The field has no singularity in its region --- the
representative under consideration is already smooth there. -/
def AlreadyRegular (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  PDE.singularSet (system.velocityField input.object)
    (system.domain input.object : Set Place) = ∅

/-- **Alternative 2.**  The represented equation is available for the selected
residual.  It always is --- it is a projection of the baseline --- so this
alternative's failure arm is closed by `alreadyReduced`. -/
def EquationAvailable (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  ∀ (test : 𝓓(system.domain input.object, ℝ)) (coordinate : Index),
    system.reader coordinate
        ((Distribution.lineDerivCLM system.timeDirection
          (system.velocity input.object input.baseline) :
            𝓓'(system.domain input.object, Value)) test) -
        system.reader coordinate
          ((∑ axis : Index,
            (Distribution.lineDerivCLM (system.spatialDirection axis) :
                𝓓'(system.domain input.object, Value) →L[ℝ]
                  𝓓'(system.domain input.object, Value))
              ((Distribution.lineDerivCLM (system.spatialDirection axis) :
                𝓓'(system.domain input.object, Value) →L[ℝ]
                  𝓓'(system.domain input.object, Value))
                  (system.velocity input.object input.baseline))) test) +
        (Distribution.lineDerivCLM (system.spatialDirection coordinate)
          (system.pressure input.object input.baseline) :
            𝓓'(system.domain input.object, ℝ)) test =
      system.reader coordinate (system.forcing input.object input.baseline test)

/-- The represented equation *is* available: it is the baseline's own momentum
identity.  This is what closes alternative 2's surviving arm. -/
theorem equationAvailable (input : Core.Strategy.ProblemInput M.problem) :
    system.EquationAvailable input :=
  system.momentum input.object input.baseline

/-- **Alternative 3.**  The *rotational* datum of the field has a smooth
representative on the region --- the antisymmetric part of its derivative
matrix, `∂_i u_j − ∂_j u_i`, which is the vorticity.

Only the antisymmetric part: `stokes:cor:vorticity-smoothing` smooths the
vorticity, and the symmetric part is not available at this stage.  Asking for
every `∂_i u` to have a smooth representative would be asking for `∇u`, which
is the conclusion of the whole argument rather than the third of six steps. -/
def RotationalSmoothed (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  ∃ rotationField : Index → Index → Place → ℝ,
    (∀ first second : Index,
      ContDiffOn ℝ ∞ (rotationField first second)
        (system.domain input.object : Set Place)) ∧
    ∀ (first second : Index) (test : 𝓓(system.domain input.object, ℝ)),
      system.reader second
          ((Distribution.lineDerivCLM (system.spatialDirection first) :
              𝓓'(system.domain input.object, Value) →L[ℝ]
                𝓓'(system.domain input.object, Value))
              (system.velocity input.object input.baseline) test) -
        system.reader first
          ((Distribution.lineDerivCLM (system.spatialDirection second) :
              𝓓'(system.domain input.object, Value) →L[ℝ]
                𝓓'(system.domain input.object, Value))
              (system.velocity input.object input.baseline) test) =
      ∫ place, test place * rotationField first second place ∂μ

/-- **Alternative 4.**  The potential splits exactly into a local child and a
complementary tail annihilated by the spatial Laplacian.  The split always
exists (`ExactLocalTail.ofSub`); annihilation of the tail is the content. -/
def PotentialDecomposed (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  ∃ (split : PDE.ExactLocalTail 𝓓'(system.domain input.object, ℝ)
      (system.pressure input.object input.baseline))
    (localGradient : Index → Place → ℝ),
    (∀ test : 𝓓(system.domain input.object, ℝ),
      Distribution.laplaceTypeCLM (system.domain input.object)
        system.spatialDirection split.tailPart test = 0) ∧
    (∀ axis : Index,
      ContDiffOn ℝ ∞ (localGradient axis)
        (system.domain input.object : Set Place)) ∧
    ∀ (axis : Index) (test : 𝓓(system.domain input.object, ℝ)),
      (Distribution.lineDerivCLM (system.spatialDirection axis) :
          𝓓'(system.domain input.object, ℝ) →L[ℝ]
            𝓓'(system.domain input.object, ℝ))
          split.localPart test =
        ∫ place, test place * localGradient axis place ∂μ

/-- **Alternative 5.**  The field is smooth modulo the local harmonic kernel:
the parasitic curl-free divergence-free mode is removed, what is left is
smooth, **and the removed mode is itself zero or smooth**.

The last clause is `stokes:prop:finite-state-stratification`(4) --- *"for a raw
representative, the additional condition is that this component be zero or
smooth on the smaller cylinder"* --- and it is not optional.  Without it the
alternative is satisfied by `stokes:rem:parasitic-counterexample`,
`u = a(t) ∇ψ(x)` with `ψ` spatially harmonic and `a` merely `L²`: that field is
its own removed mode, so the quotient is `0` and every other clause holds, while
`u` has no smooth representative.  Dropping the clause would therefore make this
alternative's closing arm false, exactly as
`Solution/HarmonicKernelSmoothing.lean` records for the grade hypothesis it
plays the same role as. -/
def RecoveredModuloKernel (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  ∃ (kernel : 𝓓'(system.domain input.object, Value))
    (kernelField : Place → Value),
    (∀ test : 𝓓(system.domain input.object, ℝ),
      kernel test = ∫ place, test place • kernelField place ∂μ) ∧
    -- The removed mode is divergence-free.
    (∀ test : 𝓓(system.domain input.object, ℝ),
      ∑ axis : Index, system.reader axis
        ((Distribution.lineDerivCLM (system.spatialDirection axis) :
            𝓓'(system.domain input.object, Value) →L[ℝ]
              𝓓'(system.domain input.object, Value)) kernel test) = 0) ∧
    -- …and curl-free: its matrix of derivatives is symmetric.
    (∀ (first second : Index) (test : 𝓓(system.domain input.object, ℝ)),
      system.reader second
          ((Distribution.lineDerivCLM (system.spatialDirection first) :
              𝓓'(system.domain input.object, Value) →L[ℝ]
                𝓓'(system.domain input.object, Value)) kernel test) =
        system.reader first
          ((Distribution.lineDerivCLM (system.spatialDirection second) :
              𝓓'(system.domain input.object, Value) →L[ℝ]
                𝓓'(system.domain input.object, Value)) kernel test)) ∧
    -- …and the removed mode is zero or smooth on the region.
    ContDiffOn ℝ ∞ kernelField (system.domain input.object : Set Place) ∧
    ContDiffOn ℝ ∞
      (fun place => system.velocityField input.object place - kernelField place)
      (system.domain input.object : Set Place)

/-- **Alternative 6.**  The balance names the gradient and it is smooth.  This
is exactly the second half of the target, so its reached arm closes. -/
def GradientClosed (input : Core.Strategy.ProblemInput M.problem) : Prop :=
  ContDiffOn ℝ ∞ (system.velocityField input.object)
    (system.domain input.object : Set Place)

/-- The reached arm of alternative 6 closes into the registered target: a
smooth field is all `target_of_velocity_smooth` needs. -/
theorem target_of_gradientClosed
    (input : Core.Strategy.ProblemInput M.problem)
    (reached : system.GradientClosed input) :
    T.Predicate input.object :=
  system.target_of_velocity_smooth input.object input.baseline reached

/--
**The reached arm of alternative 5 closes into the registered target.**

This is the last paragraph of `stokes:thm:interior-regularity` --- *"if the
harmonic-kernel component `h = proj u` is smooth on `B_r × I_r`, then
`u = u^⊥ + h` is smooth there"* --- read off the alternative's own two
smoothness clauses.  The quotient `u − h` is the recovery clause and `h` is the
normalization clause, so nothing is derived here beyond `ContDiffOn.add`: the
analysis is in the alternative, not in this step.
-/
theorem target_of_recoveredModuloKernel
    (input : Core.Strategy.ProblemInput M.problem)
    (reached : system.RecoveredModuloKernel input) :
    T.Predicate input.object := by
  obtain ⟨_kernel, _kernelField, _represents, _divergenceFree, _curlFree,
    kernelSmooth, quotientSmooth⟩ := reached
  refine system.target_of_velocity_smooth input.object input.baseline ?_
  simpa using quotientSmooth.add kernelSmooth

/-! ### The stratification really is one

`Stage.refines later earlier` declares the six states cumulative: reaching a
later one means every earlier one is already reached.  For the six predicates
above that is not a convention, it is a theorem, and the three lemmas below
prove it for the three states between the equation and the closing one.

Their consequence is the one fact the DAG needs about its own shape.  Each of
alternatives 3, 4 and 5 fails *only if* alternative 6 fails, so the arms on
which those alternatives fail carry no residual of their own: they carry the
residual of the closing alternative.  Four surviving branches are one
surviving branch, and it is `¬ GradientClosed` --- the velocity is not smooth
on the domain.  The DAG routes them accordingly.
-/

/-- The classical rotational field of a smooth velocity: the antisymmetric part
of its derivative matrix, read coordinate by coordinate.  This is the field
alternative 3 asks for, written down rather than produced. -/
noncomputable def rotationField (object : M.problem.Ambient)
    (first second : Index) (place : Place) : ℝ :=
  lineDeriv ℝ (fun position =>
      system.reader second (system.velocityField object position))
    place (system.spatialDirection first) -
  lineDeriv ℝ (fun position =>
      system.reader first (system.velocityField object position))
    place (system.spatialDirection second)

/-- A coordinate of the velocity is as smooth as the velocity: the reader is a
continuous linear map. -/
theorem contDiffOn_velocity_component (object : M.problem.Ambient)
    (smooth : ContDiffOn ℝ ∞ (system.velocityField object)
      (system.domain object : Set Place))
    (coordinate : Index) :
    ContDiffOn ℝ ∞ (fun position =>
        system.reader coordinate (system.velocityField object position))
      (system.domain object : Set Place) :=
  (system.reader coordinate).contDiff.comp_contDiffOn smooth

/-- **A coordinate of a spatial derivative of a smoothly represented velocity is
represented by the classical derivative of that coordinate.**

Reading a coordinate commutes with differentiating (`mapCLM_lineDerivCLM`),
the read state is represented by the read field (`represents_mapCLM`), and the
derivative of a smoothly represented state is represented by the classical one
(`represents_lineDeriv`).  Three framework lemmas, no analysis. -/
theorem represents_velocity_lineDeriv (object : M.problem.Ambient)
    (baseline : M.problem.Baseline object)
    (smooth : ContDiffOn ℝ ∞ (system.velocityField object)
      (system.domain object : Set Place))
    (axis coordinate : Index) (test : 𝓓(system.domain object, ℝ)) :
    system.reader coordinate
        ((Distribution.lineDerivCLM (system.spatialDirection axis) :
            𝓓'(system.domain object, Value) →L[ℝ]
              𝓓'(system.domain object, Value))
          (system.velocity object baseline) test) =
      ∫ place, test place * lineDeriv ℝ (fun position =>
          system.reader coordinate (system.velocityField object position))
        place (system.spatialDirection axis) ∂μ := by
  have component := system.contDiffOn_velocity_component object smooth coordinate
  have componentRepresents : ∀ probe : 𝓓(system.domain object, ℝ),
      (Distribution.mapCLM (system.reader coordinate)
          (system.velocity object baseline) : 𝓓'(system.domain object, ℝ)) probe =
        ∫ place, probe place *
          system.reader coordinate (system.velocityField object place) ∂μ :=
    fun probe => Distribution.represents_mapCLM (μ := μ) (system.reader coordinate)
      (system.velocity object baseline) smooth.continuousOn
      (system.velocityRepresents object baseline) probe
  rw [← Distribution.mapCLM_apply,
    Distribution.mapCLM_lineDerivCLM (system.reader coordinate)
      (system.velocity object baseline) (system.spatialDirection axis) test,
    Distribution.represents_lineDeriv (μ := μ) _ componentRepresents component
      (system.spatialDirection axis) test]

/-- **Alternative 6 implies alternative 3.**  The rotational datum of a smooth
velocity is the antisymmetric part of its classical derivative matrix. -/
theorem rotationalSmoothed_of_gradientClosed
    (input : Core.Strategy.ProblemInput M.problem)
    (reached : system.GradientClosed input) :
    system.RotationalSmoothed input := by
  refine ⟨system.rotationField input.object, ?_, ?_⟩
  · intro first second
    exact (contDiffOn_lineDeriv
        (system.contDiffOn_velocity_component input.object reached second)
        (system.spatialDirection first)).sub
      (contDiffOn_lineDeriv
        (system.contDiffOn_velocity_component input.object reached first)
        (system.spatialDirection second))
  · intro first second test
    rw [system.represents_velocity_lineDeriv input.object input.baseline reached
        first second test,
      system.represents_velocity_lineDeriv input.object input.baseline reached
        second first test,
      ← integral_sub
        (Distribution.integrable_testMul (μ := μ) test
          (contDiffOn_lineDeriv
            (system.contDiffOn_velocity_component input.object reached second)
            (system.spatialDirection first)).continuousOn)
        (Distribution.integrable_testMul (μ := μ) test
          (contDiffOn_lineDeriv
            (system.contDiffOn_velocity_component input.object reached first)
            (system.spatialDirection second)).continuousOn)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun place => by
      simp [rotationField, mul_sub])

/-- **Alternative 6 implies alternative 4.**  The split is the framework's
`ExactLocalTail.ofSub` with the potential itself as the local child, so the
tail is zero and its Laplacian is zero because the operator is linear; the
local gradient is the one the balance names. -/
theorem potentialDecomposed_of_gradientClosed
    (input : Core.Strategy.ProblemInput M.problem)
    (reached : system.GradientClosed input) :
    system.PotentialDecomposed input := by
  obtain ⟨gradientField, gradientSmooth, gradientRepresents⟩ :=
    system.exists_gradient input.object input.baseline reached
  refine ⟨PDE.ExactLocalTail.ofSub (system.pressure input.object input.baseline)
      (system.pressure input.object input.baseline),
    fun axis place => gradientField place axis, ?_, gradientSmooth, ?_⟩
  · intro test
    simp
  · intro axis test
    simpa using gradientRepresents test axis

/-- **Alternative 6 implies alternative 5.**  A smooth velocity needs no
recovery: the discarded harmonic mode is zero, which is divergence-free and
curl-free for the trivial reason, is smooth because it is constant --- the
"zero" half of the normalization clause --- and what is left is the velocity
itself. -/
theorem recoveredModuloKernel_of_gradientClosed
    (input : Core.Strategy.ProblemInput M.problem)
    (reached : system.GradientClosed input) :
    system.RecoveredModuloKernel input := by
  refine ⟨0, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro test; simp
  · intro test; simp
  · intro first second test; simp
  · exact contDiffOn_const
  · simpa [GradientClosed] using reached

/-- **The six alternatives, registered in the appendix's order.**

Three arms close with no analytic input: alternative 2's failure (the equation
is a projection of the baseline, so its absence is absurd), alternative 5's
success (`u = u^⊥ + h` with both summands handed over smooth) and alternative
6's success (a smooth field gives the target through the balance).  The other
three carry the surviving residual.

Alternatives 3 and 4 have **no** target-valued closing arm, and this is a fact
about the mathematics rather than a gap in the wiring.  Both are refuted by
`stokes:rem:parasitic-counterexample`: `u = a(t) ∇ψ(x)` with `a` merely `L²` has
`curl u = 0` --- so its rotational datum is smooth, and alternative 3 holds ---
and `Δp = div f = 0` --- so the potential splits with a purely harmonic tail and
a vanishing local gradient, and alternative 4 holds --- while `u` has no smooth
representative.  Their manuscript conclusions
(`stokes:cor:vorticity-smoothing`, `stokes:lem:local-CZ-pressure`) are the
alternatives themselves, and the manuscript reaches the target from them only by
advancing to alternative 5 through `stokes:lem:velocity-recovery`.
-/
noncomputable def alternatives :
    List (RegularityStratification.Alternative M T) :=
  [ { stage := .regular
      Reached := system.AlreadyRegular
      metadata := { name := "1. Already regular near the singularity"
                    note := "The singular set of the field is empty." }
      reachedMetadata := { name := "No singularity" }
      failedMetadata := { name := "A singularity survives" }
      -- An empty singular set *is* interior regularity
      -- (`singularSet_eq_empty_iff`), which is what the target asks for.  This
      -- arm therefore closes with no analysis at all.
      closeReached := some ⟨fun input reached =>
        system.target_of_velocity_smooth input.object input.baseline
          (PDE.singularSet_eq_empty_iff.mp reached.down)⟩ },
    { stage := .vorticityReduced
      Reached := system.EquationAvailable
      metadata := { name := "2. The equation is the active datum"
                    note := "Taking the curl removes the potential and leaves \
                      the local heat equation." }
      reachedMetadata := { name := "Represented equation available" }
      failedMetadata := { name := "No represented equation" }
      closeFailed := some ⟨fun input failure =>
        absurd (system.equationAvailable input) failure.down⟩ },
    { stage := .vorticitySmoothed
      Reached := system.RotationalSmoothed
      metadata := { name := "3. Rotational smoothing"
                    note := "The rotational datum is smooth on every \
                      compactly contained subwindow." }
      reachedMetadata := { name := "Rotational datum smooth" }
      failedMetadata := { name := "No rotational smoothing" } },
    { stage := .pressureDecomposed
      Reached := system.PotentialDecomposed
      metadata := { name := "4. Calderon-Zygmund decomposition"
                    note := "The potential splits and the complementary tail \
                      is annihilated by the spatial Laplacian." }
      reachedMetadata := { name := "Split available" }
      failedMetadata := { name := "No decomposition" } },
    { stage := .velocityRecovered
      Reached := system.RecoveredModuloKernel
      metadata := { name := "5. Recovery modulo the harmonic kernel"
                    note := "The quotient field is recovered and the parasitic \
                      mode is normalized away." }
      reachedMetadata := { name := "Quotient field recovered" }
      failedMetadata := { name := "No recovery" }
      -- `u = u^⊥ + h` with both summands smooth: the recovery clause gives the
      -- first and the normalization clause the second, so the velocity is
      -- smooth and `target_of_velocity_smooth` closes.
      closeReached := some ⟨fun input reached =>
        system.target_of_recoveredModuloKernel input reached.down⟩ },
    { stage := .gradientClosed
      Reached := system.GradientClosed
      metadata := { name := "6. Gradient from the equation"
                    note := "The balance names the gradient and the regularity \
                      of the data is inherited by it." }
      reachedMetadata := { name := "Gradient closed" }
      failedMetadata := { name := "No gradient closure" }
      closeReached := some ⟨fun input reached =>
        system.target_of_gradientClosed input reached.down⟩ } ]

@[simp] theorem alternatives_length : system.alternatives.length = 6 := rfl

/-- How far the local argument gets: the highest alternative whose state holds.
Core decides each classically. -/
noncomputable def stageReached (input : Core.Strategy.ProblemInput M.problem) :
    RegularityStratification.Stage :=
  letI := Classical.propDecidable
  if system.GradientClosed input then .gradientClosed
  else if system.RecoveredModuloKernel input then .velocityRecovered
  else if system.PotentialDecomposed input then .pressureDecomposed
  else if system.RotationalSmoothed input then .vorticitySmoothed
  else if system.EquationAvailable input then .vorticityReduced
  else .regular

/-- The stratification's finite local algebra, labelled by the stage reached at
the framework's derived window. -/
noncomputable def stageLabelling :
    RegularityStratification.Labelling
      (Core.Strategy.ProblemInput M.problem) where
  Window := fun _ => PUnit
  windows := fun _ => Core.Finite.Enumeration.singleton PUnit.unit
  stageAt := fun input _ => system.stageReached input

end Stratification

/-! ## The proof-free entry point

Everything above is stated over an arbitrary model, so it has to *ask* for the
balance and the target bridge.  For a problem registered the framework's own
way --- `PDE.problemWithBalance`, whose baseline **is** the balance, and
`PDE.noSingularityTarget`, whose predicate **is** the emptiness of the singular
set --- none of that has to be asked for:

* the two representations, the source smoothness and the momentum identity are
  projections of `input.baseline`, exactly as `k ≤ minDegree` is a projection of
  a graph problem input (`Graph/Strategy/MinimumDegreeBaseline.lean:36`);
* the target bridge is `noSingularity_of_contDiffOn`, a framework theorem.

So `ofBalancedProblem` takes **no proof arguments at all**.  An application
calls it and receives the whole global-regularity backend.
-/

/--
**The represented equation of a balanced problem.**

Its `EquationData` is trivial and its `satisfies` **is the balance**, because
for a problem registered through `problemWithBalance` the balance is the
*baseline* --- there is nothing left for the equation slot to carry separately.
So `EquationState.valid` at any window is the balance of the selected residual,
and `restrict_satisfies` is `fun _ _ _ valid => valid` because restriction is
the identity on this atlas.

This is not a placeholder equation: the content is in `satisfies`, and it is the
same proposition the baseline pins.
-/
def balanceEquation (dimension : ℕ)
    (Value : Type) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type) [Fintype Index]
    (μ : Measure (PDE.Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → PDE.Place dimension)
    (Momentum : PDE.FieldObject dimension Value → Prop)
    (BranchState : PDE.FieldObject dimension Value → Type)
    (Presentation : Type) (presentation : Presentation) :
    PDE.RepresentedEquation
      (PDE.problemWithBalance dimension Value Index μ reader spatialDirection
        Momentum BranchState Presentation presentation)
      (PDE.euclideanParabolicAtlas
        (PDE.problemWithBalance dimension Value Index μ reader spatialDirection
          Momentum BranchState Presentation presentation) dimension) where
  EquationData := fun _window _object => PUnit
  satisfies := fun {_window} {object} _data =>
    PDE.IsLocalSolution dimension Value μ Momentum
      (PDE.HarmonicKernelNormalized dimension Value Index μ reader
        spatialDirection) object
  restrictEquation := fun {_small} {_large} _nested {_object} _data => PUnit.unit
  restrict_satisfies := fun _nested _object _data valid => valid

/-- The model of a canonically registered balanced problem: the Euclidean
parabolic atlas carrying `balanceEquation`. -/
abbrev balancedModel (dimension : ℕ)
    (Value : Type) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type) [Fintype Index]
    (μ : Measure (PDE.Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → PDE.Place dimension)
    (Momentum : PDE.FieldObject dimension Value → Prop)
    (BranchState : PDE.FieldObject dimension Value → Type)
    (Presentation : Type) (presentation : Presentation) : PDE.LocalModel :=
  PDE.euclideanParabolicModel dimension
    (balanceEquation dimension Value Index μ reader spatialDirection Momentum
      BranchState Presentation presentation)

/--
**The balanced-regularity system of a canonically registered problem.**

Zero proof arguments.  Compare `Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition`,
which likewise takes only data and a target bridge and hands back a fully
derived registration.
-/
noncomputable def ofBalancedProblem (dimension : ℕ)
    (Value : Type) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value]
    (Index : Type) [Fintype Index]
    (μ : Measure (PDE.Place dimension)) [μ.IsAddHaarMeasure]
    [IsFiniteMeasureOnCompacts μ]
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : PDE.Place dimension)
    (spatialDirection : Index → PDE.Place dimension)
    (BranchState : PDE.FieldObject dimension Value → Type)
    (Presentation : Type) (presentation : Presentation)
    (equation : PDE.RepresentedEquation
      (PDE.problemWithBalance dimension Value Index μ reader spatialDirection
        (PDE.LinearParabolicMomentum dimension Value Index reader timeDirection
          spatialDirection)
        BranchState Presentation presentation)
      (PDE.euclideanParabolicAtlas
        (PDE.problemWithBalance dimension Value Index μ reader spatialDirection
          (PDE.LinearParabolicMomentum dimension Value Index reader
            timeDirection spatialDirection)
          BranchState Presentation presentation) dimension)) :
    BalancedRegularity
      (PDE.euclideanParabolicModel dimension equation)
      (PDE.noSingularityTarget dimension Value μ
        (PDE.IsLocalSolution dimension Value μ
          (PDE.LinearParabolicMomentum dimension Value Index reader
            timeDirection spatialDirection)
          (PDE.HarmonicKernelNormalized dimension Value Index μ reader
            spatialDirection))
        BranchState Presentation presentation)
      (PDE.Place dimension) Value Index μ where
  domain := fun object => object.domain
  place := id
  velocityField := fun object => object.field
  forcingField := fun object => object.source
  velocity := fun object _baseline => object.fieldState
  forcing := fun object _baseline => object.sourceState
  pressure := fun object _baseline => object.potential
  reader := reader
  timeDirection := timeDirection
  spatialDirection := spatialDirection
  -- The four former obligations, now projections of the registered baseline.
  velocityRepresents := fun _object baseline => baseline.fieldRepresents
  forcingRepresents := fun _object baseline => baseline.sourceRepresents
  forcingSmooth := fun _object baseline => baseline.sourceSmooth
  momentum := fun _object baseline => baseline.momentum
  -- The former target obligation, now a framework theorem.  The gradient half
  -- is handed in and discarded: the registered target speaks only about the
  -- field, and a smooth field is its own smooth representative.
  target_of_regularity := fun _object _baseline smooth _gradient =>
    PDE.noSingularity_of_contDiffOn smooth

end BalancedRegularity

end Hypostructure.PDE.Strategy
