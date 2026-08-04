import Hypostructure.PDE.Vorticity
import Hypostructure.PDE.Distribution.SmoothRepresentative

/-!
# A vector-valued balance, read in coordinates

`Vorticity.lean` proves the vorticity equation for a balance written as three
*scalar* distributions.  An application writes its momentum identity on a
single `Value`-valued distribution and reads it in coordinates, because that is
what the equation of the problem looks like.

This module is the bridge, and it is nothing more than linearity: reading a
coordinate of a distribution is `Distribution.mapCLM`, which commutes with
every derivative and with finite sums.  So a coordinate-read vector balance
*is* the scalar balance of `Vorticity.lean`, and the vorticity equation
follows with no further hypothesis.

Nothing here is an estimate, a window, a residual or an equation of any named
problem: the balance is a hypothesis and the vorticity equation is its
consequence.
-/

namespace Hypostructure.PDE.Distribution

open TopologicalSpace
open Hypostructure.PDE.Vorticity
open scoped Distributions

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {domain : Opens Point} {directions : Fin 3 → Point}
  {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/-- The coordinates of a vector-valued distribution, as three scalar
distributions. -/
noncomputable def components (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (state : Distribution domain Value ⊤) : Fin 3 → Distribution domain ℝ ⊤ :=
  fun index => Distribution.mapCLM (reader index) state

@[simp] theorem components_apply (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (state : Distribution domain Value ⊤) (index : Fin 3)
    (test : 𝓓(domain, ℝ)) :
    components reader state index test = reader index (state test) :=
  rfl

/-- Reading a coordinate commutes with differentiating. -/
theorem components_lineDerivCLM (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (state : Distribution domain Value ⊤) (direction : Point) :
    components reader
        ((Distribution.lineDerivCLM direction :
          Distribution domain Value ⊤ →L[ℝ] Distribution domain Value ⊤) state) =
      componentwise (derivativeCLM domain direction)
        (components reader state) := by
  funext index
  ext test
  show reader index (-(state _)) = -(reader index (state _))
  exact map_neg _ _

/-- Reading a coordinate commutes with the Laplace-type operator: it is a
finite sum of iterated derivatives. -/
theorem components_laplaceTypeCLM {Index : Type*} [Fintype Index]
    (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (state : Distribution domain Value ⊤) (spatial : Index → Point) :
    components reader
        ((Finset.univ.sum fun axis =>
          (Distribution.lineDerivCLM (spatial axis) :
              Distribution domain Value ⊤ →L[ℝ] Distribution domain Value ⊤).comp
            (Distribution.lineDerivCLM (spatial axis) :
              Distribution domain Value ⊤ →L[ℝ] Distribution domain Value ⊤))
          state) =
      componentwise (laplaceTypeCLM domain spatial) (components reader state) := by
  funext index
  ext test
  simp only [components, componentwise, Distribution.mapCLM_apply, laplaceTypeCLM,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun _axis _mem => ?_
  simp [Distribution.lineDerivCLM_apply, Distribution.mapCLM_apply]

/--
**The vorticity equation of a coordinate-read vector balance.**

The hypothesis is the momentum identity exactly as an application states it:
tested against one test function, read in one coordinate.  The conclusion is
the heat equation for the curl of the coordinates, in the same reading.  The
pressure has disappeared because the curl of a gradient vanishes.
-/
theorem vorticity_equation_of_components (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (timeDirection : Point)
    (velocity forcing : Distribution domain Value ⊤)
    (pressure : Distribution domain ℝ ⊤)
    (balance : ∀ (test : 𝓓(domain, ℝ)) (index : Fin 3),
      reader index
          ((Distribution.lineDerivCLM timeDirection :
            Distribution domain Value ⊤ →L[ℝ] Distribution domain Value ⊤)
              velocity test) -
          reader index
            ((Finset.univ.sum fun axis : Fin 3 =>
              (Distribution.lineDerivCLM (directions axis) :
                  Distribution domain Value ⊤ →L[ℝ]
                    Distribution domain Value ⊤).comp
                (Distribution.lineDerivCLM (directions axis) :
                  Distribution domain Value ⊤ →L[ℝ]
                    Distribution domain Value ⊤)) velocity test) +
          (Distribution.lineDerivCLM (directions index) :
            Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤) pressure test =
        reader index (forcing test)) :
    ∀ index : Fin 3,
      derivativeCLM domain timeDirection
          (curl domain directions (components reader velocity) index) -
        laplaceTypeCLM domain directions
          (curl domain directions (components reader velocity) index) =
      curl domain directions (components reader forcing) index := by
  have scalar :
      componentwise (derivativeCLM domain timeDirection)
            (components reader velocity) -
          componentwise (laplaceTypeCLM domain directions)
            (components reader velocity) +
          gradientField domain directions pressure =
        components reader forcing := by
    rw [← components_lineDerivCLM reader velocity timeDirection,
      ← components_laplaceTypeCLM reader velocity directions]
    funext index
    ext test
    simp only [Pi.add_apply, Pi.sub_apply, sub_apply, add_apply, components_apply,
      gradientField, derivativeCLM]
    exact balance test index
  have := vorticity_equation (domain := domain) (directions := directions)
    (Index := Fin 3) timeDirection directions
    (velocity := components reader velocity) (forcing := components reader forcing)
    (pressure := pressure) scalar
  intro index
  exact congrFun this index

/-! ## Reassembling a vector from its coordinates

The inverse of `components` for a Euclidean value: the three scalar
distributions are put back into one vector-valued distribution.  It is a finite
sum of coordinate liftings and nothing else, so the reading law is immediate
and the round trip is definitional.
-/

section Assemble

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]

/-- Lift a scalar into one Euclidean coordinate. -/
noncomputable def liftCoordinate (index : Coordinate) :
    ℝ →L[ℝ] EuclideanSpace ℝ Coordinate :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single index (1 : ℝ))

/-- Reassemble a vector-valued distribution from its coordinates. -/
noncomputable def assemble (family : Coordinate → Distribution domain ℝ ⊤) :
    Distribution domain (EuclideanSpace ℝ Coordinate) ⊤ :=
  ∑ index : Coordinate, Distribution.mapCLM (liftCoordinate index) (family index)

@[simp] theorem assemble_apply (family : Coordinate → Distribution domain ℝ ⊤)
    (test : 𝓓(domain, ℝ)) (index : Coordinate) :
    (assemble family test) index = family index test := by
  simp [assemble, liftCoordinate, EuclideanSpace.single, Finset.sum_apply,
    Pi.single_apply]

/-- The round trip: reading the coordinates of an assembled vector returns the
family it was assembled from. -/
theorem components_assemble
    (family : Fin 3 → Distribution domain ℝ ⊤) :
    components (fun index => EuclideanSpace.proj index) (assemble family) = family := by
  funext index
  ext test
  exact assemble_apply family test index

end Assemble

/-! ## The vorticity as one vector-valued distribution

`vorticity_equation_of_components` delivers the heat equation for the *three
scalar coordinates* of the curl, because that is the shape the abstract
argument of `Vorticity.lean` runs in.  An application carries its vorticity as
a single `Value`-valued distribution, exactly like its velocity, and reads
coordinates of it when it states an equation.

This section closes that last gap.  The assembled vorticity is defined here,
its coordinates are the curl by the round trip already proved above, and the
heat equation is restated in the assembled reading.  An application therefore
instantiates a term and states no lemma of its own.
-/

section AssembledVorticity

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]

/--
**The vorticity of a coordinate-read vector balance**, as one vector-valued
distribution: take coordinates, curl them, and put the result back together.
-/
noncomputable def assembledVorticity (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (directions : Fin 3 → Point) (velocity : Distribution domain Value ⊤) :
    Distribution domain (EuclideanSpace ℝ (Fin 3)) ⊤ :=
  assemble (curl domain directions (components reader velocity))

/-- Its coordinates are the curl it was assembled from. -/
@[simp] theorem components_assembledVorticity (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (directions : Fin 3 → Point) (velocity : Distribution domain Value ⊤) :
    components (fun index => EuclideanSpace.proj index)
        (assembledVorticity reader directions velocity) =
      curl domain directions (components reader velocity) :=
  components_assemble _

/--
**The vorticity equation, read on the assembled vorticity.**

Same hypothesis as `vorticity_equation_of_components` --- the application's own
momentum identity, tested against one test function in one coordinate --- and
the same conclusion, now stated about the coordinates of the single
vector-valued vorticity the application carries.  The pressure is gone because
the curl of a gradient vanishes.
-/
theorem vorticity_equation_of_assembled (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (timeDirection : Point)
    (velocity forcing : Distribution domain Value ⊤)
    (pressure : Distribution domain ℝ ⊤)
    (balance : ∀ (test : 𝓓(domain, ℝ)) (index : Fin 3),
      reader index
          ((Distribution.lineDerivCLM timeDirection :
            Distribution domain Value ⊤ →L[ℝ] Distribution domain Value ⊤)
              velocity test) -
          reader index
            ((Finset.univ.sum fun axis : Fin 3 =>
              (Distribution.lineDerivCLM (directions axis) :
                  Distribution domain Value ⊤ →L[ℝ]
                    Distribution domain Value ⊤).comp
                (Distribution.lineDerivCLM (directions axis) :
                  Distribution domain Value ⊤ →L[ℝ]
                    Distribution domain Value ⊤)) velocity test) +
          (Distribution.lineDerivCLM (directions index) :
            Distribution domain ℝ ⊤ →L[ℝ] Distribution domain ℝ ⊤) pressure test =
        reader index (forcing test))
    (index : Fin 3) :
    derivativeCLM domain timeDirection
          (components (fun coordinate => EuclideanSpace.proj coordinate)
            (assembledVorticity reader directions velocity) index) -
        laplaceTypeCLM domain directions
          (components (fun coordinate => EuclideanSpace.proj coordinate)
            (assembledVorticity reader directions velocity) index) =
      curl domain directions (components reader forcing) index := by
  rw [components_assembledVorticity]
  exact vorticity_equation_of_components reader timeDirection velocity forcing
    pressure balance index

end AssembledVorticity

/-! ## The local harmonic kernel

The kernel of the pair `(curl, div)`: the modes a vorticity argument cannot
see.  For a simply connected window these are the gradients of harmonic
potentials, and they are exactly the parasitic modes a normalization removes
--- a field in this kernel may carry arbitrarily rough time dependence while
every curl estimate about it holds vacuously.

It is stated here, on the same coordinate reading as the balance, so that no
application has to name its own notion of "harmonic component".
-/

/--
**The local harmonic kernel of a vector-valued distribution.**

Both the distributional curl and the distributional divergence vanish on the
whole domain, read in the coordinates the balance is written in.
-/
def InHarmonicKernel (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (directions : Fin 3 → Point) (state : Distribution domain Value ⊤) : Prop :=
  curl domain directions (components reader state) = 0 ∧
    ∑ axis : Fin 3,
      derivativeCLM domain (directions axis) (components reader state axis) = 0

/-- The zero distribution lies in the harmonic kernel, so a statement quantified
over kernel components is never vacuous: taking the kernel to be zero recovers
the un-normalized reading. -/
theorem inHarmonicKernel_zero (reader : Fin 3 → (Value →L[ℝ] ℝ))
    (directions : Fin 3 → Point) :
    InHarmonicKernel (domain := domain) reader directions 0 := by
  constructor
  · funext index
    simp [curl_apply, components, Pi.zero_apply]
  · simp [components]

end Hypostructure.PDE.Distribution
