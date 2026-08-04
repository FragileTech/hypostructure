import Hypostructure.PDE.Localization.RegularityTransport
import Hypostructure.PDE.Coordinate

/-!
# Parabolic recentering and rescaling

The two changes of coordinates a parabolic localization performs:

* **translation**, which moves the window so the singularity sits where the
  argument wants it;
* **parabolic rescaling** `(t, x) ↦ (λ²t, λx)`, which is the scaling the heat
  operator is invariant under --- time counts twice because `∂_t` and `Δ_x`
  must scale together.

Both are supplied here as honest maps with honest inverses, and
`RegularityTransport` already says regularity and the singular set travel along
them.  Before this module the framework had `RecenteringInterface` and
`RescalingInterface` but **no instance of either except the identity**, so
"recentering" was a shape with nothing in it.

The last section is the generic bridge: a symmetry that acts on the ambient,
on the windows, and on the local objects compatibly *is* a recentering
interface.  That is what lets an application register a translation once and
have the framework own every handoff along it.
-/

namespace Hypostructure.PDE.Localization

open scoped ContDiff

universe u

/-! ## A diagonal change of coordinates -/

section Diagonal

variable {dimension : ℕ}

/--
**A diagonal linear automorphism of a Euclidean space**, given by a weight that
never vanishes.  The inverse is the reciprocal weight, so no analysis is
involved.
-/
noncomputable def diagonalEquiv (weight : Fin dimension → ℝ)
    (nonzero : ∀ index, weight index ≠ 0) :
    EuclideanSpace ℝ (Fin dimension) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin dimension) where
  toFun place := WithLp.toLp 2 fun index => weight index * WithLp.ofLp place index
  invFun place :=
    WithLp.toLp 2 fun index => (weight index)⁻¹ * WithLp.ofLp place index
  map_add' _first _second := by ext index; simp [mul_add]
  map_smul' _scalar _place := by ext index; simp; ring
  left_inv _place := by
    ext index; simp [inv_mul_cancel_left₀ (nonzero index)]
  right_inv _place := by
    ext index; simp [mul_inv_cancel_left₀ (nonzero index)]

@[simp] theorem diagonalEquiv_apply (weight : Fin dimension → ℝ)
    (nonzero : ∀ index, weight index ≠ 0)
    (place : EuclideanSpace ℝ (Fin dimension)) (index : Fin dimension) :
    diagonalEquiv weight nonzero place index = weight index * place index :=
  rfl

/-- The same as a homeomorphism.  Finite dimensionality is the whole proof. -/
noncomputable def diagonalEquivL (weight : Fin dimension → ℝ)
    (nonzero : ∀ index, weight index ≠ 0) :
    EuclideanSpace ℝ (Fin dimension) ≃L[ℝ] EuclideanSpace ℝ (Fin dimension) :=
  (diagonalEquiv weight nonzero).toContinuousLinearEquiv

@[simp] theorem diagonalEquivL_apply (weight : Fin dimension → ℝ)
    (nonzero : ∀ index, weight index ≠ 0)
    (place : EuclideanSpace ℝ (Fin dimension)) (index : Fin dimension) :
    diagonalEquivL weight nonzero place index = weight index * place index :=
  rfl

end Diagonal

/-! ## Parabolic rescaling

Time is the zeroth coordinate, so it carries `scale ^ 2` and the spatial
coordinates carry `scale`.  That is precisely the scaling `∂_t - Δ_x` is
homogeneous under.
-/

section Parabolic

variable {dimension : ℕ}

/-- The parabolic weight: `scale ^ 2` on time, `scale` on space. -/
noncomputable def parabolicWeight (scale : ℝ) (index : Fin (dimension + 1)) : ℝ :=
  if index = 0 then scale ^ 2 else scale

theorem parabolicWeight_ne_zero {scale : ℝ} (nonzero : scale ≠ 0)
    (index : Fin (dimension + 1)) :
    parabolicWeight scale index ≠ 0 := by
  unfold parabolicWeight
  split
  · exact pow_ne_zero 2 nonzero
  · exact nonzero

/--
**Parabolic rescaling** `(t, x) ↦ (λ²t, λx)`, as a homeomorphism of the
Euclidean space-time.
-/
noncomputable def parabolicScaling {scale : ℝ} (nonzero : scale ≠ 0) :
    EuclideanSpace ℝ (Fin (dimension + 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (dimension + 1)) :=
  diagonalEquivL (parabolicWeight scale) (parabolicWeight_ne_zero nonzero)

@[simp] theorem parabolicScaling_time {scale : ℝ} (nonzero : scale ≠ 0)
    (place : EuclideanSpace ℝ (Fin (dimension + 1))) :
    parabolicScaling nonzero place 0 = scale ^ 2 * place 0 := by
  simp [parabolicScaling, parabolicWeight]

theorem parabolicScaling_space {scale : ℝ} (nonzero : scale ≠ 0)
    (place : EuclideanSpace ℝ (Fin (dimension + 1)))
    {index : Fin (dimension + 1)} (spatial : index ≠ 0) :
    parabolicScaling nonzero place index = scale * place index := by
  simp [parabolicScaling, parabolicWeight, spatial]

/-- **Regularity is unchanged by parabolic rescaling.** -/
theorem contDiffOn_parabolicScaling_iff {Value : Type u} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {scale : ℝ} (nonzero : scale ≠ 0)
    (field : EuclideanSpace ℝ (Fin (dimension + 1)) → Value)
    (region : Set (EuclideanSpace ℝ (Fin (dimension + 1)))) :
    ContDiffOn ℝ ∞ (fun place => field (parabolicScaling nonzero place))
        (parabolicScaling nonzero ⁻¹' region) ↔
      ContDiffOn ℝ ∞ field region :=
  RegularityTransport.contDiffOn_equiv_iff _

/-- **The singularity is carried along by parabolic rescaling.** -/
theorem singularSet_parabolicScaling {Value : Type u} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {scale : ℝ} (nonzero : scale ≠ 0)
    (field : EuclideanSpace ℝ (Fin (dimension + 1)) → Value)
    (region : Set (EuclideanSpace ℝ (Fin (dimension + 1)))) :
    PDE.singularSet (fun place => field (parabolicScaling nonzero place))
        (parabolicScaling nonzero ⁻¹' region) =
      (parabolicScaling nonzero : _ → _) ⁻¹' PDE.singularSet field region :=
  RegularityTransport.singularSet_comp_equiv _ _ _

/-- **Regularity is unchanged by recentering**, i.e. by translating the window
so a chosen point sits at the origin. -/
theorem contDiffOn_recentre_iff {Value : Type u} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (centre : EuclideanSpace ℝ (Fin (dimension + 1)))
    (field : EuclideanSpace ℝ (Fin (dimension + 1)) → Value)
    (region : Set (EuclideanSpace ℝ (Fin (dimension + 1)))) :
    ContDiffOn ℝ ∞ (fun place => field (place + centre))
        ((fun place => place + centre) ⁻¹' region) ↔
      ContDiffOn ℝ ∞ field region :=
  RegularityTransport.contDiffOn_add_const_iff centre

/-- **The singularity is carried along by recentering.**  Recentring on the
singularity therefore really does put it at the origin. -/
theorem singularSet_recentre {Value : Type u} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (centre : EuclideanSpace ℝ (Fin (dimension + 1)))
    (field : EuclideanSpace ℝ (Fin (dimension + 1)) → Value)
    (region : Set (EuclideanSpace ℝ (Fin (dimension + 1)))) :
    PDE.singularSet (fun place => field (place + centre))
        ((fun place => place + centre) ⁻¹' region) =
      (fun place => place + centre) ⁻¹' PDE.singularSet field region :=
  RegularityTransport.singularSet_comp_add_const _ _ _

end Parabolic

/-! ## A symmetry is a recentering interface

`RecenteringInterface` asks for a family of realized coordinates indexed by a
shift.  A symmetry that acts compatibly on ambients, windows and local objects
supplies exactly that, so an application registers the action once and the
framework owns every handoff along it.
-/

/--
**A symmetry of a local model.**

`act` moves the ambient object, `window` moves the window, and `transform`
moves the local object; `realizes` is the single compatibility law tying them
together, and it is the same law `RealizedCoordinate.realizes` states.
-/
structure WindowSymmetry (M : PDE.LocalModel.{u}) where
  /-- The shifts available. -/
  Shift : Type u
  /-- How a shift moves an ambient object. -/
  act : Shift → M.problem.Ambient → M.problem.Ambient
  /-- How a shift moves a window. -/
  window : Shift → M.atlas.Window → M.atlas.Window
  /-- How a shift moves a local object. -/
  transform : ∀ (shift : Shift) (source : M.atlas.Window),
    M.atlas.LocalObject source → M.atlas.LocalObject (window shift source)
  /-- How a shift moves the equation data. -/
  transformEquation : ∀ (shift : Shift) (source : M.atlas.Window)
    {object : M.atlas.LocalObject source},
    M.equation.EquationData source object →
      M.equation.EquationData (window shift source) (transform shift source object)
  /-- A moved solution is a solution: the equation is symmetric under the
  action. -/
  preservesEquation : ∀ (shift : Shift) (source : M.atlas.Window)
    {object : M.atlas.LocalObject source}
    (data : M.equation.EquationData source object),
    M.equation.satisfies data →
      M.equation.satisfies (transformEquation shift source data)
  /-- Moving then restricting is restricting then moving. -/
  realizes : ∀ (shift : Shift) (object : M.problem.Ambient)
    (source : M.atlas.Window),
    transform shift source (M.atlas.restrict object source) =
      M.atlas.restrict (act shift object) (window shift source)
  /-- A moved object still satisfies the baseline. -/
  preservesBaseline : ∀ (shift : Shift) {object : M.problem.Ambient},
    M.problem.Baseline object → M.problem.Baseline (act shift object)

namespace WindowSymmetry

variable {M : PDE.LocalModel.{u}} (symmetry : WindowSymmetry M)

/-- The realized coordinate of one shift at one window. -/
def coordinate (shift : symmetry.Shift) (source : M.atlas.Window) :
    PDE.RealizedCoordinate M source (symmetry.window shift source) where
  transform := symmetry.transform shift source
  transformEquation := symmetry.transformEquation shift source
  preservesEquation := symmetry.preservesEquation shift source
  realize := symmetry.act shift
  realizes := fun object => symmetry.realizes shift object source
  preservesBaseline := symmetry.preservesBaseline shift

/--
**The recentering interface a symmetry induces.**

This is the first non-identity `RecenteringInterface` the framework has: every
earlier instance was the identity in a fixture.  With it, `TailFocus`,
`RepresentedTail.recenter` and the whole handoff machinery become usable at a
real change of coordinates.
-/
def recenteringInterface : PDE.RecenteringInterface M where
  Shift := symmetry.Shift
  targetWindow := symmetry.window
  coordinate := fun shift source => symmetry.coordinate shift source

@[simp] theorem recenteringInterface_targetWindow
    (shift : symmetry.Shift) (source : M.atlas.Window) :
    symmetry.recenteringInterface.targetWindow shift source =
      symmetry.window shift source := rfl

/-- The same symmetry read as a rescaling interface, for the scale-indexed
half of a parabolic handoff. -/
def rescalingInterface : PDE.RescalingInterface M where
  Scale := symmetry.Shift
  targetWindow := symmetry.window
  coordinate := fun shift source => symmetry.coordinate shift source

@[simp] theorem rescalingInterface_targetWindow
    (shift : symmetry.Shift) (source : M.atlas.Window) :
    symmetry.rescalingInterface.targetWindow shift source =
      symmetry.window shift source := rfl

end WindowSymmetry

end Hypostructure.PDE.Localization
