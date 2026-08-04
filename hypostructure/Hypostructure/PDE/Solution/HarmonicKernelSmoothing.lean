import Hypostructure.PDE.Solution.ScaleRecombination
import Hypostructure.PDE.Solution.PressureNormalization
import Hypostructure.PDE.Distribution.CurlCalculus

/-!
# The parasitic mode is smooth exactly when its time derivatives keep their grade

`stokes:rem:parasitic-counterexample` is the reason every pressure-free route to
velocity regularity fails: `u = a(t) ∇ψ(x)` with `ψ` spatially harmonic and `a`
merely `L²` has `curl u = 0`, `div u = 0`, `Δ_x u = 0`, and solves the balance
with `f = 0` and `p = −a'(t) ψ`.  Nothing built from the vorticity, the div--curl
identity or the spatial Poisson equation can exclude it, because it satisfies
all of them.

This module isolates what *does* exclude it, and the answer is a statement about
**grades**, not about ellipticity.

A spatially harmonic state is spatially smooth on the window at its own grade —
that is `spatialSmoothOn_of_spatialLaplacian_smoothOn` with a vanishing source.
So the harmonic kernel already has every spatial derivative.  What it does not
have is time regularity, and
`ScaleRecombination.smoothOn_of_spatialSmoothOn_timeDerivIterate` says exactly
what would buy it: spatial smoothness of **every** time derivative *at one fixed
base grade*.

That fixed grade is the whole content.  Differentiating in time normally costs a
grade, so `∂_t^k v` sits at `grade − k` and the tower cannot be fed — which is
correct, since otherwise the counterexample would be smooth.  The hypothesis is
therefore not automatic and cannot be, and
`SpatiallyHarmonicTower` below names it: the tower of time derivatives stays at
one grade.

**Where such a tower comes from.**  The harmonic kernel of a normalized solution
is `v = −proj_{𝓗(B)} w` for a smooth `w`, and `proj_{𝓗(B)}` is a *time
independent* orthogonal projection, so `∂_t^k v = −proj_{𝓗(B)}(∂_t^k w)` and
`‖∂_t^k v‖ ≤ ‖∂_t^k w‖`: bounded, at grade `0`, for every `k`.  Time
independence of the projection is the same property
`Distribution/Recovery.SliceRecovery` carries, and it is the property the
appendix uses in `stokes:lem:time-param-quotient`.  A construction of that
projection is not in this module; what is here is the theorem that consumes it,
so that once the projection is registered nothing further is asked of an
application.
-/

namespace Hypostructure.PDE.Solution.HarmonicKernelSmoothing

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.SliceRestriction
open Hypostructure.PDE.Solution.ScaleRecombination
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Distribution.CurlCalculus
open scoped SchwartzMap Real LineDeriv Laplacian

set_option linter.unusedSectionVars false

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-! ## Spatial harmonicity is spatial smoothness -/

/--
**A spatially harmonic state is spatially smooth on the window, at its own
grade.**

No ellipticity in the time direction is claimed and none is available; this is
`spatialSmoothOn_of_spatialLaplacian_smoothOn` read with a vanishing source.
-/
theorem spatialSmoothOn_of_spatialHarmonic (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (held : SobolevOn region grade state)
    (harmonic : spatialLaplacian basis timeIndex state = 0) :
    SpatialSmoothOn basis timeIndex region grade state :=
  spatialSmoothOn_of_spatialLaplacian_smoothOn basis timeIndex held
    (by rw [harmonic]; exact PressureNormalization.smoothOn_zero)

/-! ## The spatial Laplacian passes through time derivatives -/

/-- Second derivatives in fixed directions commute with a time derivative, so
the spatial Laplacian does. -/
theorem spatialLaplacian_lineDerivOp (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (direction : Point) (state : 𝓢'(Point, Value)) :
    spatialLaplacian basis timeIndex (∂_{direction} state) =
      ∂_{direction} (spatialLaplacian basis timeIndex state) := by
  simp only [spatialLaplacian]
  rw [lineDerivOp_finset_sum]
  refine Finset.sum_congr rfl fun index _ => ?_
  rw [lineDerivOp_comm (basis index) direction state,
    lineDerivOp_comm (basis index) direction (∂_{basis index} state)]

/-- …and therefore through every iterated time derivative. -/
theorem spatialLaplacian_timeDerivIterate (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    ∀ (order : ℕ) (state : 𝓢'(Point, Value)),
      spatialLaplacian basis timeIndex (timeDerivIterate basis timeIndex order state) =
        timeDerivIterate basis timeIndex order (spatialLaplacian basis timeIndex state) := by
  intro order
  induction order with
  | zero => intro state; simp only [timeDerivIterate_zero]
  | succ previous gained =>
      intro state
      rw [timeDerivIterate_succ_inner, timeDerivIterate_succ_inner, gained,
        spatialLaplacian_lineDerivOp]

/-- A spatially harmonic state stays spatially harmonic under time
differentiation. -/
theorem spatialLaplacian_timeDerivIterate_eq_zero
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {state : 𝓢'(Point, Value)}
    (harmonic : spatialLaplacian basis timeIndex state = 0) (order : ℕ) :
    spatialLaplacian basis timeIndex
        (timeDerivIterate basis timeIndex order state) = 0 := by
  rw [spatialLaplacian_timeDerivIterate basis timeIndex order state, harmonic]
  clear harmonic
  induction order with
  | zero => simp only [timeDerivIterate_zero]
  | succ previous gained =>
      rw [timeDerivIterate_succ_outer, gained]
      exact map_zero _

/-! ## The closure

`SpatiallyHarmonicTower` is the hypothesis that is not automatic, stated once.
Everything below consumes it and nothing reproves it.
-/

/--
**The tower a normalized harmonic kernel carries**: spatially harmonic, and
every time derivative held at *one* Sobolev grade.

The second clause is the whole strength.  Dropping it makes the structure
satisfiable by `a(t) ∇ψ(x)` with `a ∈ L²`, which is not smooth, so no weakening
of it can be sound.  A time-independent orthogonal projection supplies it with
`grade = 0` and no loss, because `‖proj (∂_t^k w)‖ ≤ ‖∂_t^k w‖`.
-/
structure SpatiallyHarmonicTower (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (region : Set Point) (grade : ℝ)
    (state : 𝓢'(Point, Value)) : Prop where
  /-- The state is spatially harmonic. -/
  harmonic : spatialLaplacian basis timeIndex state = 0
  /-- Every time derivative is held at the *same* grade. -/
  held : ∀ order : ℕ, SobolevOn region grade
    (timeDerivIterate basis timeIndex order state)

namespace SpatiallyHarmonicTower

variable {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}

/--
**The parasitic mode is smooth.**

Spatial harmonicity gives every spatial derivative of every time derivative, all
at the one grade the tower fixes, and
`smoothOn_of_spatialSmoothOn_timeDerivIterate` recombines them.  This is the
single step that the counterexample survives only by failing the grade
hypothesis.
-/
theorem smoothOn (tower : SpatiallyHarmonicTower basis timeIndex region grade state) :
    SmoothOn region state :=
  smoothOn_of_spatialSmoothOn_timeDerivIterate basis timeIndex fun order =>
    spatialSmoothOn_of_spatialHarmonic basis timeIndex (tower.held order)
      (spatialLaplacian_timeDerivIterate_eq_zero basis timeIndex tower.harmonic order)

/-- A tower restricts to a smaller window. -/
theorem mono_region {smaller : Set Point} (subset : smaller ⊆ region)
    (tower : SpatiallyHarmonicTower basis timeIndex region grade state) :
    SpatiallyHarmonicTower basis timeIndex smaller grade state where
  harmonic := tower.harmonic
  held := fun order => (tower.held order).mono_region subset

end SpatiallyHarmonicTower

/-! ## Building the tower from the div--curl data

The kernel of the local Hodge quotient is presented as a divergence-free
curl-free field, not as a spatially harmonic one.  `curl_curl` converts.
-/

/--
**A divergence-free curl-free field is spatially harmonic**, componentwise.

`Δ v = ∇(div v) − curl curl v` is `curl_curl`, and both terms vanish; the frame
Laplacian is the spatial one by reindexing alone
(`scalarLaplacian_eq_spatialLaplacian_of_card_eq_four`), so no time direction is
involved.
-/
theorem spatialLaplacian_eq_zero_of_divergence_free_of_curl_free
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {kernel : Fin 3 → 𝓢'(Point, Value)}
    (divergence_free :
      divergence (fun axis => basis (spatialIndex axis)) kernel = 0)
    (curl_free : curl (fun axis => basis (spatialIndex axis)) kernel = 0)
    (index : Fin 3) :
    spatialLaplacian basis timeIndex (kernel index) = 0 := by
  set frame : Fin 3 → Point := fun axis => basis (spatialIndex axis) with frame_def
  have expand := congrFun (curl_curl (frame := frame) kernel) index
  have rearranged :
      laplacian frame kernel index =
        gradient frame (divergence frame kernel) index -
          curl frame (curl frame kernel) index := by
    rw [expand]
    simp only [Pi.sub_apply]
    abel
  have gradient_zero : gradient frame (divergence frame kernel) index = 0 := by
    rw [divergence_free]
    simpa using
      (map_zero (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Point, Value) (frame index)))
  have curl_zero : curl frame (curl frame kernel) index = 0 := by
    rw [curl_free]
    simpa using congrFun (curl_zero (frame := frame) (Value := Value)) index
  have vanishes : laplacian frame kernel index = 0 := by
    rw [rearranged, gradient_zero, curl_zero, sub_zero]
  have identify : laplacian frame kernel index =
      spatialLaplacian basis timeIndex (kernel index) :=
    scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex spatialIndex
      injective avoidsTime dimension (kernel index)
  rw [← identify, vanishes]

/--
**The tower of a divergence-free curl-free kernel**, in the shape the local
Hodge quotient delivers it.
-/
theorem spatiallyHarmonicTower_of_divergence_free_of_curl_free
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {region : Set Point} {grade : ℝ} {kernel : Fin 3 → 𝓢'(Point, Value)}
    (divergence_free :
      divergence (fun axis => basis (spatialIndex axis)) kernel = 0)
    (curl_free : curl (fun axis => basis (spatialIndex axis)) kernel = 0)
    (held : ∀ (order : ℕ) (index : Fin 3), SobolevOn region grade
      (timeDerivIterate basis timeIndex order (kernel index)))
    (index : Fin 3) :
    SpatiallyHarmonicTower basis timeIndex region grade (kernel index) where
  harmonic := spatialLaplacian_eq_zero_of_divergence_free_of_curl_free basis timeIndex
    spatialIndex injective avoidsTime dimension divergence_free curl_free index
  held := fun order => held order index

/-! ## The payoff -/

/--
**The velocity is smooth once the quotient is smooth and the kernel carries a
tower.**

This is `stokes:lem:velocity-recovery`'s last sentence — *"if the
harmonic-kernel component is smooth, then `u = u^⊥ + proj u` is smooth"* — with
the smoothness of the kernel replaced by the grade hypothesis that actually
produces it.  The quotient half is
`QuotientVelocityRegularity.smoothOn_quotient_of_balance`, which needs no
pressure; the kernel half is the tower.
-/
theorem smoothOn_of_quotient_of_tower
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {region : Set Point} {grade : ℝ}
    {velocity quotient kernel : Fin 3 → 𝓢'(Point, Value)}
    (decomposition : velocity = quotient + kernel)
    (quotient_smooth : ∀ index, SmoothOn region (quotient index))
    (tower : ∀ index,
      SpatiallyHarmonicTower basis timeIndex region grade (kernel index))
    (index : Fin 3) :
    SmoothOn region (velocity index) := by
  have expand : velocity index = quotient index + kernel index := by
    rw [decomposition]
    rfl
  rw [expand]
  exact (quotient_smooth index).add (tower index).smoothOn

/--
**The same on nested balls**, in the shape a residual carrying a window pair
consumes.
-/
theorem smoothOn_ball_of_quotient_of_tower
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (center : Point)
    {innerRadius outerRadius : ℝ} (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {velocity quotient kernel : Fin 3 → 𝓢'(Point, Value)}
    (decomposition : velocity = quotient + kernel)
    (quotient_smooth : ∀ index, SmoothOn (ball center innerRadius) (quotient index))
    (tower : ∀ index, SpatiallyHarmonicTower basis timeIndex
      (ball center outerRadius) grade (kernel index))
    (index : Fin 3) :
    SmoothOn (ball center innerRadius) (velocity index) :=
  smoothOn_of_quotient_of_tower basis timeIndex decomposition quotient_smooth
    (fun component =>
      (tower component).mono_region (ball_subset_ball nested)) index

end Hypostructure.PDE.Solution.HarmonicKernelSmoothing
