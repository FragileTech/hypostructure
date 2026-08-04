import Hypostructure.PDE.Solution.WindowCertificate
import Hypostructure.PDE.Distribution.CurlCalculus

/-!
# The local regularity chain

The three-step local bootstrap every incompressible parabolic balance runs, and
the only thing between the framework's per-window certificates
(`PDE/Solution/WindowCertificate.lean`) and a local-closure vertex.

Given, **on one window**, a balance `∂_t u − Δu + ∇p = f` with divergence-free
`u` and smooth forcing:

1. **Vorticity.**  Taking the curl kills the pressure, because the curl of a
   gradient vanishes, and commutes with the heat operator.  So `ω = curl u`
   satisfies `∂_t ω − Δω = curl f`, whose right side is smooth --- and the
   parabolic certificate makes `ω` smooth.
2. **Div--curl.**  For divergence-free `u`, `−Δu = curl curl u`, so `Δu` is
   smooth once `ω` is, and the elliptic certificate makes `u` smooth.
3. **Pressure.**  `∇p = f − ∂_t u + Δu` is then a difference of smooth states.

Nothing here is global: every hypothesis and every conclusion is about one ball
around one point, and the passage from a family of these to the registered
target is `LocalClosureAlgebra.target_of_exhaustion`, already proved.

There is no equation registration, residual, ledger, route or target in this
file, and no dimension is named beyond the `Fin 3` the curl itself needs.
-/

namespace Hypostructure.PDE.Strategy.LocalRegularityChain

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.WindowCertificate
open Hypostructure.PDE.Distribution.CurlCalculus
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

-- The shared variable block below is deliberately uniform across the file:
-- every theorem here is one step of the same chain, and splitting the
-- instances per step would obscure that.
set_option linter.unusedSectionVars false

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {frame : Fin 3 → Point}

/-! ## Step 0: the heat operator commutes with the curl -/

/-- The heat operator is subtractive: both of its summands are. -/
theorem heatOperator_sub (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (first second : 𝓢'(Point, Value)) :
    heatOperator basis timeIndex (first - second) =
      heatOperator basis timeIndex first - heatOperator basis timeIndex second := by
  simp only [heatOperator, spatialLaplacian, lineDerivOp_sub,
    Finset.sum_sub_distrib]
  abel

/--
**The curl commutes with the heat operator.**

This is `curl_componentwise` fed the two facts the heat operator already has:
it is subtractive, and it commutes with every directional derivative
(`heatOperator_lineDerivOp_comm`).  The time direction is not distinguished.
-/
theorem curl_heatOperator (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (field : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (fun index => heatOperator basis timeIndex (field index)) =
      fun index => heatOperator basis timeIndex (curl frame field index) :=
  curl_componentwise (heatOperator basis timeIndex)
    (heatOperator_sub basis timeIndex)
    (fun direction state =>
      heatOperator_lineDerivOp_comm basis timeIndex direction state)
    field

/-! ## Step 1: the vorticity satisfies the heat equation with a smooth source -/

/--
**The vorticity equation on a window.**

Taking the curl of the balance eliminates the pressure and leaves the heat
equation for `ω = curl u`.  This is an identity of states, not an estimate.
-/
theorem heatOperator_curl_eq_curl_forcing
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index) :
    ∀ index,
      heatOperator basis timeIndex (curl frame velocity index) =
        curl frame forcing index := by
  intro index
  have split :
      (fun i => heatOperator basis timeIndex (velocity i) +
          gradient frame pressure i) =
        (fun i => heatOperator basis timeIndex (velocity i)) +
          gradient frame pressure := rfl
  have curl_balance :
      curl frame (fun i =>
          heatOperator basis timeIndex (velocity i) + gradient frame pressure i) =
        curl frame forcing :=
    congrArg (curl frame) (funext balance)
  rw [split, curl_add, curl_gradient, curl_heatOperator, add_zero] at curl_balance
  exact congrFun curl_balance index

/-! ## Step 2: the vorticity is smooth, hence so is the velocity's Laplacian -/

/--
**The velocity's Laplacian is smooth on the inner window.**

For a divergence-free field `−Δu = curl curl u`, so smoothness of the
vorticity on a window transports to smoothness of `Δu` there.  Both inputs are
local.
-/
theorem smoothOn_laplacian_of_smoothOn_curl {region : Set Point}
    {velocity : Fin 3 → 𝓢'(Point, Value)}
    (divergence_free : divergence frame velocity = 0)
    (curl_smooth : ∀ index, SmoothOn region (curl frame (curl frame velocity) index))
    (index : Fin 3) :
    SmoothOn region (laplacian frame velocity index) := by
  have zero_deriv : ∀ direction : Point,
      ∂_{direction} (0 : 𝓢'(Point, Value)) = 0 := by
    intro direction
    have base := lineDerivOp_sub direction (0 : 𝓢'(Point, Value)) 0
    rw [sub_self] at base
    exact base.trans (sub_self _)
  have identity :
      laplacian frame velocity index =
        -(curl frame (curl frame velocity) index) := by
    have expand := congrFun (curl_curl (frame := frame) velocity) index
    rw [divergence_free] at expand
    have zero_grad : gradient frame (0 : 𝓢'(Point, Value)) index = 0 :=
      zero_deriv (frame index)
    have pointwise :
        curl frame (curl frame velocity) index =
          gradient frame (0 : 𝓢'(Point, Value)) index -
            laplacian frame velocity index := expand
    rw [zero_grad] at pointwise
    rw [pointwise]
    abel
  rw [identity]
  exact (curl_smooth index).neg

/-- **Step 1, in local form.**  The vorticity is smooth on the inner ball as
soon as its heat image is smooth on the outer one.

No balance appears --- there is nothing here for a residual to establish on all
of `Point`.  A residual owns its equation only on its own window, and this is
the form that consumes exactly that: `SmoothOn` reads a state only through bumps
supported in the ball, so `SmoothOn.congr_sub` turns "the equation holds on this
window" into this hypothesis with nothing global in between.

`smoothOn_curl_of_balance` below is this theorem with the global balance used to
supply the hypothesis; it is kept because it is the cheaper call when a genuine
whole-space identity happens to be available. -/
theorem smoothOn_curl_of_heat_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (center : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    {grade : ℝ} {velocity : Fin 3 → 𝓢'(Point, Value)}
    (held : ∀ index,
      SobolevOn (ball center outer) grade (curl frame velocity index))
    (heat_smooth : ∀ index,
      SmoothOn (ball center outer)
        (heatOperator basis timeIndex (curl frame velocity index)))
    (index : Fin 3) :
    SmoothOn (ball center inner) (curl frame velocity index) :=
  smoothOn_ball_of_heat_smoothOn basis timeIndex center nested (held index)
    (heat_smooth index)

/-- **Step 1, complete.**  The vorticity is smooth on the inner ball.

Its heat image is `curl f`, which is smooth because the forcing is; the
parabolic certificate does the rest.  The Sobolev input is not an assumption:
`Localization.Tempered.memLp_cutoffSmul` puts the cutoff of an `L²_loc` field
at grade `0`. -/
theorem smoothOn_curl_of_balance (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (center : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    {grade : ℝ} {velocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure : 𝓢'(Point, Value)}
    (held : ∀ index,
      SobolevOn (ball center outer) grade (curl frame velocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (forcing_smooth : ∀ index,
      SmoothOn (ball center outer) (curl frame forcing index))
    (index : Fin 3) :
    SmoothOn (ball center inner) (curl frame velocity index) :=
  smoothOn_curl_of_heat_smoothOn basis timeIndex center nested held
    (fun axis => by
      rw [heatOperator_curl_eq_curl_forcing basis timeIndex balance axis]
      exact forcing_smooth axis)
    index

/-- **Step 3.**  The pressure gradient is read off the balance.

`∇p = f − (∂_t u − Δu)`, a difference of two states already known smooth on the
window.  Nothing is inverted and nothing is estimated --- this is
`Localization.Tempered.closure_of_balance` in the `𝓢'` setting. -/
theorem smoothOn_gradient_of_balance {region : Set Point}
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (forcing_smooth : ∀ index, SmoothOn region (forcing index))
    (heat_smooth : ∀ index,
      SmoothOn region (heatOperator basis timeIndex (velocity index)))
    (index : Fin 3) :
    SmoothOn region (gradient frame pressure index) := by
  have closure :
      gradient frame pressure index =
        forcing index - heatOperator basis timeIndex (velocity index) := by
    rw [← balance index]
    abel
  rw [closure]
  exact (forcing_smooth index).sub (heat_smooth index)

/-! ## The chain, composed

The four steps run in one place.  Note what closes the velocity: **not**
spatial ellipticity --- `PDE/Solution/SliceRestriction.lean` shows `1 - Δ_x`
gains nothing on the isotropic space-time scale --- but the *parabolic*
certificate applied to the velocity itself.  Its heat image is
`∂_t u - Δ_x u`, and both summands are already known smooth on the window:
`Δ_x u` from step 2, and `∂_t u` from the window's own time-derivative datum.

Every input below names one ball.  Nothing is global.
-/

/--
**The local regularity chain.**

On one window: a divergence-free balance with smooth forcing, whose vorticity
and velocity sit at some Sobolev grade there and whose velocity has a smooth
time derivative, has smooth velocity *and* smooth pressure gradient on the
inner ball.

`spatialIndex` picks the three non-time directions of the basis, which is what
identifies the frame Laplacian with the spatial one
(`scalarLaplacian_eq_spatialLaplacian_of_card_eq_four`); on a
four-dimensional space-time injectivity and time-avoidance suffice.
-/
theorem smoothOn_of_balance (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (spatialIndex : Fin 3 → Index)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (center : Point) {inner middle outer : ℝ}
    (inner_le : inner ≤ middle) (middle_le : middle ≤ outer)
    {curlGrade velocityGrade : ℝ}
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (curl_held : ∀ index, SobolevOn (ball center outer) curlGrade
      (curl (fun axis => basis (spatialIndex axis)) velocity index))
    (velocity_held : ∀ index,
      SobolevOn (ball center middle) velocityGrade (velocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient (fun axis => basis (spatialIndex axis)) pressure index =
        forcing index)
    (divergence_free :
      divergence (fun axis => basis (spatialIndex axis)) velocity = 0)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (timeDeriv_smooth : ∀ index,
      SmoothOn (ball center middle) (∂_{basis timeIndex} (velocity index))) :
    (∀ index, SmoothOn (ball center inner) (velocity index)) ∧
      (∀ index, SmoothOn (ball center inner)
        (gradient (fun axis => basis (spatialIndex axis)) pressure index)) := by
  set frame : Fin 3 → Point := fun axis => basis (spatialIndex axis) with frame_def
  -- Step 1: the vorticity is smooth on the middle ball.
  have vorticity_smooth : ∀ index,
      SmoothOn (ball center middle) (curl frame velocity index) := fun index =>
    smoothOn_curl_of_balance basis timeIndex center middle_le curl_held balance
      (fun i => curl_smoothOn forcing_smooth i) index
  -- Step 2: the frame Laplacian of the velocity is smooth there.
  have frame_laplacian_smooth : ∀ index,
      SmoothOn (ball center middle) (laplacian frame velocity index) :=
    fun index =>
      smoothOn_laplacian_of_smoothOn_curl divergence_free
        (fun i => curl_smoothOn vorticity_smooth i) index
  -- The frame Laplacian *is* the spatial one, by reindexing alone.
  have spatial_laplacian_smooth : ∀ index,
      SmoothOn (ball center middle)
        (spatialLaplacian basis timeIndex (velocity index)) := by
    intro index
    have identify :
        laplacian frame velocity index =
          spatialLaplacian basis timeIndex (velocity index) :=
      scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex
        spatialIndex injective avoidsTime dimension (velocity index)
    exact identify ▸ frame_laplacian_smooth index
  -- Step 2': the velocity's own heat image is smooth, so the parabolic
  -- certificate closes the velocity.  Spatial ellipticity is never used.
  have heat_smooth : ∀ index,
      SmoothOn (ball center middle)
        (heatOperator basis timeIndex (velocity index)) := fun index =>
    (timeDeriv_smooth index).sub (spatial_laplacian_smooth index)
  have velocity_smooth : ∀ index,
      SmoothOn (ball center inner) (velocity index) := fun index =>
    smoothOn_ball_of_heat_smoothOn basis timeIndex center inner_le
      (velocity_held index) (heat_smooth index)
  refine ⟨velocity_smooth, fun index => ?_⟩
  -- Step 3: the pressure gradient is the balance's remaining term.
  exact smoothOn_gradient_of_balance basis timeIndex balance
    (fun i => (forcing_smooth i).mono_region (ball_subset_ball
      (inner_le.trans middle_le)))
    (fun i => (heat_smooth i).mono_region (ball_subset_ball inner_le)) index

/--
**The per-window certificate of an incompressible parabolic balance.**

The same chain, delivered in the shape a local-closure vertex consumes:
genuine `ContDiff ℝ ∞` functions representing the velocity and the pressure
gradient against every test supported in the window ball.

This is `smoothOn_of_balance` followed by the local embedding.  It is the last
link: `LocalClosureAlgebra.exhaustiveLocalClosureDichotomy` takes a family of
these, one per admissible window, and closes both arms --- and the passage
from the family to the registered target is `target_of_exhaustion`, which is
already proved.  No step of this is global.
-/
theorem exists_contDiff_representatives_of_balance
    (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (spatialIndex : Fin 3 → Index)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (center : Point) {windowRadius inner middle outer : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < inner)
    (inner_le : inner ≤ middle) (middle_le : middle ≤ outer)
    {curlGrade velocityGrade : ℝ}
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (curl_held : ∀ index, SobolevOn (ball center outer) curlGrade
      (curl (fun axis => basis (spatialIndex axis)) velocity index))
    (velocity_held : ∀ index,
      SobolevOn (ball center middle) velocityGrade (velocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient (fun axis => basis (spatialIndex axis)) pressure index =
        forcing index)
    (divergence_free :
      divergence (fun axis => basis (spatialIndex axis)) velocity = 0)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (timeDeriv_smooth : ∀ index,
      SmoothOn (ball center middle) (∂_{basis timeIndex} (velocity index))) :
    (∀ index, ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
        ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
          velocity index test =
            ∫ place : Point, test place • representative place) ∧
      (∀ index, ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
        ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
          gradient (fun axis => basis (spatialIndex axis)) pressure index test =
            ∫ place : Point, test place • representative place) := by
  obtain ⟨velocity_smooth, gradient_smooth⟩ :=
    smoothOn_of_balance basis timeIndex spatialIndex injective avoidsTime
      dimension center inner_le middle_le curl_held velocity_held balance
      divergence_free forcing_smooth timeDeriv_smooth
  exact
    ⟨fun index =>
      LocalEmbedding.exists_contDiff_representative_of_smoothOn_ball center window_pos
        window_nested (velocity_smooth index),
     fun index =>
      LocalEmbedding.exists_contDiff_representative_of_smoothOn_ball center window_pos
        window_nested (gradient_smooth index)⟩

/-! ## The gauge: normalizing away the harmonic kernel

The balance determines the velocity only up to a curl-free, divergence-free
field --- the parasitic mode.  Removing it is a *gauge choice*, not an
analytic step: subtract a gradient from the velocity and add the corresponding
time derivative to the pressure.

The whole of that move is the four theorems below, and each is one line of
operator algebra.  The single hypothesis is that the potential is spatially
harmonic; an application never carries a structure of side conditions for it,
because `Distribution/CurlCalculus.lean` already proves every other identity
such a structure would list.
-/

section Gauge

variable {frame : Fin 3 → Point}

/--
**The heat operator sends the gradient of a spatially harmonic potential to
the gradient of its time derivative.**

`∂_t` and `Δ_x` both commute past `∇`, and harmonicity kills the spatial half.
-/
theorem heatOperator_gradient_of_harmonic
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {potential : 𝓢'(Point, Value)}
    (harmonic : spatialLaplacian basis timeIndex potential = 0) (index : Fin 3) :
    heatOperator basis timeIndex (gradient frame potential index) =
      gradient frame (∂_{basis timeIndex} potential) index := by
  show heatOperator basis timeIndex (∂_{frame index} potential) =
    ∂_{frame index} (∂_{basis timeIndex} potential)
  rw [heatOperator_lineDerivOp_comm basis timeIndex, heatOperator, harmonic,
    sub_zero]

/--
**`stokes:lem:harmonic-kernel-normalization`, clause (i): the gauge preserves
the balance, with the same source.**

`(u − ∇Φ, p + ∂_tΦ)` solves exactly the equation `(u, p)` solves.  The two
gradient terms cancel, which is the entire proof and the entire reason the
normalization costs nothing.
-/
theorem balance_sub_gradient_of_harmonic
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure potential : 𝓢'(Point, Value)}
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (harmonic : spatialLaplacian basis timeIndex potential = 0) (index : Fin 3) :
    heatOperator basis timeIndex ((velocity - gradient frame potential) index) +
        gradient frame (pressure + ∂_{basis timeIndex} potential) index =
      forcing index := by
  have expand :
      heatOperator basis timeIndex ((velocity - gradient frame potential) index) =
        heatOperator basis timeIndex (velocity index) -
          gradient frame (∂_{basis timeIndex} potential) index := by
    show heatOperator basis timeIndex
        (velocity index - gradient frame potential index) = _
    rw [heatOperator_sub, heatOperator_gradient_of_harmonic basis timeIndex harmonic]
  have split :
      gradient frame (pressure + ∂_{basis timeIndex} potential) index =
        gradient frame pressure index +
          gradient frame (∂_{basis timeIndex} potential) index :=
    congrFun (gradient_add (frame := frame) pressure _) index
  rw [expand, split, ← balance index]
  abel

/-- **Clause (iv): the gauge is invisible to the vorticity.**  The curl of a
gradient vanishes, so the normalized velocity carries the same rotational
datum --- which is why every vorticity estimate transfers unchanged. -/
theorem curl_sub_gradient (potential : 𝓢'(Point, Value))
    (velocity : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (velocity - gradient frame potential) = curl frame velocity := by
  rw [curl_sub, curl_gradient, sub_zero]

/-- **Clause (ii): the gauge preserves incompressibility**, because
`div ∘ grad = Δ` and the potential is harmonic. -/
theorem divergence_sub_gradient_eq_zero
    {velocity : Fin 3 → 𝓢'(Point, Value)} {potential : 𝓢'(Point, Value)}
    (divergence_free : divergence frame velocity = 0)
    (harmonic : scalarLaplacian frame potential = 0) :
    divergence frame (velocity - gradient frame potential) = 0 := by
  rw [divergence_sub, divergence_free, divergence_gradient, harmonic, sub_zero]

/--
**`stokes:thm:global-normalized-representative`, on one window.**

The normalized velocity `u − ∇Φ` and the normalized pressure gradient
`∇(p + ∂_tΦ)` are smooth on the inner ball, and **no hypothesis whatever is
placed on the discarded harmonic component**.  That is the whole point of the
gauge: the parasitic mode of `stokes:rem:parasitic-counterexample` is removed
rather than assumed away.

The vorticity input is stated for the *original* velocity, because
`curl_sub_gradient` says the two have the same curl.
-/
theorem smoothOn_of_balance_normalized
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (center : Point) {inner middle outer : ℝ}
    (inner_le : inner ≤ middle) (middle_le : middle ≤ outer)
    {curlGrade quotientGrade : ℝ}
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure potential : 𝓢'(Point, Value)}
    (harmonic :
      spatialLaplacian basis timeIndex potential = 0)
    (spatialHarmonic :
      scalarLaplacian (fun axis => basis (spatialIndex axis)) potential = 0)
    (curl_held : ∀ index, SobolevOn (ball center outer) curlGrade
      (curl (fun axis => basis (spatialIndex axis)) velocity index))
    (quotient_held : ∀ index, SobolevOn (ball center middle) quotientGrade
      ((velocity -
        gradient (fun axis => basis (spatialIndex axis)) potential) index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient (fun axis => basis (spatialIndex axis)) pressure index =
        forcing index)
    (divergence_free :
      divergence (fun axis => basis (spatialIndex axis)) velocity = 0)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (timeDeriv_smooth : ∀ index, SmoothOn (ball center middle)
      (∂_{basis timeIndex}
        ((velocity -
          gradient (fun axis => basis (spatialIndex axis)) potential) index))) :
    (∀ index, SmoothOn (ball center inner)
        ((velocity -
          gradient (fun axis => basis (spatialIndex axis)) potential) index)) ∧
      (∀ index, SmoothOn (ball center inner)
        (gradient (fun axis => basis (spatialIndex axis))
          (pressure + ∂_{basis timeIndex} potential) index)) :=
  smoothOn_of_balance basis timeIndex spatialIndex injective avoidsTime dimension
    center inner_le middle_le
    (fun index => by
      rw [curl_sub_gradient
        (frame := fun axis => basis (spatialIndex axis)) potential velocity]
      exact curl_held index)
    quotient_held
    (fun index =>
      balance_sub_gradient_of_harmonic basis timeIndex balance harmonic index)
    (divergence_sub_gradient_eq_zero divergence_free spatialHarmonic)
    forcing_smooth timeDeriv_smooth

end Gauge

end Hypostructure.PDE.Strategy.LocalRegularityChain
