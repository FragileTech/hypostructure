import Hypostructure.PDE.Solution.InteriorRegularity
import Hypostructure.PDE.Solution.ParabolicRegularity
import Hypostructure.PDE.Solution.LocalEmbedding

/-!
# The per-window classical certificate

This module composes, once and for every PDE, the framework's local bootstrap
into the single statement a local-closure vertex consumes: **on one window, a
state whose elliptic or parabolic source is smooth there has a classical
`ContDiff ℝ ∞` representative on the inner window.**

Nothing here is global.  Every hypothesis and every conclusion speaks about one
ball around one point:

* the state sits at *some* Sobolev grade on the outer ball --- for a tempered
  state this is not an assumption at all, it is
  `Solution.FiniteOrder.mem_sobolev_of_fourier_eq_integral`;
* its source is smooth on that same outer ball --- for a represented equation
  this is read off the equation, not estimated;
* the conclusion is a genuine function, `ContDiff ℝ ∞`, pairing with every test
  supported in the inner ball.

`LocalClosureAlgebra.exhaustiveLocalClosureDichotomy` turns a family of these
into the registered target; that passage is `target_of_exhaustion` and is
already proved.  So this file is the last piece of the local pipeline, and it
contains no equation, residual, ledger, route or target.
-/

namespace Hypostructure.PDE.Solution.WindowCertificate

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.LocalEmbedding
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/--
**The parabolic per-window certificate.**

A state that sits at some Sobolev grade on the outer ball and whose heat image
is smooth there is represented, on the window ball, by a genuine
`ContDiff ℝ ∞` function.

This is `smoothOn_ball_of_heat_smoothOn` followed by
`exists_contDiff_representative_of_smoothOn_ball`: the bootstrap raises the
grade without bound on the inner ball, and the local embedding reads the
resulting `H^∞_loc` state as a classical function.
-/
theorem exists_contDiff_representative_of_heat_smoothOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (center : Point)
    {windowRadius innerRadius outerRadius : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < innerRadius)
    (nested : innerRadius ≤ outerRadius)
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius)
      (heatOperator basis timeIndex state)) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
        state test = ∫ place : Point, test place • representative place :=
  exists_contDiff_representative_of_smoothOn_ball center window_pos window_nested
    (smoothOn_ball_of_heat_smoothOn basis timeIndex center nested state_held
      source_smooth)

omit [DecidableEq Index] in
/--
**The elliptic per-window certificate.**

The same statement with the Laplacian in place of the heat operator, composing
`smoothOn_ball_of_laplacian_smoothOn` with the local embedding.
-/
theorem exists_contDiff_representative_of_laplacian_smoothOn
    (basis : OrthonormalBasis Index ℝ Point) (center : Point)
    {windowRadius innerRadius outerRadius : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < innerRadius)
    (nested : innerRadius ≤ outerRadius)
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius) (Δ state)) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
        state test = ∫ place : Point, test place • representative place :=
  exists_contDiff_representative_of_smoothOn_ball center window_pos window_nested
    (smoothOn_ball_of_laplacian_smoothOn basis center nested state_held
      source_smooth)

end Hypostructure.PDE.Solution.WindowCertificate
