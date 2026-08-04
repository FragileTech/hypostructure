import Hypostructure.PDE.Strategy.LocalRegularityChain
import Hypostructure.PDE.Distribution.Recovery
import Hypostructure.PDE.Distribution.Multiplier

/-!
# Regularity of the recovered velocity

The vorticity determines the velocity only modulo the harmonic kernel.  A
*recovery operator* is the inverse of that determination: a matrix of Fourier
multipliers `T` with `u^⊥ = T ω`, which is what
`PDE/Distribution/Multiplier.lean` carries as `QuotientRecovery`.

The observation this module rests on is that the recovery operator commutes
with the heat operator, because both are Fourier multipliers.  So the vorticity
equation `(∂_t − Δ_x) ω = curl f` is carried straight over to the recovered
field:

> `(∂_t − Δ_x) u^⊥ = T (curl f) = f`,

and the recovered velocity solves the *heat equation with the forcing itself as
its source*.  Smoothness of the forcing is then the only analytic input, and
the parabolic certificate finishes.

**No analytic hypothesis is placed on the recovery operator, and none on the
discarded harmonic component.**  That is what makes this the unconditional half
of `stokes:thm:global-normalized-representative`: the parasitic mode of
`stokes:rem:parasitic-counterexample` lives entirely in the kernel `T` quotients
out, so it cannot obstruct anything proved here.
-/

namespace Hypostructure.PDE.Solution.QuotientVelocityRegularity

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Distribution.CurlCalculus
open Hypostructure.PDE.Distribution.Multiplier
open Hypostructure.PDE.Distribution
open Hypostructure.PDE.Strategy.LocalRegularityChain
open scoped SchwartzMap Real LineDeriv Laplacian ContDiff

set_option linter.unusedSectionVars false

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {frame : Fin 3 → Point}

/--
**The recovered velocity solves the heat equation whose source is the forcing
itself.**

Three rewrites and nothing else: the recovery operator commutes with the heat
operator (`QuotientRecovery.heatOperator_apply`), the vorticity equation
replaces the heat image of the curl by the curl of the forcing
(`heatOperator_curl_eq_curl_forcing`), and `forcing_recovered` reads the result
back as the forcing.

`forcing_recovered` says the forcing is itself in the range of the recovery —
for an incompressible system it is, because `T` is the identity on
divergence-free fields.  It is an input here rather than a theorem because the
operator is a black box.
-/
theorem heatOperator_quotient_eq_forcing
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (recovery : Recovery.SliceRecovery Point Value Index (Fin 3))
    {velocity quotientVelocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure : 𝓢'(Point, Value)}
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (recovers : quotientVelocity = recovery.apply (curl frame velocity))
    (forcing_recovered : forcing = recovery.apply (curl frame forcing))
    (index : Fin 3) :
    heatOperator basis timeIndex (quotientVelocity index) = forcing index := by
  rw [recovers, recovery.heatOperator_apply basis timeIndex]
  simp only [heatOperator_curl_eq_curl_forcing basis timeIndex balance]
  rw [← forcing_recovered]

/--
**The recovered velocity is smooth on the inner ball.**

There is no analytic hypothesis: the Sobolev datum is the starting grade, and
the only smoothness assumed is that of the forcing.  In particular nothing is
assumed about the harmonic component the recovery discards, nothing about the
pressure, and nothing about the operator beyond its symbols having temperate
growth.

This is `stokes:lem:velocity-recovery` composed with
`stokes:cor:vorticity-smoothing`, and it is strictly stronger than the route
through the div--curl identity: because `heatOperator_quotient_eq_forcing` is an
identity of states, the heat image of the recovered velocity is smooth wherever
the forcing is, and the parabolic certificate applies directly.  Incompressibility
of the recovered field is therefore not needed.
-/
theorem smoothOn_quotient_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (recovery : Recovery.SliceRecovery Point Value Index (Fin 3))
    (center : Point) {inner outer : ℝ} (nested : inner ≤ outer) {grade : ℝ}
    {velocity quotientVelocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure : 𝓢'(Point, Value)}
    (quotient_held : ∀ index,
      SobolevOn (ball center outer) grade (quotientVelocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (recovers : quotientVelocity = recovery.apply (curl frame velocity))
    (forcing_recovered : forcing = recovery.apply (curl frame forcing))
    (index : Fin 3) :
    SmoothOn (ball center inner) (quotientVelocity index) := by
  refine smoothOn_ball_of_heat_smoothOn basis timeIndex center nested
    (quotient_held index) ?_
  rw [heatOperator_quotient_eq_forcing basis timeIndex recovery balance recovers
    forcing_recovered index]
  exact forcing_smooth index

/--
**The same, presented through an explicit decomposition.**

`velocity = quotientVelocity + harmonicPart` with a curl-free discarded part is
the shape `stokes:def:harmonic-kernel` states, and it gives the recovery
identity back: the curl does not see the harmonic component, so the recovered
field of `velocity` is the recovered field of `quotientVelocity`.
-/
theorem smoothOn_quotient_of_balance_of_decomposition
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (recovery : Recovery.SliceRecovery Point Value Index (Fin 3))
    (center : Point) {inner outer : ℝ} (nested : inner ≤ outer) {grade : ℝ}
    {velocity quotientVelocity harmonicPart forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure : 𝓢'(Point, Value)}
    (decomposition : velocity = quotientVelocity + harmonicPart)
    (harmonic_curl_free : curl frame harmonicPart = 0)
    (quotient_held : ∀ index,
      SobolevOn (ball center outer) grade (quotientVelocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (recovers : quotientVelocity = recovery.apply (curl frame quotientVelocity))
    (forcing_recovered : forcing = recovery.apply (curl frame forcing))
    (index : Fin 3) :
    SmoothOn (ball center inner) (quotientVelocity index) := by
  have same_vorticity : curl frame velocity = curl frame quotientVelocity := by
    rw [decomposition, curl_add, harmonic_curl_free, add_zero]
  refine smoothOn_quotient_of_balance basis timeIndex recovery center nested
    quotient_held balance forcing_smooth ?_ forcing_recovered index
  rw [same_vorticity]
  exact recovers

/--
**The classical reading of the recovered velocity.**

The same conclusion delivered as a genuine `ContDiff ℝ ∞` function pairing with
every test supported in the window ball --- the shape a local-closure vertex
consumes, matching
`LocalRegularityChain.exists_contDiff_representatives_of_balance`.
-/
theorem exists_contDiff_quotient_representatives_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (recovery : Recovery.SliceRecovery Point Value Index (Fin 3))
    (center : Point) {windowRadius inner outer : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < inner)
    (nested : inner ≤ outer) {grade : ℝ}
    {velocity quotientVelocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {pressure : 𝓢'(Point, Value)}
    (quotient_held : ∀ index,
      SobolevOn (ball center outer) grade (quotientVelocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient frame pressure index = forcing index)
    (forcing_smooth : ∀ index, SmoothOn (ball center outer) (forcing index))
    (recovers : quotientVelocity = recovery.apply (curl frame velocity))
    (forcing_recovered : forcing = recovery.apply (curl frame forcing)) :
    ∀ index, ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
        quotientVelocity index test =
          ∫ place : Point, test place • representative place := fun index =>
  LocalEmbedding.exists_contDiff_representative_of_smoothOn_ball center window_pos
    window_nested
    (smoothOn_quotient_of_balance basis timeIndex recovery center nested
      quotient_held balance forcing_smooth recovers forcing_recovered index)

end Hypostructure.PDE.Solution.QuotientVelocityRegularity
