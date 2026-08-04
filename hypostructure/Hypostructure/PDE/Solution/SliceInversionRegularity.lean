import Hypostructure.PDE.Solution.ScaleRecombination
import Hypostructure.PDE.Solution.HarmonicKernelSmoothing
import Hypostructure.PDE.Strategy.LocalRegularityChain
import Hypostructure.PDE.Localization.BalanceTransport
import Hypostructure.PDE.DivCurl

/-!
# The local div–curl inversion, and why time-independence is the whole of it

`PDE/Solution/QuotientVelocityRegularity.lean` runs the recovery through
`Recovery.SliceRecovery`, whose second field asks the operator to commute with
the **heat operator** `∂_t − Δ_x`.  That field is true of a Fourier multiplier
and it is what makes the multiplier route short, but it is a genuinely stronger
statement than a local Hodge quotient satisfies: `𝒯_{B_ρ}` acts inside one ball,
and commuting it past `Δ_x` is exactly the boundary-term question the projection
does not answer.  The appendix never claims it — `stokes:lem:time-param-quotient`
claims commutation with `∂_t` alone, and takes the spatial derivatives from
elliptic regularity of the div–curl system instead.

This module carries that weaker, satisfiable interface, runs the appendix's own
route on it, and then constructs it from a statement about a *class of states*
rather than about an operator.

## The three layers

* `SliceInversion` — the consumer's interface.  Two fields: `timeDeriv_invert`
  (the operator commutes with the **time** derivative, and the spatial statement
  is deliberately absent because it is false for a quotient on a ball) and
  `spatialSmoothOn_invert` (smooth rotational data go to **spatially** smooth
  output, at one fixed grade).  `smoothOn_invert` is the payoff.
* `LocalHodge` — the same operator described by the identities of
  `stokes:def:harmonic-kernel` instead: divergence-free values carrying the given
  rotational datum.  `LocalHodge.toSliceInversion` proves the spatial regularity
  from those, so the second field of `SliceInversion` is a **theorem**.
* `HodgeClass` — no operator at all, only the *class* of normalized states,
  closed under the time derivative, with the two halves of the local Hodge
  decomposition: **uniqueness** (normalized states with the same rotational datum
  are the same state) and **solvability** (every state has a normalized field
  with its rotational datum).  `HodgeClass.toLocalHodge` builds the operator from
  those by choice, and every identity above comes out of uniqueness.

## Everything local is `AgreeOn`, and that is what makes it true

The identities are stated as agreement on the window, never as equality of
states.  This is not a weakening for convenience — the global readings are
**false**, and shipping them would repeat the mistake the harmonic-kernel gauge
made.  A normalized field is determined by its rotational datum *on the window
where it is normalized* and not off it; a state-level operator built by cutting
the quotient off carries the right curl on the window and a commutator term
outside it.  `AgreeOn` is what the appendix's `L²(B_ρ)` statements say when read
on states, and `PDE/Localization/WindowAgreement.lean` already transports every
regularity notion along it.

That is also the answer to the bridge.  `PDE/Solution/QuotientRecoveryData.lean`
builds the projection on the window's own `L²` and explains that it does not
transport to states because `LocalNormalization.restrict` has no right inverse.
It does not need one: `HodgeClass` never leaves the state level, and its `unique`
and `solvable` are the window-local readings of
`DivCurl.eq_of_orthogonal_of_curl_eq` and of the existence of
`DivCurl.harmonicComplement`.  No Hilbert space appears below.

## Why the fixed grade is the whole content

`ScaleRecombination` cannot leave the spatial scale from spatial smoothness at
*some* grade: differentiating in time normally costs a grade, so `∂_t^k u`
starves at `grade − k` and the tower dies.  It must die — `a(t)∇ψ(x)` with
`a ∈ L²` is spatially smooth at every level and is not smooth
(`stokes:rem:parasitic-counterexample`).  What rescues the tower is that `𝒯` is
time-independent, so

> `∂_t^k u^⊥ = 𝒯(∂_t^k ω)`,

and each `∂_t^k ω` is smooth because `ω` is: every level of the tower is the
operator's output on smooth data, hence sits at the **same** grade.  That is
`SliceInversion.smoothOn_invert`, and it is why the pressure never enters.

Nothing here mentions Stokes, a dimension, or a gauge.  Being harmonic-kernel
normalized on the window is the only hypothesis the payoff places on the
velocity, and `HodgeClass.agreeOn_invert_of_normalized` turns it into the
recovery identity.
-/

namespace Hypostructure.PDE.Localization.AgreeOn

open MeasureTheory TemperedDistribution TopologicalSpace
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.SliceRestriction
open Hypostructure.PDE.Solution.ScaleRecombination
open scoped SchwartzMap Real LineDeriv

set_option linter.unusedSectionVars false

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {window : Compacts Point} {first second : 𝓢'(Point, Value)}

/-! ### Two more congruences

`WindowAgreement.lean` transports `SobolevOn` and `SmoothOn` along agreement, by
`AgreeOn.localize` and nothing else.  The spatial scale is defined the same way —
through bumps supported in the region — so it transports by the same three
lines.  These belong beside `AgreeOn.sobolevOn`; they are here only so that this
module can be iterated without rebuilding the localization layer. -/

/-- **Agreement on a window transfers spatial Sobolev regularity.** -/
theorem spatialSobolevOn (agree : AgreeOn window first second) {region : Set Point}
    (region_subset : region ⊆ (window : Set Point))
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) {gain grade : ℝ}
    (held : SpatialSobolevOn basis timeIndex region gain grade second) :
    SpatialSobolevOn basis timeIndex region gain grade first := by
  intro bump supported
  rw [agree.localize bump (supported.trans region_subset)]
  exact held bump supported

/-- **…and spatial smoothness**, which is every gain at once. -/
theorem spatialSmoothOn (agree : AgreeOn window first second) {region : Set Point}
    (region_subset : region ⊆ (window : Set Point))
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) {grade : ℝ}
    (smooth : SpatialSmoothOn basis timeIndex region grade second) :
    SpatialSmoothOn basis timeIndex region grade first :=
  fun gain => agree.spatialSobolevOn region_subset basis timeIndex (smooth gain)

/-- **Agreement survives the whole time tower**, `AgreeOn.lineDerivOp` once per
level.  A derivative of a test function supported in the window is supported in
the window, so no level can expose a difference the first did not. -/
theorem timeDerivIterate (agree : AgreeOn window first second)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    ∀ order : ℕ, AgreeOn window
      (Solution.ScaleRecombination.timeDerivIterate basis timeIndex order first)
      (Solution.ScaleRecombination.timeDerivIterate basis timeIndex order second) := by
  intro order
  induction order with
  | zero => exact agree
  | succ previous gained =>
      rw [timeDerivIterate_succ_outer, timeDerivIterate_succ_outer]
      exact gained.lineDerivOp (basis timeIndex)

end Hypostructure.PDE.Localization.AgreeOn

namespace Hypostructure.PDE.Solution.SliceInversionRegularity

open MeasureTheory Metric TemperedDistribution TopologicalSpace
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.SliceRestriction
open Hypostructure.PDE.Solution.ScaleRecombination
open Hypostructure.PDE.Distribution.CurlCalculus
open Hypostructure.PDE.Strategy.LocalRegularityChain
open Hypostructure.PDE.Localization
open scoped SchwartzMap Real LineDeriv Laplacian ContDiff

set_option linter.unusedSectionVars false

universe uPoint uValue uIndex

section Commutation

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {frame : Fin 3 → Point}

/-- **The curl commutes with the whole time tower.**  `curl_lineDerivOp` once per
level; the time direction is not distinguished from any other. -/
theorem curl_timeDerivIterate (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    ∀ (order : ℕ) (field : Fin 3 → 𝓢'(Point, Value)),
      curl frame (fun index => timeDerivIterate basis timeIndex order (field index)) =
        fun index => timeDerivIterate basis timeIndex order (curl frame field index) := by
  intro order
  induction order with
  | zero => intro field; rfl
  | succ previous gained =>
      intro field
      have peel : (fun index => timeDerivIterate basis timeIndex (previous + 1) (field index)) =
          fun index => timeDerivIterate basis timeIndex previous
            (∂_{basis timeIndex} (field index)) :=
        funext fun index => timeDerivIterate_succ_inner basis timeIndex previous (field index)
      rw [peel, gained, curl_lineDerivOp]
      exact funext fun index =>
        (timeDerivIterate_succ_inner basis timeIndex previous (curl frame field index)).symm

/-- **Smoothness on a window passes to the curl**: two directional derivatives of
states already smooth there. -/
theorem smoothOn_curl {region : Set Point} {field : Fin 3 → 𝓢'(Point, Value)}
    (smooth : ∀ column, SmoothOn region (field column)) (index : Fin 3) :
    SmoothOn region (curl frame field index) :=
  (smoothOn_lineDerivOp (smooth (index + 2)) (frame (index + 1))).sub
    (smoothOn_lineDerivOp (smooth (index + 1)) (frame (index + 2)))

end Commutation

/-! ## The consumer's interface -/

/--
**The local div–curl inversion of a window.**

The operator that returns the normalized field carrying a given rotational
datum, together with the two properties the recovery argument uses — and no
others.  There is no continuity hypothesis, no symbol, no temperate growth, and
in particular no commutation with the heat operator: a local Hodge quotient
satisfies both fields below and does not satisfy that one.

Both fields speak only of *rotational* data, `curl frame field`, which is the
only kind a recovery is ever fed, and the commutation is agreement on the window
rather than equality of states.
-/
structure SliceInversion (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (frame : Fin 3 → Point) (window : Compacts Point) (grade : ℝ) where
  /-- The inversion itself: rotational datum to normalized field. -/
  invert : (Fin 3 → 𝓢'(Point, Value)) → Fin 3 → 𝓢'(Point, Value)
  /-- **Commutation with the time derivative, and with that one alone.**

  This is time-independence of the window's quotient.  The corresponding
  statement for a *spatial* direction is deliberately absent — it is false for a
  quotient on a ball, and the appendix does not claim it either.  Every spatial
  derivative arrives through `spatialSmoothOn_invert` instead. -/
  timeDeriv_invert : ∀ (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3),
    AgreeOn window (∂_{basis timeIndex} (invert (curl frame field) row))
      (invert (curl frame fun column => ∂_{basis timeIndex} (field column)) row)
  /-- **Smooth rotational data give spatially smooth output, at one fixed
  grade.**  `LocalHodge.toSliceInversion` proves this from the div–curl identity,
  so it is not an extra analytic assumption; it is stated as a field so that a
  caller carrying the operator in any other realization can supply it directly. -/
  spatialSmoothOn_invert : ∀ field : Fin 3 → 𝓢'(Point, Value),
    (∀ column, SmoothOn (window : Set Point) (curl frame field column)) →
    ∀ row, SpatialSmoothOn basis timeIndex (window : Set Point) grade
      (invert (curl frame field) row)

namespace SliceInversion

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {frame : Fin 3 → Point} {window : Compacts Point} {grade : ℝ}

/-- **Every time derivative of the recovered field comes from that time
derivative of the datum.**  Induction on the order with `timeDeriv_invert` as the
step and `AgreeOn.timeDerivIterate` to carry each level's agreement past the
remaining derivatives; this is `stokes:lem:time-param-quotient`'s
`∂_t^j u^⊥ = 𝒯(∂_t^j ω)`, and it is the identity that keeps the pressure out. -/
theorem timeDerivIterate_invert
    (inversion : SliceInversion Point Value basis timeIndex frame window grade) :
    ∀ (order : ℕ) (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3),
      AgreeOn window
        (timeDerivIterate basis timeIndex order (inversion.invert (curl frame field) row))
        (inversion.invert (curl frame fun column =>
          timeDerivIterate basis timeIndex order (field column)) row) := by
  intro order
  induction order with
  | zero => intro field row; exact AgreeOn.refl _
  | succ previous gained =>
      intro field row
      have peel :
          (fun column => timeDerivIterate basis timeIndex previous
              (∂_{basis timeIndex} (field column))) =
            fun column => timeDerivIterate basis timeIndex (previous + 1) (field column) :=
        funext fun column =>
          (timeDerivIterate_succ_inner basis timeIndex previous (field column)).symm
      have head : timeDerivIterate basis timeIndex (previous + 1)
            (inversion.invert (curl frame field) row) =
          timeDerivIterate basis timeIndex previous
            (∂_{basis timeIndex} (inversion.invert (curl frame field) row)) :=
        timeDerivIterate_succ_inner basis timeIndex previous _
      have tail := gained (fun column => ∂_{basis timeIndex} (field column)) row
      rw [peel] at tail
      rw [head]
      exact ((inversion.timeDeriv_invert field row).timeDerivIterate basis timeIndex
        previous).trans tail

/--
**The recovered field is smooth on the window** — the whole content of the
interface.

Every level of the time tower agrees on the window with the operator's output on
smooth rotational data, by `timeDerivIterate_invert` and `curl_timeDerivIterate`,
so every level is spatially smooth at the operator's **own** grade rather than
one grade lower than the level below.  That is the hypothesis
`ScaleRecombination.smoothOn_of_spatialSmoothOn_timeDerivIterate` asks for, and
it is exactly what a time-independent inversion supplies and what a spatial
elliptic recovery alone does not.
-/
theorem smoothOn_invert
    (inversion : SliceInversion Point Value basis timeIndex frame window grade)
    {field : Fin 3 → 𝓢'(Point, Value)}
    (vorticity_smooth : ∀ column, SmoothOn (window : Set Point) (curl frame field column))
    (row : Fin 3) :
    SmoothOn (window : Set Point) (inversion.invert (curl frame field) row) := by
  refine smoothOn_of_spatialSmoothOn_timeDerivIterate basis timeIndex (grade := grade) ?_
  intro order
  refine (inversion.timeDerivIterate_invert order field row).spatialSmoothOn
    (subset_refl _) basis timeIndex ?_
  refine inversion.spatialSmoothOn_invert _ (fun column => ?_) row
  rw [curl_timeDerivIterate basis timeIndex order field]
  exact smoothOn_timeDerivIterate basis timeIndex (vorticity_smooth column) order

/--
**A field that its own vorticity recovers is smooth wherever that vorticity is.**

`recovers` is the normalization: it says the field carries no harmonic-kernel
component on the window, so that the rotational datum determines it there.  It is
the one place a gauge enters, and it enters as agreement on the window, not as an
estimate.  `HodgeClass.agreeOn_invert_of_normalized` supplies it from membership
of the normalized class.
-/
theorem smoothOn_of_recovers
    (inversion : SliceInversion Point Value basis timeIndex frame window grade)
    {velocity : Fin 3 → 𝓢'(Point, Value)}
    (recovers : ∀ index,
      AgreeOn window (velocity index) (inversion.invert (curl frame velocity) index))
    (vorticity_smooth : ∀ index,
      SmoothOn (window : Set Point) (curl frame velocity index))
    (index : Fin 3) :
    SmoothOn (window : Set Point) (velocity index) :=
  (recovers index).smoothOn (subset_refl _)
    (inversion.smoothOn_invert vorticity_smooth index)

end SliceInversion

/-! ## The inversion, from the div–curl identity -/

/-- The spatial frame a window's operators are read in: the three basis
directions the time direction is not. -/
noncomputable abbrev spatialFrame {Point : Type uPoint} [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
    {Index : Type uIndex} [Fintype Index]
    (basis : OrthonormalBasis Index ℝ Point) (spatialIndex : Fin 3 → Index) :
    Fin 3 → Point := fun axis => basis (spatialIndex axis)

/--
**The local Hodge datum.**

What a construction of the window's quotient delivers, described by identities
rather than by regularity: values that are divergence-free on the window and
carry the rotational datum they were recovered from, commuting with the time
derivative, and landing at a fixed grade.

`sobolevOn_invert` is a *membership* statement, not an estimate: the recovered
field sits in `H^grade` on the window.  For the `L²(B_ρ)` quotient the grade is
`0`, and the statement is that the quotient of a square-integrable field is
square integrable — `stokes:lem:projection-state`.
-/
structure LocalHodge (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (window : Compacts Point) (grade : ℝ) where
  /-- The inversion itself. -/
  invert : (Fin 3 → 𝓢'(Point, Value)) → Fin 3 → 𝓢'(Point, Value)
  /-- Time-independence, exactly as in `SliceInversion`. -/
  timeDeriv_invert : ∀ (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3),
    AgreeOn window
      (∂_{basis timeIndex}
        (invert (curl (spatialFrame basis spatialIndex) field) row))
      (invert (curl (spatialFrame basis spatialIndex) fun column =>
        ∂_{basis timeIndex} (field column)) row)
  /-- The recovered field is divergence-free on the window — the first clause of
  the quotient's definition, and what turns `curl_curl` into an identity for
  `Δ_x` there. -/
  divergence_invert : ∀ field : Fin 3 → 𝓢'(Point, Value),
    AgreeOn window
      (divergence (spatialFrame basis spatialIndex)
        (invert (curl (spatialFrame basis spatialIndex) field))) 0
  /-- The recovered field carries the rotational datum it was recovered from —
  the second clause. -/
  curl_invert : ∀ (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3),
    AgreeOn window
      (curl (spatialFrame basis spatialIndex)
        (invert (curl (spatialFrame basis spatialIndex) field)) row)
      (curl (spatialFrame basis spatialIndex) field row)
  /-- The recovered field sits at a fixed grade on the window. -/
  sobolevOn_invert : ∀ field : Fin 3 → 𝓢'(Point, Value),
    (∀ column, SmoothOn (window : Set Point)
      (curl (spatialFrame basis spatialIndex) field column)) →
    ∀ row, SobolevOn (window : Set Point) grade
      (invert (curl (spatialFrame basis spatialIndex) field) row)

namespace LocalHodge

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {spatialIndex : Fin 3 → Index} {window : Compacts Point} {grade : ℝ}

/--
**On the window, the spatial Laplacian of the recovered field is a curl of the
datum.**

`Δv = ∇(div v) − curl curl v` with `div v = 0` there, and the frame Laplacian is
the spatial one by reindexing alone — the same two steps as
`HarmonicKernelSmoothing.spatialLaplacian_eq_zero_of_divergence_free_of_curl_free`,
with the curl kept instead of discarded, and each step carried by the agreement
algebra.  No analysis is added.
-/
theorem agreeOn_spatialLaplacian_invert
    (hodge : LocalHodge Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3) :
    AgreeOn window
      (spatialLaplacian basis timeIndex
        (hodge.invert (curl (spatialFrame basis spatialIndex) field) row))
      (-curl (spatialFrame basis spatialIndex)
        (curl (spatialFrame basis spatialIndex) field) row) := by
  set frame : Fin 3 → Point := spatialFrame basis spatialIndex with frame_def
  set recovered : Fin 3 → 𝓢'(Point, Value) :=
    hodge.invert (curl frame field) with recovered_def
  have expand := congrFun (curl_curl (frame := frame) recovered) row
  have rearranged : laplacian frame recovered row =
      gradient frame (divergence frame recovered) row -
        curl frame (curl frame recovered) row := by
    rw [expand]
    simp only [Pi.sub_apply]
    abel
  have identify : laplacian frame recovered row =
      spatialLaplacian basis timeIndex (recovered row) :=
    scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex spatialIndex
      injective avoidsTime dimension (recovered row)
  have gradient_zero : AgreeOn window
      (gradient frame (divergence frame recovered) row) 0 := by
    refine ((hodge.divergence_invert field).lineDerivOp (frame row)).trans
      (AgreeOn.of_eq ?_)
    simp
  have curls : AgreeOn window (curl frame (curl frame recovered) row)
      (curl frame (curl frame field) row) :=
    AgreeOn.curl (hodge.curl_invert field) row
  rw [← identify, rearranged]
  simpa using gradient_zero.sub curls

/--
**The Hodge datum is a slice inversion.**

Both fields of `SliceInversion` come out: the first is carried over verbatim, and
the second — the spatial regularity — is a *theorem*, from the agreement above
plus `spatialSmoothOn_of_spatialLaplacian_smoothOn`.  So a slice inversion has no
analytic content beyond the fixed-grade membership `sobolevOn_invert`.
-/
noncomputable def toSliceInversion
    (hodge : LocalHodge Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) :
    SliceInversion Point Value basis timeIndex
      (spatialFrame basis spatialIndex) window grade where
  invert := hodge.invert
  timeDeriv_invert := hodge.timeDeriv_invert
  spatialSmoothOn_invert field vorticity_smooth row := by
    refine spatialSmoothOn_of_spatialLaplacian_smoothOn basis timeIndex
      (hodge.sobolevOn_invert field vorticity_smooth row) ?_
    exact (hodge.agreeOn_spatialLaplacian_invert injective avoidsTime dimension
      field row).smoothOn (subset_refl _) (smoothOn_curl vorticity_smooth row).neg

@[simp] theorem toSliceInversion_invert
    (hodge : LocalHodge Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) :
    (hodge.toSliceInversion injective avoidsTime dimension).invert = hodge.invert := rfl

end LocalHodge

/-! ## The operator, from the normalized class alone -/

/--
**The normalized class of a window**, and nothing else.

No operator appears.  What is asked is the class of states the window's
normalization admits, together with the two halves of the local Hodge
decomposition:

* `unique` — normalized states whose rotational data agree on the window agree on
  the window.  This is `DivCurl.eq_of_orthogonal_of_curl_eq` read on states: the
  difference is divergence-free, curl-free and normalized at once, and the
  normalization admits no such state on the window.
* `solvable` — every state has a normalized field whose rotational datum agrees
  with its own there.  This is the existence of `DivCurl.harmonicComplement`: the
  field to take is `u − proj_𝓗 u`, whose curl is `curl u` by
  `LocalNormalization.sliceCurl_quotientSlicePart`, cut off outside the window
  where nothing is claimed.

The remaining three fields say the class is closed under the time derivative,
consists of states divergence-free on the window, and sits at a fixed grade
there.

Every clause is `AgreeOn`.  The global readings are false, and that is the whole
reason the interface is shaped this way — see the module docstring.
-/
structure HodgeClass (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (window : Compacts Point) (grade : ℝ) where
  /-- The states the window's normalization admits. -/
  Normalized : (Fin 3 → 𝓢'(Point, Value)) → Prop
  /-- Normalized states are divergence-free on the window. -/
  divergence_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    AgreeOn window (divergence (spatialFrame basis spatialIndex) state) 0
  /-- The class is closed under the time derivative — the state-level reading of
  the quotient being the same one at every time. -/
  timeDeriv_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    Normalized fun column => ∂_{basis timeIndex} (state column)
  /-- Normalized states sit at a fixed grade on the window. -/
  sobolevOn_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    ∀ row, SobolevOn (window : Set Point) grade (state row)
  /-- **Uniqueness.**  On the window, the rotational datum determines the
  normalized state. -/
  unique : ∀ {first second : Fin 3 → 𝓢'(Point, Value)}, Normalized first → Normalized second →
    (∀ row, AgreeOn window
      (curl (spatialFrame basis spatialIndex) first row)
      (curl (spatialFrame basis spatialIndex) second row)) →
    ∀ row, AgreeOn window (first row) (second row)
  /-- **Solvability.**  Every state has a normalized field carrying its rotational
  datum on the window. -/
  solvable : ∀ field : Fin 3 → 𝓢'(Point, Value), ∃ state, Normalized state ∧
    ∀ row, AgreeOn window
      (curl (spatialFrame basis spatialIndex) state row)
      (curl (spatialFrame basis spatialIndex) field row)

namespace HodgeClass

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {spatialIndex : Fin 3 → Index} {window : Compacts Point} {grade : ℝ}

open Classical in
/-- **The operator, from the class.**  A normalized state whose rotational datum
is the given one on the window, which `unique` makes a description rather than a
choice. -/
noncomputable def invert
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (data : Fin 3 → 𝓢'(Point, Value)) : Fin 3 → 𝓢'(Point, Value) :=
  if witness : ∃ state, cls.Normalized state ∧
      ∀ row, AgreeOn window
        (curl (spatialFrame basis spatialIndex) state row) (data row) then
    witness.choose
  else 0

/-- The recovered field is normalized. -/
theorem normalized_invert
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (field : Fin 3 → 𝓢'(Point, Value)) :
    cls.Normalized (cls.invert (curl (spatialFrame basis spatialIndex) field)) := by
  classical
  obtain ⟨state, normalized, same⟩ := cls.solvable field
  have witness : ∃ candidate, cls.Normalized candidate ∧
      ∀ row, AgreeOn window
        (curl (spatialFrame basis spatialIndex) candidate row)
        (curl (spatialFrame basis spatialIndex) field row) := ⟨state, normalized, same⟩
  rw [invert, dif_pos witness]
  exact witness.choose_spec.1

/-- The recovered field carries, on the window, the rotational datum it was
recovered from. -/
theorem agreeOn_curl_invert
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3) :
    AgreeOn window
      (curl (spatialFrame basis spatialIndex)
        (cls.invert (curl (spatialFrame basis spatialIndex) field)) row)
      (curl (spatialFrame basis spatialIndex) field row) := by
  classical
  obtain ⟨state, normalized, same⟩ := cls.solvable field
  have witness : ∃ candidate, cls.Normalized candidate ∧
      ∀ row, AgreeOn window
        (curl (spatialFrame basis spatialIndex) candidate row)
        (curl (spatialFrame basis spatialIndex) field row) := ⟨state, normalized, same⟩
  rw [invert, dif_pos witness]
  exact witness.choose_spec.2 row

/-- **The gauge, in the form the recovery consumes.**  A normalized state is what
its own rotational datum recovers, on the window — this is the identity
`recovers` of `SliceInversion.smoothOn_of_recovers`, and it comes straight from
`unique`. -/
theorem agreeOn_invert_of_normalized
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    {state : Fin 3 → 𝓢'(Point, Value)} (normalized : cls.Normalized state) (row : Fin 3) :
    AgreeOn window
      (cls.invert (curl (spatialFrame basis spatialIndex) state) row) (state row) :=
  cls.unique (cls.normalized_invert state) normalized (cls.agreeOn_curl_invert state) row

/-- **The operator only sees the datum on the window.**  Rotational data agreeing
there are recovered to states agreeing there — by `unique` when both are
solvable, and trivially otherwise, since either witness would serve for both. -/
theorem agreeOn_invert_congr
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    {first second : Fin 3 → 𝓢'(Point, Value)}
    (agree : ∀ row, AgreeOn window (first row) (second row)) (row : Fin 3) :
    AgreeOn window (cls.invert first row) (cls.invert second row) := by
  classical
  by_cases left : ∃ state, cls.Normalized state ∧
      ∀ row, AgreeOn window
        (curl (spatialFrame basis spatialIndex) state row) (first row)
  · have right : ∃ state, cls.Normalized state ∧
        ∀ row, AgreeOn window
          (curl (spatialFrame basis spatialIndex) state row) (second row) :=
      ⟨left.choose, left.choose_spec.1,
        fun index => (left.choose_spec.2 index).trans (agree index)⟩
    rw [invert, dif_pos left, invert, dif_pos right]
    exact cls.unique left.choose_spec.1 right.choose_spec.1
      (fun index => (left.choose_spec.2 index).trans
        ((agree index).trans (right.choose_spec.2 index).symm)) row
  · have right : ¬ ∃ state, cls.Normalized state ∧
        ∀ row, AgreeOn window
          (curl (spatialFrame basis spatialIndex) state row) (second row) := by
      rintro ⟨state, normalized, same⟩
      exact left ⟨state, normalized, fun index => (same index).trans (agree index).symm⟩
    rw [invert, dif_neg left, invert, dif_neg right]

/-- **Time-independence, as a theorem.**  The time derivative of the recovered
field is normalized and carries, on the window, the time derivative of the datum,
so it *is* what that derivative recovers — by `unique`, and by nothing else. -/
theorem agreeOn_timeDeriv_invert
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (field : Fin 3 → 𝓢'(Point, Value)) (row : Fin 3) :
    AgreeOn window
      (∂_{basis timeIndex}
        (cls.invert (curl (spatialFrame basis spatialIndex) field) row))
      (cls.invert (curl (spatialFrame basis spatialIndex) fun column =>
        ∂_{basis timeIndex} (field column)) row) := by
  set frame : Fin 3 → Point := spatialFrame basis spatialIndex with frame_def
  set recovered : Fin 3 → 𝓢'(Point, Value) := cls.invert (curl frame field) with recovered_def
  have normalized : cls.Normalized recovered := cls.normalized_invert field
  have derivative : AgreeOn window
      (cls.invert (curl frame fun column => ∂_{basis timeIndex} (recovered column)) row)
      (∂_{basis timeIndex} (recovered row)) :=
    cls.agreeOn_invert_of_normalized (cls.timeDeriv_of_normalized normalized) row
  have data : ∀ index, AgreeOn window
      (curl frame (fun column => ∂_{basis timeIndex} (recovered column)) index)
      (curl frame (fun column => ∂_{basis timeIndex} (field column)) index) := by
    intro index
    rw [curl_lineDerivOp, curl_lineDerivOp]
    exact (cls.agreeOn_curl_invert field index).lineDerivOp (basis timeIndex)
  exact derivative.symm.trans (cls.agreeOn_invert_congr data row)

/--
**The class is a Hodge datum.**

Every field of `LocalHodge` is discharged: the identities from `unique` and
`solvable` through `agreeOn_invert_of_normalized`, the divergence and the grade
from the corresponding clauses of the class.  So no operator has to be
exhibited — the normalized class is the whole input.
-/
noncomputable def toLocalHodge
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade) :
    LocalHodge Point Value basis timeIndex spatialIndex window grade where
  invert := cls.invert
  timeDeriv_invert := cls.agreeOn_timeDeriv_invert
  divergence_invert field := cls.divergence_of_normalized (cls.normalized_invert field)
  curl_invert := cls.agreeOn_curl_invert
  sobolevOn_invert field _ row :=
    cls.sobolevOn_of_normalized (cls.normalized_invert field) row

/-- **The class is a slice inversion.**  The composite of the two constructions,
which is the form a consumer wants: from the normalized class of a window
straight to the interface `smoothOn_invert` runs on. -/
noncomputable def toSliceInversion
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) :
    SliceInversion Point Value basis timeIndex
      (spatialFrame basis spatialIndex) window grade :=
  cls.toLocalHodge.toSliceInversion injective avoidsTime dimension

@[simp] theorem toSliceInversion_invert
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) :
    (cls.toSliceInversion injective avoidsTime dimension).invert = cls.invert := rfl

/--
**A normalized velocity is smooth wherever its vorticity is** — the gauge's
payoff, with no operator mentioned anywhere in the statement.

This is `stokes:lem:time-param-quotient` in the form the closure of a local
regularity vertex consumes: being harmonic-kernel normalized on the window is all
that is asked of the velocity, and the pressure never appears.
-/
theorem smoothOn_of_normalized
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {velocity : Fin 3 → 𝓢'(Point, Value)} (normalized : cls.Normalized velocity)
    (vorticity_smooth : ∀ index, SmoothOn (window : Set Point)
      (curl (spatialFrame basis spatialIndex) velocity index))
    (index : Fin 3) :
    SmoothOn (window : Set Point) (velocity index) :=
  (cls.toSliceInversion injective avoidsTime dimension).smoothOn_of_recovers
    (fun row => by
      rw [toSliceInversion_invert]
      exact (cls.agreeOn_invert_of_normalized normalized row).symm)
    vorticity_smooth index

end HodgeClass

/-! ## The class, from the window's own `L²`

The five clauses of `HodgeClass` that are not the Hodge decomposition come from a
*realization*: a picture of the states in the window's own `L²`, together with
the statement that the picture is faithful — states with the same restriction
agree on the window.  Against that, **`unique` is a theorem**: it is
`DivCurl.eq_of_orthogonal_of_curl_eq`, which the framework already proves from
nothing but continuity of the two first-order operators, followed by
faithfulness.

`solvable` is the one clause that does not reduce.  It is the local Hodge
decomposition itself — every state has a divergence-free normalized field
carrying its rotational datum on the window — and no reformulation moves it: the
class it lives in has to be small enough for `unique` and large enough for
`solvable` at the same time, and that is exactly what the decomposition asserts.
-/

universe uSlice uDivergence uCurl

/--
**The window's own `L²`, and the fact that it sees exactly the window.**

`restrict` is the picture of a state on the window, `sliceDivergence` and
`sliceCurl` are the window's first-order operators on it — continuous, which is
the only analytic property `DivCurl` ever uses — and `faithful` is the statement
that nothing on the window is invisible to the picture.
-/
structure WindowRealization (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (window : Compacts Point) (grade : ℝ)
    (Slice : Type uSlice) [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
    (DivergenceValue : Type uDivergence) [NormedAddCommGroup DivergenceValue]
    [NormedSpace ℝ DivergenceValue]
    (CurlValue : Type uCurl) [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue] where
  /-- The picture of a state on the window. -/
  restrict : (Fin 3 → 𝓢'(Point, Value)) → Slice
  /-- The window's divergence, continuous into a negative-order space. -/
  sliceDivergence : Slice →L[ℝ] DivergenceValue
  /-- The window's curl. -/
  sliceCurl : Slice →L[ℝ] CurlValue
  /-- **Faithfulness**: the picture sees exactly the window.  This is what
  replaces a right inverse of the restriction — the map need not be invertible,
  only injective up to what the window can tell. -/
  faithful : ∀ {first second : Fin 3 → 𝓢'(Point, Value)}, restrict first = restrict second →
    ∀ row, AgreeOn window (first row) (second row)
  /-- The slice divergence is the window's divergence. -/
  agreeOn_divergence : ∀ {state : Fin 3 → 𝓢'(Point, Value)},
    sliceDivergence (restrict state) = 0 →
    AgreeOn window (divergence (spatialFrame basis spatialIndex) state) 0
  /-- The slice curl is the window's curl: rotational data agreeing there are the
  same slice curl. -/
  sliceCurl_of_agreeOn : ∀ {first second : Fin 3 → 𝓢'(Point, Value)},
    (∀ row, AgreeOn window
      (curl (spatialFrame basis spatialIndex) first row)
      (curl (spatialFrame basis spatialIndex) second row)) →
    sliceCurl (restrict first) = sliceCurl (restrict second)
  /-- Normalized states sit at the grade on the window. -/
  sobolevOn_of_orthogonal : ∀ {state : Fin 3 → 𝓢'(Point, Value)},
    restrict state ∈ (DivCurl.harmonicKernel sliceDivergence sliceCurl)ᗮ →
    sliceDivergence (restrict state) = 0 →
    ∀ row, SobolevOn (window : Set Point) grade (state row)
  /-- **Time-independence of the normalization**: the picture is the same one at
  every time, so the class is closed under the time derivative. -/
  timeDeriv_of_orthogonal : ∀ {state : Fin 3 → 𝓢'(Point, Value)},
    restrict state ∈ (DivCurl.harmonicKernel sliceDivergence sliceCurl)ᗮ →
    sliceDivergence (restrict state) = 0 →
    restrict (fun column => ∂_{basis timeIndex} (state column)) ∈
        (DivCurl.harmonicKernel sliceDivergence sliceCurl)ᗮ ∧
      sliceDivergence (restrict fun column => ∂_{basis timeIndex} (state column)) = 0
  /-- **Solvability** — the local Hodge decomposition, and the only clause that is
  not plumbing.  Every state has a divergence-free normalized field carrying its
  rotational datum on the window. -/
  solvable : ∀ field : Fin 3 → 𝓢'(Point, Value), ∃ state,
    restrict state ∈ (DivCurl.harmonicKernel sliceDivergence sliceCurl)ᗮ ∧
      sliceDivergence (restrict state) = 0 ∧
      ∀ row, AgreeOn window
        (curl (spatialFrame basis spatialIndex) state row)
        (curl (spatialFrame basis spatialIndex) field row)

namespace WindowRealization

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {spatialIndex : Fin 3 → Index} {window : Compacts Point} {grade : ℝ}
  {Slice : Type uSlice} [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
  {DivergenceValue : Type uDivergence} [NormedAddCommGroup DivergenceValue]
  [NormedSpace ℝ DivergenceValue]
  {CurlValue : Type uCurl} [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]

/--
**A faithful realization is a normalized class.**

Five of the six clauses are read straight off the realization.  The sixth,
`unique`, is a **theorem**: two normalized states whose rotational data agree on
the window have the same slice curl and the same slice divergence, so
`DivCurl.eq_of_orthogonal_of_curl_eq` makes their pictures equal, and
faithfulness carries that back to agreement on the window.

So the whole of `HodgeClass` reduces to the realization, and the whole of the
realization reduces — modulo plumbing — to `solvable`.
-/
def toHodgeClass
    (realization : WindowRealization Point Value basis timeIndex spatialIndex window grade
      Slice DivergenceValue CurlValue) :
    HodgeClass Point Value basis timeIndex spatialIndex window grade where
  Normalized state :=
    realization.restrict state ∈
        (DivCurl.harmonicKernel realization.sliceDivergence realization.sliceCurl)ᗮ ∧
      realization.sliceDivergence (realization.restrict state) = 0
  divergence_of_normalized normalized := realization.agreeOn_divergence normalized.2
  timeDeriv_of_normalized normalized :=
    realization.timeDeriv_of_orthogonal normalized.1 normalized.2
  sobolevOn_of_normalized normalized :=
    realization.sobolevOn_of_orthogonal normalized.1 normalized.2
  unique first_normalized second_normalized curls row :=
    realization.faithful
      (DivCurl.eq_of_orthogonal_of_curl_eq first_normalized.1 second_normalized.1
        (by rw [first_normalized.2, second_normalized.2])
        (realization.sliceCurl_of_agreeOn curls)) row
  solvable field := by
    obtain ⟨state, orthogonal, divergence_free, curls⟩ := realization.solvable field
    exact ⟨state, ⟨orthogonal, divergence_free⟩, curls⟩

end WindowRealization



/-! ## The class the argument actually consumes

Everything above builds an operator.  The argument does not use one.

Run the tower directly: at each level `∂_t^k u` is again normalized, hence
divergence-free on the window and at the **same** grade; `Δ_x = −curl curl` there
by `curl_curl`, and the right-hand side is smooth because `curl u` is; so
`spatialSmoothOn_of_spatialLaplacian_smoothOn` gives every level spatial
smoothness at that one grade, and `ScaleRecombination` closes.  `𝒯` is never
applied, so uniqueness of the normalized representative and solvability of the
div--curl system are never needed --- they were only ever there to build the
operator.

What is left is **four** clauses, and the fixed grade in the presence of the
closure under `∂_t` is the whole of the content: differentiating in time normally
costs a grade, and a class that keeps one is exactly what the harmonic-kernel
normalization buys (`stokes:rem:parasitic-counterexample` is the field for which
no such class exists).
-/

/--
**The normalized class of a window**, carrying only what the recovery argument
reads: divergence-free on the window, closed under the time derivative, and at a
fixed grade there.

No operator, no uniqueness, no solvability, no Hilbert space.
-/
structure NormalizedClass (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (window : Compacts Point) (grade : ℝ) where
  /-- The states the window's normalization admits. -/
  Normalized : (Fin 3 → 𝓢'(Point, Value)) → Prop
  /-- They are divergence-free on the window. -/
  divergence_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    AgreeOn window (divergence (spatialFrame basis spatialIndex) state) 0
  /-- The class is closed under the time derivative. -/
  timeDeriv_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    Normalized fun column => ∂_{basis timeIndex} (state column)
  /-- …and every member sits at **one** grade on the window.  Read with the
  previous clause, this is the statement that the time tower does not starve. -/
  sobolevOn_of_normalized : ∀ {state : Fin 3 → 𝓢'(Point, Value)}, Normalized state →
    ∀ row, SobolevOn (window : Set Point) grade (state row)

namespace NormalizedClass

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
  {spatialIndex : Fin 3 → Index} {window : Compacts Point} {grade : ℝ}

/-- **Every level of the time tower is normalized**, hence at the same grade. -/
theorem normalized_timeDerivIterate
    (cls : NormalizedClass Point Value basis timeIndex spatialIndex window grade) :
    ∀ (order : ℕ) {state : Fin 3 → 𝓢'(Point, Value)}, cls.Normalized state →
      cls.Normalized fun column => timeDerivIterate basis timeIndex order (state column) := by
  intro order
  induction order with
  | zero => intro state normalized; exact normalized
  | succ previous gained =>
      intro state normalized
      have peel : (fun column => timeDerivIterate basis timeIndex (previous + 1) (state column)) =
          fun column => timeDerivIterate basis timeIndex previous
            (∂_{basis timeIndex} (state column)) :=
        funext fun column =>
          timeDerivIterate_succ_inner basis timeIndex previous (state column)
      rw [peel]
      exact gained (cls.timeDeriv_of_normalized normalized)

/-- **On the window, the spatial Laplacian of a normalized state is a double
curl.**  `Δv = ∇(div v) − curl curl v` with the first term gone there; the frame
Laplacian is the spatial one by reindexing alone.  No analysis is added. -/
theorem agreeOn_spatialLaplacian
    (cls : NormalizedClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {state : Fin 3 → 𝓢'(Point, Value)} (normalized : cls.Normalized state) (row : Fin 3) :
    AgreeOn window (spatialLaplacian basis timeIndex (state row))
      (-curl (spatialFrame basis spatialIndex)
        (curl (spatialFrame basis spatialIndex) state) row) := by
  set frame : Fin 3 → Point := spatialFrame basis spatialIndex with frame_def
  have expand := congrFun (curl_curl (frame := frame) state) row
  have rearranged : laplacian frame state row =
      gradient frame (divergence frame state) row -
        curl frame (curl frame state) row := by
    rw [expand]
    simp only [Pi.sub_apply]
    abel
  have identify : laplacian frame state row =
      spatialLaplacian basis timeIndex (state row) :=
    scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex spatialIndex
      injective avoidsTime dimension (state row)
  have gradient_zero : AgreeOn window
      (gradient frame (divergence frame state) row) 0 := by
    refine ((cls.divergence_of_normalized normalized).lineDerivOp (frame row)).trans
      (AgreeOn.of_eq ?_)
    simp
  rw [← identify, rearranged]
  simpa using gradient_zero.sub (AgreeOn.refl (curl frame (curl frame state) row))

/-- **A normalized state whose curl is smooth on the window is spatially smooth
there, at the class's own grade.** -/
theorem spatialSmoothOn_of_normalized
    (cls : NormalizedClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {state : Fin 3 → 𝓢'(Point, Value)} (normalized : cls.Normalized state)
    (vorticity_smooth : ∀ column, SmoothOn (window : Set Point)
      (curl (spatialFrame basis spatialIndex) state column))
    (row : Fin 3) :
    SpatialSmoothOn basis timeIndex (window : Set Point) grade (state row) :=
  spatialSmoothOn_of_spatialLaplacian_smoothOn basis timeIndex
    (cls.sobolevOn_of_normalized normalized row)
    ((cls.agreeOn_spatialLaplacian injective avoidsTime dimension normalized row).smoothOn
      (subset_refl _) (smoothOn_curl vorticity_smooth row).neg)

/--
**The payoff, with no operator anywhere.**

A normalized velocity whose vorticity is smooth on the window is smooth there.
Each level of the time tower is normalized by `normalized_timeDerivIterate`,
hence spatially smooth at the *same* grade, and
`ScaleRecombination.smoothOn_of_spatialSmoothOn_timeDerivIterate` closes.

This is `stokes:lem:time-param-quotient`.  Being harmonic-kernel normalized on
the window is the only hypothesis on the velocity; the pressure never appears,
and neither does the local Hodge decomposition.
-/
theorem smoothOn_of_normalized
    (cls : NormalizedClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {velocity : Fin 3 → 𝓢'(Point, Value)} (normalized : cls.Normalized velocity)
    (vorticity_smooth : ∀ index, SmoothOn (window : Set Point)
      (curl (spatialFrame basis spatialIndex) velocity index))
    (index : Fin 3) :
    SmoothOn (window : Set Point) (velocity index) := by
  refine smoothOn_of_spatialSmoothOn_timeDerivIterate basis timeIndex (grade := grade) ?_
  intro order
  refine cls.spatialSmoothOn_of_normalized injective avoidsTime dimension
    (cls.normalized_timeDerivIterate order normalized) (fun column => ?_) index
  rw [curl_timeDerivIterate basis timeIndex order velocity]
  exact smoothOn_timeDerivIterate basis timeIndex (vorticity_smooth column) order

/--
**The local closure, from the balance alone.**

The vorticity is smooth on the inner ball because taking the curl of the balance
eliminates the pressure and leaves a heat equation with a smooth source
(`smoothOn_curl_of_balance`); the class turns that into smoothness of the
velocity.  Nothing is assumed about the pressure, and nothing is inverted.
-/
theorem smoothOn_of_balance
    (cls : NormalizedClass Point Value basis timeIndex spatialIndex window grade)
    (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (center : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    (inside : (window : Set Point) ⊆ ball center inner)
    {vorticityGrade : ℝ}
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (normalized : cls.Normalized velocity)
    (held : ∀ index, SobolevOn (ball center outer) vorticityGrade
      (curl (spatialFrame basis spatialIndex) velocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient (spatialFrame basis spatialIndex) pressure index = forcing index)
    (forcing_smooth : ∀ index,
      SmoothOn (ball center outer) (curl (spatialFrame basis spatialIndex) forcing index))
    (index : Fin 3) :
    SmoothOn (window : Set Point) (velocity index) :=
  cls.smoothOn_of_normalized injective avoidsTime dimension normalized
    (fun axis => SmoothOn.mono_region inside
      (smoothOn_curl_of_balance basis timeIndex center nested held balance forcing_smooth axis))
    index

end NormalizedClass

/-! ## The local closure -/

/--
**The local closure, from the balance alone.**

Two steps and nothing else: the vorticity is smooth on the inner ball because
taking the curl of the balance eliminates the pressure and leaves a heat equation
with a smooth source (`smoothOn_curl_of_balance`), and the normalized class turns
that into smoothness of the velocity itself
(`HodgeClass.smoothOn_of_normalized`).

The pressure appears in the hypotheses and in no conclusion, and no hypothesis is
placed on it: that is the sense in which the route is non-circular.  The velocity
is asked only to be harmonic-kernel normalized on the window.
-/
theorem smoothOn_of_balance_of_normalized
    {Point : Type uPoint} [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
    [MeasurableSpace Point] [BorelSpace Point]
    {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    (center : Point) {inner outer : ℝ} (nested : inner ≤ outer) {grade : ℝ}
    {window : Compacts Point}
    (inside : (window : Set Point) ⊆ ball center inner)
    (cls : HodgeClass Point Value basis timeIndex spatialIndex window grade)
    {vorticityGrade : ℝ}
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {pressure : 𝓢'(Point, Value)}
    (normalized : cls.Normalized velocity)
    (held : ∀ index, SobolevOn (ball center outer) vorticityGrade
      (curl (spatialFrame basis spatialIndex) velocity index))
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) +
          gradient (spatialFrame basis spatialIndex) pressure index = forcing index)
    (forcing_smooth : ∀ index,
      SmoothOn (ball center outer) (curl (spatialFrame basis spatialIndex) forcing index))
    (index : Fin 3) :
    SmoothOn (window : Set Point) (velocity index) :=
  cls.smoothOn_of_normalized injective avoidsTime dimension normalized
    (fun axis => SmoothOn.mono_region inside
      (smoothOn_curl_of_balance basis timeIndex center nested held balance forcing_smooth axis))
    index

end Hypostructure.PDE.Solution.SliceInversionRegularity
