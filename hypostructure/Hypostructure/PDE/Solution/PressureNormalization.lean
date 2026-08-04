import Hypostructure.PDE.Localization.WindowAgreement
import Hypostructure.PDE.Distribution.CurlCalculus
import Hypostructure.PDE.Solution.SliceRestriction

/-!
# Normalizing the potential

In the balance

> `∂_t u − Δ_x u + ∇p = f`

the potential `p` enters **only** through its spatial gradient.  Nothing in the
identity — and therefore nothing any consumer of the identity can observe —
distinguishes `p` from `p + a`, where `a` is any state annihilated by every
spatial derivative, that is, any function of time alone.  This module is that
observation, `stokes:lem:pressure-normalization`, and its consequences.

## Why it is needed rather than merely true

A residual that recovers a potential does not recover *the* potential: it
recovers *a* potential, produced by whichever solve it happened to run.  A
later stage that asks for the regularity of "the" potential is therefore asking
an ill-posed question unless one of two things holds — either the stage is
insensitive to the ambiguity, or the ambiguity is pinned down by a further
normalization.  The theorems below establish the first and make the second
available:

* `gradient_add_eq_of_spatiallyConstant` and its window companion
  `agreeOn_gradient_add_of_spatiallyConstantOn` say the *gradient* does not see
  the ambiguity, so `agreeOn_balance_add_of_spatiallyConstantOn` says the
  *balance* does not either: a normalized representative may be substituted for
  the recovered one at no cost, in the window-local form a residual owns its
  equation in;
* `spatiallyConstantOn_sub_of_agreeOn_balance` is the exact converse and the
  reason the ambiguity is no larger than claimed: two potentials that solve the
  same balance on a window differ, *there*, by a spatially constant state and by
  nothing else;
* `spatialSmoothOn_congr_of_spatiallyConstantOn_sub` is the payoff.  Spatial
  regularity of the potential on a window is a property of the balance and not
  of the representative, so a stage may be handed whichever potential is
  convenient.

## What the normalization does **not** buy, and why

It buys nothing in time, and this is not a gap in the proof — it is the
mathematics.  The ambiguity `a` is a function of time alone, so it may be
chosen as rough in time as one likes while remaining invisible to the balance;
consequently *no* statement of the form "the potential is regular in time" can
follow from the balance without some further input.  The frequency-side form of
exactly this obstruction is already recorded in
`Solution/SliceRestriction.lean` as `exists_norm_sq_gt_mul_spatialSymbol`, whose
witness is the same parasitic mode `u(x,t) = a(t)`.  So the conclusions here are
stated on the spatial scale — `SpatialSmoothOn` — which is the strongest true
form, and the module claims nothing isotropic.

## Locality

Everything that touches a region is window-scoped.  The global statements
(`SpatiallyConstant`, `gradient_add_eq_of_spatiallyConstant`) exist only because
they are the statements a *definition* of a normalized representative would be
phrased with; every statement that consumes a balance or produces regularity
takes its hypotheses through `AgreeOn` and reads them on one window.

Nothing here names an equation of a particular problem, a dimension beyond the
three frame directions, a boundary condition, or a residual.
-/

namespace Hypostructure.PDE.Solution.PressureNormalization

open TopologicalSpace TemperedDistribution LineDeriv
open Hypostructure.PDE.Localization
open Hypostructure.PDE.Distribution.CurlCalculus
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.SliceRestriction
open scoped SchwartzMap LineDeriv

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {window : Compacts Point}

/-! ## The ambiguity, named

`a(t)` is not a function here — a state of finite regularity need not be one.
What survives of "depends on time alone" without a function is exactly that
every *spatial* derivative annihilates the state, and that is what the balance
can and cannot see.  So the predicate is stated as annihilation by the frame's
derivatives, and the frame is the same bare family `Fin 3 → Point` the gradient
of `Distribution/CurlCalculus.lean` is written against: the ambiguity is
relative to the directions the balance differentiates in, and to nothing else.
-/

section Global

variable {frame : Fin 3 → Point}

/--
**Constant in the spatial directions.**

The additive ambiguity of the potential: a state killed by every derivative the
balance takes.  On a space–time this is "a function of time alone", but no
function is assumed to exist — only the annihilation, which is what every
statement below actually consumes.
-/
def SpatiallyConstant (frame : Fin 3 → Point) (state : 𝓢'(Point, Value)) : Prop :=
  ∀ axis : Fin 3, (∂_{frame axis} state : 𝓢'(Point, Value)) = 0

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- **The spatial gradient of a spatially constant state vanishes.**  This is
the predicate read as a single statement about the operator the balance uses,
rather than as three statements about directions, and it is the form
`gradient_add_eq_of_spatiallyConstant` consumes. -/
theorem SpatiallyConstant.gradient_eq_zero {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame state) :
    gradient frame state = 0 := by
  funext index
  exact constant index

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- Conversely, a vanishing gradient is exactly spatial constancy: the two
formulations carry the same information, so a consumer may supply either. -/
theorem spatiallyConstant_of_gradient_eq_zero {state : 𝓢'(Point, Value)}
    (vanishes : gradient frame state = 0) : SpatiallyConstant frame state :=
  fun axis => congrFun vanishes axis

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
theorem spatiallyConstant_zero : SpatiallyConstant frame (0 : 𝓢'(Point, Value)) :=
  fun axis => lineDerivOp_zero (frame axis)

/-! The ambiguities form a group, which is why "normalizing" is a well-posed
operation: one may compose two normalizations, or undo one. -/

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
theorem SpatiallyConstant.add {first second : 𝓢'(Point, Value)}
    (firstConstant : SpatiallyConstant frame first)
    (secondConstant : SpatiallyConstant frame second) :
    SpatiallyConstant frame (first + second) := fun axis => by
  rw [lineDerivOp_add, firstConstant axis, secondConstant axis, add_zero]

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
theorem SpatiallyConstant.neg {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame state) : SpatiallyConstant frame (-state) :=
  fun axis => by rw [lineDerivOp_neg, constant axis, neg_zero]

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
theorem SpatiallyConstant.sub {first second : 𝓢'(Point, Value)}
    (firstConstant : SpatiallyConstant frame first)
    (secondConstant : SpatiallyConstant frame second) :
    SpatiallyConstant frame (first - second) := fun axis => by
  rw [lineDerivOp_sub, firstConstant axis, secondConstant axis, sub_zero]

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- A spatially constant state is annihilated by the frame's Laplacian, since
each of its summands already contains one frame derivative.  This is what makes
the ambiguity invisible to the *Poisson* equation for the potential as well as
to the balance itself. -/
theorem SpatiallyConstant.scalarLaplacian_eq_zero {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame state) :
    scalarLaplacian frame state = 0 := by
  show ∑ axis, (∂_{frame axis} (∂_{frame axis} state) : 𝓢'(Point, Value)) = 0
  refine Finset.sum_eq_zero fun axis _ => ?_
  rw [constant axis, lineDerivOp_zero]

/-! ### Gauge invariance of the balance, globally

The one-line reason the whole module exists: adding an ambiguity to the
potential changes the gradient not at all, so it changes the momentum identity
not at all.
-/

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- **The gradient does not see the ambiguity.** -/
theorem gradient_add_eq_of_spatiallyConstant {potential gauge : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame gauge) :
    gradient frame (potential + gauge) = gradient frame potential := by
  rw [gradient_add, constant.gradient_eq_zero, add_zero]

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- **The balance does not see the ambiguity.**

If `p` satisfies the momentum identity against a velocity and a forcing, so does
`p + a` for every spatially constant `a`.  This is the statement that a
normalized representative may be substituted for a recovered one. -/
theorem balance_add_of_spatiallyConstant
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {potential gauge : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame gauge)
    (balance : ∀ index,
      heatOperator basis timeIndex (velocity index) + gradient frame potential index =
        forcing index)
    (index : Fin 3) :
    heatOperator basis timeIndex (velocity index) +
        gradient frame (potential + gauge) index = forcing index := by
  rw [gradient_add_eq_of_spatiallyConstant constant]
  exact balance index

end Global

/-! ## The ambiguity on a window

A residual owns its equation on its own window and nowhere else, so the version
of the predicate that is actually consumed is the one read through `AgreeOn`:
the spatial derivatives of the ambiguity are indistinguishable from zero *by the
tests the window supplies*.  Nothing is claimed off the window, and nothing
needs to be.
-/

section Window

variable {frame : Fin 3 → Point}

/--
**Constant in the spatial directions, on a window.**

The local form of `SpatiallyConstant`: no test supported in the window can tell
a spatial derivative of the state from zero.  This is strictly weaker than the
global predicate — it says nothing outside the window — and it is exactly what
two potentials solving the same balance on a window can be shown to differ by.
-/
def SpatiallyConstantOn (window : Compacts Point) (frame : Fin 3 → Point)
    (state : 𝓢'(Point, Value)) : Prop :=
  ∀ axis : Fin 3, AgreeOn window (∂_{frame axis} state) 0

/-- A global ambiguity is an ambiguity on every window. -/
theorem SpatiallyConstant.spatiallyConstantOn {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstant frame state) :
    SpatiallyConstantOn window frame state :=
  fun axis => AgreeOn.of_eq (constant axis)

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- Ambiguity on a window is inherited by every smaller window: fewer tests can
only fail to distinguish more. -/
theorem SpatiallyConstantOn.mono {smaller larger : Compacts Point}
    (subset : (smaller : Set Point) ⊆ (larger : Set Point))
    {state : 𝓢'(Point, Value)} (constant : SpatiallyConstantOn larger frame state) :
    SpatiallyConstantOn smaller frame state :=
  fun axis test supported => constant axis test (supported.trans subset)

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- The gradient of a window ambiguity agrees with zero there — the local form
of `SpatiallyConstant.gradient_eq_zero`, and the shape every balance statement
below consumes. -/
theorem SpatiallyConstantOn.agreeOn_gradient {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window frame state) (index : Fin 3) :
    AgreeOn window (gradient frame state index) 0 :=
  constant index

theorem spatiallyConstantOn_zero :
    SpatiallyConstantOn window frame (0 : 𝓢'(Point, Value)) :=
  spatiallyConstant_zero.spatiallyConstantOn

theorem SpatiallyConstantOn.add {first second : 𝓢'(Point, Value)}
    (firstConstant : SpatiallyConstantOn window frame first)
    (secondConstant : SpatiallyConstantOn window frame second) :
    SpatiallyConstantOn window frame (first + second) := fun axis => by
  rw [lineDerivOp_add]
  simpa using (firstConstant axis).add (secondConstant axis)

theorem SpatiallyConstantOn.neg {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window frame state) :
    SpatiallyConstantOn window frame (-state) := fun axis => by
  rw [lineDerivOp_neg]
  simpa using (constant axis).neg

theorem SpatiallyConstantOn.sub {first second : 𝓢'(Point, Value)}
    (firstConstant : SpatiallyConstantOn window frame first)
    (secondConstant : SpatiallyConstantOn window frame second) :
    SpatiallyConstantOn window frame (first - second) := fun axis => by
  rw [lineDerivOp_sub]
  simpa using (firstConstant axis).sub (secondConstant axis)

/-- **The frame Laplacian of a window ambiguity agrees with zero there.**

`AgreeOn.lineDerivOp` is the whole proof: each summand of the frame Laplacian
carries one frame derivative already agreeing with zero, and differentiating
cannot expose a difference the window hid. -/
theorem SpatiallyConstantOn.agreeOn_scalarLaplacian {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window frame state) :
    AgreeOn window (scalarLaplacian frame state) 0 := by
  have summands : ∀ axis ∈ (Finset.univ : Finset (Fin 3)),
      AgreeOn window (∂_{frame axis} (∂_{frame axis} state))
        ((fun _ : Fin 3 => (0 : 𝓢'(Point, Value))) axis) := by
    intro axis _
    refine AgreeOn.trans ((constant axis).lineDerivOp (frame axis)) (AgreeOn.of_eq ?_)
    exact lineDerivOp_zero (frame axis)
  have summed := AgreeOn.sum (Finset.univ : Finset (Fin 3)) summands
  simpa [scalarLaplacian] using summed

/-- **The spatial Laplacian of a window ambiguity agrees with zero there.**

The same fact on the operator `Solution/SliceRestriction.lean` bootstraps.  The
frame here is the spatial part of an orthonormal basis of a four-dimensional
space–time, which is exactly when the frame Laplacian *is* the spatial one
(`scalarLaplacian_eq_spatialLaplacian_of_card_eq_four`); no analysis is added,
only the identification of the two sums. -/
theorem SpatiallyConstantOn.agreeOn_spatialLaplacian
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) {state : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window (fun axis => basis (spatialIndex axis)) state) :
    AgreeOn window (spatialLaplacian basis timeIndex state) 0 := by
  rw [← scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex spatialIndex
    injective avoidsTime dimension state]
  exact constant.agreeOn_scalarLaplacian

/-! ### Gauge invariance of the balance, on the window -/

/-- **The gradient does not see the ambiguity, on the window.** -/
theorem agreeOn_gradient_add_of_spatiallyConstantOn
    {potential gauge : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window frame gauge) (index : Fin 3) :
    AgreeOn window (gradient frame (potential + gauge) index)
      (gradient frame potential index) := by
  have combined := AgreeOn.add (AgreeOn.refl (gradient frame potential index))
    (constant.agreeOn_gradient index)
  rw [gradient_add]
  simpa using combined

/--
**The balance does not see the ambiguity, on the window.**

`stokes:lem:pressure-normalization` in the only form a residual can use: the
momentum identity is read against tests supported in the window, and replacing
the potential by any representative differing from it by a window ambiguity
leaves the identity standing.  Nothing outside the window is assumed, and
nothing outside it is claimed.
-/
theorem agreeOn_balance_add_of_spatiallyConstantOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {potential gauge : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window frame gauge)
    (balance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) + gradient frame potential index)
      (forcing index))
    (index : Fin 3) :
    AgreeOn window
      (heatOperator basis timeIndex (velocity index) +
        gradient frame (potential + gauge) index) (forcing index) :=
  AgreeOn.trans
    (AgreeOn.add (AgreeOn.refl (heatOperator basis timeIndex (velocity index)))
      (agreeOn_gradient_add_of_spatiallyConstantOn constant index))
    (balance index)

/--
**The ambiguity is no larger than that.**

The converse of `agreeOn_balance_add_of_spatiallyConstantOn`, and the statement
that makes normalization a *choice among a known set* rather than an unbounded
one: two potentials satisfying the same balance on the same window differ there
by a spatially constant state, and by nothing else.  The velocity and the
forcing cancel because they are literally the same in the two hypotheses — no
regularity, no uniqueness theorem and no equation for the velocity is used.
-/
theorem spatiallyConstantOn_sub_of_agreeOn_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {potential normalized : 𝓢'(Point, Value)}
    (balance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) + gradient frame potential index)
      (forcing index))
    (normalizedBalance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) + gradient frame normalized index)
      (forcing index)) :
    SpatiallyConstantOn window frame (normalized - potential) := by
  intro axis
  have cancelled : AgreeOn window (gradient frame normalized axis)
      (gradient frame potential axis) := by
    have combined := (normalizedBalance axis).trans (balance axis).symm
    have subtracted := AgreeOn.sub combined
      (AgreeOn.refl (heatOperator basis timeIndex (velocity axis)))
    simpa using subtracted
  have difference := AgreeOn.sub cancelled (AgreeOn.refl (gradient frame potential axis))
  rw [lineDerivOp_sub]
  simpa [Distribution.CurlCalculus.gradient] using difference

end Window

/-! ## The payoff: spatial regularity is a property of the balance

`Solution/SliceRestriction.lean` delivers `SpatialSmoothOn` — every spatial
derivative at a fixed isotropic grade — for a potential whose spatial Laplacian
is smooth on a window.  The question this module answers is whether that
conclusion belongs to the potential that happened to be recovered or to the
balance itself, and the answer is the balance: a window ambiguity has a
vanishing spatial Laplacian *there*, so it is spatially smooth as soon as it has
a base grade, and the class is additive.

The base grade is a genuine hypothesis and is not removable.  `SpatialSmoothOn`
at gain zero *is* `SobolevOn` at the base grade, so a representative with no
base grade on the window cannot be spatially smooth there whatever the balance
says — which is again the time direction refusing to be controlled by a spatial
operator.
-/

section Payoff

variable {frame : Fin 3 → Point}

/-- The zero state is smooth on every region: localizing it gives zero, and zero
holds every Sobolev grade.  Needed because "agrees with zero on the window" is
turned into regularity by `AgreeOn.smoothOn`, which asks for the regularity of
the state agreed with. -/
theorem smoothOn_zero {region : Set Point} :
    SmoothOn region (0 : 𝓢'(Point, Value)) := by
  intro grade bump _
  have vanishes : localize bump (0 : 𝓢'(Point, Value)) = 0 := map_zero _
  rw [vanishes]
  exact Bessel.mem_sobolev.mp (AddSubgroup.zero_mem (Bessel.sobolev grade))

omit [DecidableEq Index] in
/-- Spatial regularity on a window is additive, because localizing is linear and
the spatial Sobolev class is closed under sums.  This is what lets a potential
be split into a representative and an ambiguity and reassembled. -/
theorem spatialSobolevOn_add {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {region : Set Point} {gain grade : ℝ} {first second : 𝓢'(Point, Value)}
    (firstHeld : SpatialSobolevOn basis timeIndex region gain grade first)
    (secondHeld : SpatialSobolevOn basis timeIndex region gain grade second) :
    SpatialSobolevOn basis timeIndex region gain grade (first + second) := by
  intro bump supported
  rw [localize_add]
  exact (firstHeld bump supported).add (secondHeld bump supported)

omit [DecidableEq Index] in
theorem spatialSmoothOn_add {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {region : Set Point} {grade : ℝ} {first second : 𝓢'(Point, Value)}
    (firstSmooth : SpatialSmoothOn basis timeIndex region grade first)
    (secondSmooth : SpatialSmoothOn basis timeIndex region grade second) :
    SpatialSmoothOn basis timeIndex region grade (first + second) :=
  fun gain => spatialSobolevOn_add (firstSmooth gain) (secondSmooth gain)

omit [DecidableEq Index] in
/-- Spatial smoothness contains its own base grade: the spatial scale at gain
zero is the isotropic one at the base grade.  This is why the base grade of the
*second* representative is the only extra hypothesis the transfer below needs —
the first one carries its own. -/
theorem sobolevOn_of_spatialSmoothOn {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (smooth : SpatialSmoothOn basis timeIndex region grade state) :
    SobolevOn region grade state :=
  spatialSobolevOn_zero_iff.mp (smooth 0)

/--
**A window ambiguity with a base grade is spatially smooth there.**

Its spatial Laplacian agrees with zero on the window, hence is smooth on any
region inside it, and the spatial bootstrap of `Solution/SliceRestriction.lean`
converts that into every spatial derivative at the base grade.  No time
regularity is produced, and by `exists_norm_sq_gt_mul_spatialSymbol` none can
be: the ambiguity is precisely the parasitic mode that theorem exhibits.
-/
theorem spatialSmoothOn_of_spatiallyConstantOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) {gauge : 𝓢'(Point, Value)}
    (constant : SpatiallyConstantOn window (fun axis => basis (spatialIndex axis)) gauge)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point)) {grade : ℝ}
    (held : SobolevOn region grade gauge) :
    SpatialSmoothOn basis timeIndex region grade gauge :=
  spatialSmoothOn_of_spatialLaplacian_smoothOn basis timeIndex held
    (AgreeOn.smoothOn
      (constant.agreeOn_spatialLaplacian basis timeIndex spatialIndex injective
        avoidsTime dimension)
      region_subset smoothOn_zero)

/--
**Spatial regularity does not depend on the representative.**

If two potentials differ by a window ambiguity, and one of them is spatially
smooth on a region inside that window, so is the other — provided the other has
a base grade there, which it must in any case in order for the conclusion to be
stated at all (`sobolevOn_of_spatialSmoothOn`).

This is the sense in which normalizing the potential is free: a stage may be
handed whichever representative a solve produced, and the spatial regularity it
reads off is the same.
-/
theorem spatialSmoothOn_congr_of_spatiallyConstantOn_sub
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {potential normalized : 𝓢'(Point, Value)}
    (gauge : SpatiallyConstantOn window (fun axis => basis (spatialIndex axis))
      (normalized - potential))
    {region : Set Point} (region_subset : region ⊆ (window : Set Point)) {grade : ℝ}
    (held : SobolevOn region grade normalized)
    (smooth : SpatialSmoothOn basis timeIndex region grade potential) :
    SpatialSmoothOn basis timeIndex region grade normalized := by
  have base : SobolevOn region grade potential := sobolevOn_of_spatialSmoothOn smooth
  have difference : SpatialSmoothOn basis timeIndex region grade (normalized - potential) :=
    spatialSmoothOn_of_spatiallyConstantOn basis timeIndex spatialIndex injective
      avoidsTime dimension gauge region_subset (held.sub base)
  have recombined := spatialSmoothOn_add smooth difference
  have rewritten : potential + (normalized - potential) = normalized := by abel
  rwa [rewritten] at recombined

/--
**The pressure-normalization step, end to end.**

Two potentials solving the *same* balance on a window — nothing else relating
them is assumed — have the same spatial regularity on any region inside it.  The
ambiguity between them is identified by
`spatiallyConstantOn_sub_of_agreeOn_balance` and then discharged by
`spatialSmoothOn_congr_of_spatiallyConstantOn_sub`.

This is what a stage consumes when it must not depend on which potential a
predecessor's solve returned: the balance, not the representative, carries the
conclusion.
-/
theorem spatialSmoothOn_normalized_of_agreeOn_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)}
    {potential normalized : 𝓢'(Point, Value)}
    (balance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) +
        gradient (fun axis => basis (spatialIndex axis)) potential index)
      (forcing index))
    (normalizedBalance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) +
        gradient (fun axis => basis (spatialIndex axis)) normalized index)
      (forcing index))
    {region : Set Point} (region_subset : region ⊆ (window : Set Point)) {grade : ℝ}
    (held : SobolevOn region grade normalized)
    (smooth : SpatialSmoothOn basis timeIndex region grade potential) :
    SpatialSmoothOn basis timeIndex region grade normalized :=
  spatialSmoothOn_congr_of_spatiallyConstantOn_sub basis timeIndex spatialIndex injective
    avoidsTime dimension
    (spatiallyConstantOn_sub_of_agreeOn_balance basis timeIndex balance normalizedBalance)
    region_subset held smooth

end Payoff

end Hypostructure.PDE.Solution.PressureNormalization
