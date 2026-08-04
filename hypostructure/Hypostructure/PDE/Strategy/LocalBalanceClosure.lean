import Hypostructure.PDE.Localization.BalanceTransport
import Hypostructure.PDE.Strategy.LocalRegularityChain
import Hypostructure.PDE.Solution.SliceRestriction

/-!
# The local chain, fed by a baseline's own balance

`Strategy/LocalRegularityChain.lean` proves the parabolic bootstrap on one
window and asks for its inputs on the tempered carrier: a Sobolev grade for the
vorticity, and smoothness of the heat image of the vorticity.  A registered
baseline does not speak that language --- it carries a balance on `𝓓'(Ω, V)`
and an `L²_loc` datum --- and `Localization/BalanceTransport.lean` is the
translation.

This module spends the translation on the chain.  Its statements take **only**
what a baseline has:

* the local balance `localHeatOperator (localCurl u) = localCurl f`, which is
  the curl of the momentum identity --- the step at which the potential drops
  out;
* a Sobolev grade for the bridged field, which the `L²_loc` datum supplies at
  grade zero through `Localization/PlacementOfBaseline.lean`;
* smoothness of the bridged forcing, which is the problem's data hypothesis.

and produce smoothness of the vorticity on a strictly smaller concentric ball.
Every hypothesis and the conclusion name one ball inside one window.  Nothing
is assumed about the field anywhere else, and no whole-space identity between
states appears at any point --- which is the whole reason the transport layer
exists.
-/

namespace Hypostructure.PDE.Strategy.LocalBalanceClosure

open Metric TopologicalSpace
open Hypostructure.PDE.Localization
open Hypostructure.PDE.Distribution.CurlCalculus
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open scoped Distributions SchwartzMap LineDeriv ContDiff

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [SecondCountableTopology Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {domain : Opens Point} {window : Compacts Point}

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/--
**The vorticity is smooth on the inner ball.**

`stokes:cor:vorticity-smoothing`, assembled from a baseline's own data.  The
three inputs are the local balance for the curl, a Sobolev grade for the
bridged field, and smoothness of the bridged forcing's curl; the output is the
hypothesis the next stage of `LocalRegularityChain` consumes.

Both translations happen here and only here: `sobolevOn_curl` prices the
rotational datum out of the field's own grade and `AgreeOn.sobolevOn` moves it
onto the curl of the bridged field, while
`smoothOn_heatOperator_curl_of_localBalance` turns the balance into the
bootstrap's `heat_smooth`.  The bootstrap itself is unchanged.
-/
theorem smoothOn_curl_of_localBalance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (frame : Fin 3 → Point)
    (field forcing : Fin 3 → 𝓓'(domain, Value))
    (balance : ∀ index,
      localHeatOperator basis timeIndex (localCurl frame field index) =
        localCurl frame forcing index)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    (centre : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    (ball_inside : ball centre outer ⊆ (window : Set Point))
    {grade : ℝ}
    (held : ∀ index, SobolevOn (ball centre outer) grade
      (temperedOfLocal cutoff inside (field index)))
    (forcing_smooth : ∀ index, SmoothOn (ball centre outer)
      (temperedOfLocal cutoff inside (localCurl frame forcing index)))
    (index : Fin 3) :
    SmoothOn (ball centre inner)
      (curl frame (fun axis => temperedOfLocal cutoff inside (field axis))
        index) :=
  LocalRegularityChain.smoothOn_curl_of_heat_smoothOn basis timeIndex centre
    nested (sobolevOn_curl (frame := frame) held)
    (smoothOn_heatOperator_curl_of_localBalance cutoff inside basis timeIndex
      frame field forcing balance unit ball_inside forcing_smooth)
    index

/-! ## Incompressibility is only needed on the window

`LocalRegularityChain.smoothOn_laplacian_of_smoothOn_curl` asks for
`divergence frame velocity = 0` as an identity of states on all of `Point`.  A
residual owns its equation only on its own window, so that hypothesis is not
one a baseline can supply.  It does not have to: the div--curl identity
`curl curl = grad div − Δ` is global, and agreement of the divergence with zero
on the window is enough to read it there.
-/

/-- **The div--curl identity, on the window.**  Where the divergence agrees
with zero, the Laplacian agrees with minus the double curl.  `AgreeOn.gradient`
does the only work: a gradient cannot see a difference the window already
hides. -/
theorem agreeOn_laplacian_neg_curl_curl {frame : Fin 3 → Point}
    {velocity : Fin 3 → 𝓢'(Point, Value)}
    (divergence_free : AgreeOn window (divergence frame velocity) 0)
    (index : Fin 3) :
    AgreeOn window (laplacian frame velocity index)
      (-(curl frame (curl frame velocity) index)) := by
  have expand := congrFun (curl_curl (frame := frame) velocity) index
  have rearranged :
      laplacian frame velocity index =
        gradient frame (divergence frame velocity) index -
          curl frame (curl frame velocity) index := by
    rw [expand]
    simp only [Pi.sub_apply]
    abel
  rw [rearranged]
  have gradient_zero : AgreeOn window
      (gradient frame (divergence frame velocity) index)
      (gradient frame (0 : 𝓢'(Point, Value)) index) :=
    divergence_free.gradient index
  have vanishes : gradient frame (0 : 𝓢'(Point, Value)) index = 0 := by
    simpa using (map_zero (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Point, Value)
      (frame index)))
  refine AgreeOn.trans (AgreeOn.sub gradient_zero (AgreeOn.refl _)) ?_
  rw [vanishes]
  exact AgreeOn.of_eq (by abel)

/-- **The Laplacian of the velocity is smooth on the window**, from the double
curl and incompressibility *there*.  This is
`LocalRegularityChain.smoothOn_laplacian_of_smoothOn_curl` with its global
hypothesis replaced by the local one. -/
theorem smoothOn_laplacian_of_smoothOn_curl {frame : Fin 3 → Point}
    {velocity : Fin 3 → 𝓢'(Point, Value)}
    (divergence_free : AgreeOn window (divergence frame velocity) 0)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point))
    (curl_smooth : ∀ index,
      SmoothOn region (curl frame (curl frame velocity) index))
    (index : Fin 3) :
    SmoothOn region (laplacian frame velocity index) :=
  AgreeOn.smoothOn (agreeOn_laplacian_neg_curl_curl divergence_free index)
    region_subset (curl_smooth index).neg

/-! ## The potential, on the spatial scale

Taking the divergence of the momentum identity kills the heat term wherever the
field is incompressible and leaves `Δ_x p = div f`: a Poisson equation for the
potential in the *spatial* variables only.

`Solution/SliceRestriction.lean` is the scale that equation lives on.  It does
not pretend the spatial operator gains isotropically ---
`exists_norm_sq_gt_mul_spatialSymbol` proves it does not --- and instead
bootstraps `1 − Δ_x` on its own terms, delivering `SpatialSmoothOn`: every
spatial derivative, at a fixed isotropic grade.  That is the strongest
conclusion a purely spatial operator can give, and it is what the potential
needs.

The only thing missing between a baseline and that bootstrap was the window: a
residual owns `Δ_x p = div f` on its own window, not on all of `Point`.
`AgreeOn` closes the gap.
-/

/-- The heat operator kills zero: `heatOperator_sub` at equal arguments. -/
theorem heatOperator_zero (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    heatOperator basis timeIndex (0 : 𝓢'(Point, Value)) = 0 := by
  simpa using LocalRegularityChain.heatOperator_sub basis timeIndex
    (0 : 𝓢'(Point, Value)) 0

/-- …and is additive, which `heatOperator_sub` gives through the negative. -/
theorem heatOperator_add (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (first second : 𝓢'(Point, Value)) :
    heatOperator basis timeIndex (first + second) =
      heatOperator basis timeIndex first + heatOperator basis timeIndex second := by
  have negation : heatOperator basis timeIndex (-second) =
      -heatOperator basis timeIndex second := by
    simpa [heatOperator_zero] using
      LocalRegularityChain.heatOperator_sub basis timeIndex
        (0 : 𝓢'(Point, Value)) second
  have expanded := LocalRegularityChain.heatOperator_sub basis timeIndex first
    (-second)
  rw [negation] at expanded
  simpa [sub_neg_eq_add] using expanded

/-- **The divergence commutes with the heat operator**, the companion of
`LocalRegularityChain.curl_heatOperator`.  Both are built from the same two
facts: the heat operator is additive and it commutes with a line derivative. -/
theorem divergence_heatOperator (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {frame : Fin 3 → Point}
    (field : Fin 3 → 𝓢'(Point, Value)) :
    divergence frame (fun index => heatOperator basis timeIndex (field index)) =
      heatOperator basis timeIndex (divergence frame field) := by
  show ∑ index, ∂_{frame index} (heatOperator basis timeIndex (field index)) =
    heatOperator basis timeIndex (∑ index, ∂_{frame index} (field index))
  simp only [Fin.sum_univ_three, heatOperator_add,
    heatOperator_lineDerivOp_comm]

/--
**The potential solves a Poisson equation on the window.**

The divergence of the momentum identity.  Where the field is incompressible the
heat term disappears --- `divergence_heatOperator` moves the divergence inside
and `AgreeOn.heatOperator` sends it to zero --- and `divergence_gradient` turns
what is left into the scalar Laplacian of the potential, which on a
four-dimensional space-time *is* the spatial one.

Both hypotheses are read on the window and nowhere else, which is exactly the
form a residual carries them in.
-/
theorem agreeOn_spatialLaplacian_potential
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {potential : 𝓢'(Point, Value)}
    (balance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) +
        gradient (fun axis => basis (spatialIndex axis)) potential index)
      (forcing index))
    (divergence_free : AgreeOn window
      (divergence (fun axis => basis (spatialIndex axis)) velocity) 0) :
    AgreeOn window (spatialLaplacian basis timeIndex potential)
      (divergence (fun axis => basis (spatialIndex axis)) forcing) := by
  set frame : Fin 3 → Point := fun axis => basis (spatialIndex axis) with frame_def
  have divided := AgreeOn.divergence (frame := frame) balance
  have split : divergence frame
      (fun index => heatOperator basis timeIndex (velocity index) +
        gradient frame potential index) =
      heatOperator basis timeIndex (divergence frame velocity) +
        scalarLaplacian frame potential := by
    rw [show (fun index => heatOperator basis timeIndex (velocity index) +
        gradient frame potential index) =
      (fun index => heatOperator basis timeIndex (velocity index)) +
        gradient frame potential from rfl,
      divergence_add, divergence_heatOperator, divergence_gradient]
  rw [split] at divided
  have heat_zero : AgreeOn window
      (heatOperator basis timeIndex (divergence frame velocity)) 0 :=
    AgreeOn.trans (divergence_free.heatOperator basis timeIndex)
      (AgreeOn.of_eq (heatOperator_zero basis timeIndex))
  have identify : scalarLaplacian frame potential =
      spatialLaplacian basis timeIndex potential :=
    scalarLaplacian_eq_spatialLaplacian_of_card_eq_four basis timeIndex
      spatialIndex injective avoidsTime dimension potential
  refine AgreeOn.trans (AgreeOn.of_eq identify.symm) (AgreeOn.trans ?_ divided)
  simpa using (AgreeOn.add heat_zero.symm (AgreeOn.refl
    (scalarLaplacian frame potential)))

/-- **The potential is spatially smooth on the inner ball.**

The Poisson identity is taken *on the window*, which is the only form a
residual has.  `AgreeOn.smoothOn` turns it into the hypothesis
`spatialSmoothOn_ball_of_spatialLaplacian_smoothOn` consumes, and the spatial
bootstrap does the rest.

No time regularity is claimed, and by `exists_norm_sq_gt_mul_spatialSymbol`
none can be. -/
theorem spatialSmoothOn_of_localPoisson
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {potential source : 𝓢'(Point, Value)}
    (poisson : AgreeOn window
      (spatialLaplacian basis timeIndex potential) source)
    (centre : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    (ball_inside : ball centre outer ⊆ (window : Set Point))
    {grade : ℝ}
    (held : SobolevOn (ball centre outer) grade potential)
    (source_smooth : SmoothOn (ball centre outer) source) :
    Solution.SliceRestriction.SpatialSmoothOn basis timeIndex
      (ball centre inner) grade potential :=
  Solution.SliceRestriction.spatialSmoothOn_ball_of_spatialLaplacian_smoothOn
    basis timeIndex centre nested held
    (AgreeOn.smoothOn poisson ball_inside source_smooth)

/--
**The pressure stage, in one step.**

`stokes:lem:local-CZ-pressure` for the local windows of a singularity profile:
the momentum identity and incompressibility, both read only on the window, plus
a Sobolev grade for the potential and smoothness of the forcing's divergence,
give every spatial derivative of the potential on the inner ball.

This is the whole backend the stage needs.  Nothing outside the window is
assumed and nothing outside it is concluded.
-/
theorem spatialSmoothOn_potential_of_localBalance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4)
    {velocity forcing : Fin 3 → 𝓢'(Point, Value)} {potential : 𝓢'(Point, Value)}
    (balance : ∀ index, AgreeOn window
      (heatOperator basis timeIndex (velocity index) +
        gradient (fun axis => basis (spatialIndex axis)) potential index)
      (forcing index))
    (divergence_free : AgreeOn window
      (divergence (fun axis => basis (spatialIndex axis)) velocity) 0)
    (centre : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    (ball_inside : ball centre outer ⊆ (window : Set Point))
    {grade : ℝ}
    (held : SobolevOn (ball centre outer) grade potential)
    (forcing_smooth : SmoothOn (ball centre outer)
      (divergence (fun axis => basis (spatialIndex axis)) forcing)) :
    Solution.SliceRestriction.SpatialSmoothOn basis timeIndex
      (ball centre inner) grade potential :=
  spatialSmoothOn_of_localPoisson basis timeIndex
    (agreeOn_spatialLaplacian_potential basis timeIndex spatialIndex injective
      avoidsTime dimension balance divergence_free)
    centre nested ball_inside held forcing_smooth

end Hypostructure.PDE.Strategy.LocalBalanceClosure
