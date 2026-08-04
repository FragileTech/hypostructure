import Hypostructure.PDE.Strategy.LocalRegularityChain

/-!
# The balance window certificate: the rotational half, packaged

**Nothing in this module is new mathematics.**  Every analytic step it needs is
already proved and already kernel-checked:

* `Strategy/LocalRegularityChain.smoothOn_curl_of_balance` — on one window, a
  balance `∂_t u − Δ_x u + ∇p = f` whose rotational part sits at some Sobolev
  grade on the outer ball and whose source is smooth there has a *smooth*
  rotational part on the inner ball.  This is the problem-agnostic form of the
  application's `spacetime_vorticity_smooth`: the curl kills the gradient
  (`heatOperator_curl_eq_curl_forcing`) and the parabolic certificate
  (`Solution/ParabolicRegularity.smoothOn_ball_of_heat_smoothOn`) does the rest.
* `Distribution/CurlCalculus.curl_smoothOn` — the bridge that lets the source be
  assumed smooth componentwise rather than after differentiation, exactly as the
  application's `curl_smoothOn` field is used.
* `Solution/LocalEmbedding.exists_contDiff_representative_of_smoothOn_ball` —
  from `SmoothOn` on a ball to a genuine `ContDiff ℝ ∞` function pairing with
  every test supported in a strictly smaller concentric ball.

What is *not* in the framework is the composition of the three, so an
application still has to run it by hand — three radii, one `choose` over
`Fin 3`, and a locally restated copy of the embedding lemma.  That composition
is problem-independent, so it is performed here once.

The corresponding statement for the **field itself** and the potential gradient
is `Strategy/LocalRegularityChain.exists_contDiff_representatives_of_balance`,
which already exists and is not duplicated.  It costs strictly more hypotheses —
divergence freedom, a grade for the field, a datum for its time derivative, a
four-dimensional count and the identification of the frame with three directions
of the basis — because closing the field needs them.  The rotational half needs
none of them, which is the only reason this module is separate from that one.

Nothing here is global, and nothing here names an equation, a residual, a
ledger, a route, a target, a boundary condition or a physical quantity.
-/

namespace Hypostructure.PDE.Solution.BalanceWindowCertificate

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.LocalEmbedding
open Hypostructure.PDE.Distribution.CurlCalculus
open Hypostructure.PDE.Strategy.LocalRegularityChain
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-! ## The composition

Three radii, as in every window statement of the framework: the classical
conclusion is wanted on `ball centre windowRadius`, the cutoff of the embedding
lives between it and `ball centre innerRadius`, and the two analytic hypotheses
are available on `ball centre outerRadius`.  The `choose` at the end is the step
that turns three component-wise existentials into one family, and it is the same
line the application already writes.
-/

/--
**The certificate, with nothing global in its hypotheses.**

The rotational part of a field has a classical `ContDiff ℝ ∞` representative on
the window ball as soon as, *on the outer ball*, it sits at some Sobolev grade
and its heat image is smooth.  There is no balance and no `source`: both are
whole-space objects a residual does not own.

This is the form a local residual can actually meet.  Its Sobolev input is
`Localization.sobolevOn_componentPlacement`, which reads the grade off the local
`L²` bound, and its heat input is the residual's own equation on its own window,
carried across by `SmoothOn.congr_sub`.
-/
theorem exists_contDiff_curl_representatives_of_heat_smoothOn {frame : Fin 3 → Point}
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (centre : Point)
    {windowRadius innerRadius outerRadius : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < innerRadius)
    (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {field : Fin 3 → 𝓢'(Point, Value)}
    (curl_held : ∀ index,
      SobolevOn (ball centre outerRadius) grade (curl frame field index))
    (heat_smooth : ∀ index,
      SmoothOn (ball centre outerRadius)
        (heatOperator basis timeIndex (curl frame field index))) :
    ∃ representative : Fin 3 → Point → Value,
      (∀ index, ContDiff ℝ ∞ (representative index)) ∧
        ∀ (index : Fin 3) (test : 𝓢(Point, ℂ)),
          tsupport (⇑test) ⊆ ball centre windowRadius →
            curl frame field index test =
              ∫ place : Point, test place • representative index place := by
  choose representative representative_smooth representative_pairs using
    fun index : Fin 3 =>
      exists_contDiff_representative_of_smoothOn_ball centre window_pos window_nested
        (smoothOn_curl_of_heat_smoothOn basis timeIndex centre nested curl_held
          heat_smooth index)
  exact ⟨representative, representative_smooth, representative_pairs⟩

/--
**The certificate from an equation that holds only on the window.**

Every hypothesis is ball-local, including the equation: `localized_balance` says
the vorticity equation `∂_t ω − Δω = curl f` holds *as seen by the bumps of the
outer ball*, which is precisely what a residual owns and precisely what
`SmoothOn` consults.  Nothing is assumed off the window, and no whole-space
identity appears anywhere in the statement.

The proof is `SmoothOn.congr_sub` --- states that the region's bumps cannot
tell apart have the same local regularity --- followed by the local certificate
above.  `curl_smoothOn` is the framework's bridge letting the source be assumed
smooth componentwise rather than after differentiation.
-/
theorem exists_contDiff_curl_representatives_of_localizedBalance
    {frame : Fin 3 → Point}
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (centre : Point)
    {windowRadius innerRadius outerRadius : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < innerRadius)
    (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {field forcing : Fin 3 → 𝓢'(Point, Value)}
    (curl_held : ∀ index,
      SobolevOn (ball centre outerRadius) grade (curl frame field index))
    (forcing_smooth : ∀ index,
      SmoothOn (ball centre outerRadius) (forcing index))
    (localized_balance : ∀ (index : Fin 3) (bump : Bump Point),
      tsupport bump.weight ⊆ ball centre outerRadius →
        localize bump
          (heatOperator basis timeIndex (curl frame field index) -
            curl frame forcing index) = 0) :
    ∃ representative : Fin 3 → Point → Value,
      (∀ index, ContDiff ℝ ∞ (representative index)) ∧
        ∀ (index : Fin 3) (test : 𝓢(Point, ℂ)),
          tsupport (⇑test) ⊆ ball centre windowRadius →
            curl frame field index test =
              ∫ place : Point, test place • representative index place :=
  exists_contDiff_curl_representatives_of_heat_smoothOn basis timeIndex centre
    window_pos window_nested nested curl_held
    fun index =>
      SmoothOn.congr_sub (localized_balance index)
        (curl_smoothOn forcing_smooth index)

/-- **The same certificate, from a whole-space balance.**  Kept for the case
where a genuine global identity happens to be available; a residual should reach
for `exists_contDiff_curl_representatives_of_heat_smoothOn` above instead. -/
theorem exists_contDiff_curl_representatives_of_balance {frame : Fin 3 → Point}
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (centre : Point)
    {windowRadius innerRadius outerRadius : ℝ}
    (window_pos : 0 < windowRadius) (window_nested : windowRadius < innerRadius)
    (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {field source : Fin 3 → 𝓢'(Point, Value)} {potential : 𝓢'(Point, Value)}
    (balance : ∀ index,
      heatOperator basis timeIndex (field index) + gradient frame potential index =
        source index)
    (curl_held : ∀ index,
      SobolevOn (ball centre outerRadius) grade (curl frame field index))
    (source_smooth : ∀ index, SmoothOn (ball centre outerRadius) (source index)) :
    ∃ representative : Fin 3 → Point → Value,
      (∀ index, ContDiff ℝ ∞ (representative index)) ∧
        ∀ (index : Fin 3) (test : 𝓢(Point, ℂ)),
          tsupport (⇑test) ⊆ ball centre windowRadius →
            curl frame field index test =
              ∫ place : Point, test place • representative index place := by
  choose representative representative_smooth representative_pairs using
    fun index : Fin 3 =>
      exists_contDiff_representative_of_smoothOn_ball centre window_pos window_nested
        (smoothOn_curl_of_balance basis timeIndex centre nested curl_held balance
          (fun axis => curl_smoothOn source_smooth axis) index)
  exact ⟨representative, representative_smooth, representative_pairs⟩

/-! ## The same thing, bundled

The structure below carries no hypothesis that the theorem above does not
carry, and its certificate is that theorem applied to its own fields.  Its only
purpose is that an application names its window once.
-/

/--
**One window of a parabolic balance**, as a single object: the window geometry
and the three hypotheses of `exists_contDiff_curl_representatives_of_balance`,
field for field.

`field`, `potential` and `source` are the three unknowns of a balance
`∂_t u − Δ_x u + ∇p = f`; `frame` is the triple of directions the rotational
operator is read against, unconstrained beyond living in the same space.
-/
structure BalanceWindow (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value]
    (Index : Type uIndex) [Fintype Index] [DecidableEq Index] where
  /-- The orthonormal basis the heat operator is read against. -/
  basis : OrthonormalBasis Index ℝ Point
  /-- The distinguished direction of the heat operator. -/
  timeIndex : Index
  /-- The three directions the rotational operator is read against. -/
  frame : Fin 3 → Point
  /-- The centre of the window. -/
  centre : Point
  /-- The ball on which the classical conclusion is wanted. -/
  windowRadius : ℝ
  /-- The ball the embedding's cutoff lives inside. -/
  innerRadius : ℝ
  /-- The ball on which the two analytic hypotheses are available. -/
  outerRadius : ℝ
  /-- The field the balance is solved for. -/
  field : Fin 3 → 𝓢'(Point, Value)
  /-- The scalar whose gradient the balance carries. -/
  potential : 𝓢'(Point, Value)
  /-- The right-hand side of the balance. -/
  source : Fin 3 → 𝓢'(Point, Value)
  /-- The grade the rotational part is known to sit at. -/
  grade : ℝ
  /-- The window is a genuine ball. -/
  window_pos : 0 < windowRadius
  /-- The window sits strictly inside the cutoff's ball. -/
  window_nested : windowRadius < innerRadius
  /-- The cutoff's ball sits inside the ball the hypotheses live on. -/
  nested : innerRadius ≤ outerRadius
  /-- **(a)** The balance, as an identity of states. -/
  balance : ∀ index,
    heatOperator basis timeIndex (field index) + gradient frame potential index =
      source index
  /-- **(b)** The rotational part sits at some grade on the outer ball. -/
  curl_held : ∀ index,
    SobolevOn (ball centre outerRadius) grade (curl frame field index)
  /-- **(c)** The source is smooth on the outer ball. -/
  source_smooth : ∀ index, SmoothOn (ball centre outerRadius) (source index)

variable (window : BalanceWindow Point Value Index)

/-- The rotational part of a balance window is smooth on the cutoff's ball.
This is `smoothOn_curl_of_balance` read off the bundle. -/
theorem BalanceWindow.smoothOn_curl (index : Fin 3) :
    SmoothOn (ball window.centre window.innerRadius)
      (curl window.frame window.field index) :=
  smoothOn_curl_of_balance window.basis window.timeIndex window.centre window.nested
    window.curl_held window.balance
    (fun axis => curl_smoothOn window.source_smooth axis) index

/-- **The certificate of a balance window**: the rotational part is a genuine
`ContDiff ℝ ∞` field on the window ball.  This is
`exists_contDiff_curl_representatives_of_balance` read off the bundle, so an
application supplies its balance and nothing else. -/
theorem BalanceWindow.exists_contDiff_curl_representatives :
    ∃ representative : Fin 3 → Point → Value,
      (∀ index, ContDiff ℝ ∞ (representative index)) ∧
        ∀ (index : Fin 3) (test : 𝓢(Point, ℂ)),
          tsupport (⇑test) ⊆ ball window.centre window.windowRadius →
            curl window.frame window.field index test =
              ∫ place : Point, test place • representative index place :=
  exists_contDiff_curl_representatives_of_balance window.basis window.timeIndex
    window.centre window.window_pos window.window_nested window.nested
    window.balance window.curl_held window.source_smooth

end Hypostructure.PDE.Solution.BalanceWindowCertificate
