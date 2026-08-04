import Hypostructure.PDE.Localization.WindowAgreement
import Hypostructure.PDE.Distribution.CurlCalculus
import Hypostructure.PDE.Solution.ParabolicRegularity

/-!
# A local balance becomes a tempered one on the inner window

`Localization/TemperedBridge.lean` carries a distribution on a window to a
tempered distribution, and
`temperedOfLocal_lineDerivOp_apply_of_eqOn_one` says the carry commutes with
differentiation where the cutoff is one.  This module spends that on the one
operator the framework's regularity theory is written in: the heat operator
`∂_t − Δ_x`.

A baseline states its equation on the local carrier `𝓓'(Ω, V)`, because that
is where a represented equation lives --- it is a statement about test
functions supported in the object's own domain, and nothing outside it is
claimed.  Every solve the framework proves acts on `𝓢'(Point, V)`.  The two
are joined here, and only here:

* `localHeatOperator` --- the same formula as
  `ParabolicRegularity.heatOperator`, written with `Distribution.lineDerivCLM`
  on the local carrier;
* `temperedOfLocal_heatOperator_apply_of_eqOn_one` --- the two agree across the
  bridge, tested against anything supported where the cutoff is one;
* `heatOperator_temperedOfLocal_eq_of_balance` --- consequently a *local*
  balance `∂_t u − Δ_x u = f` is a *tempered* balance between the bridged
  states, on the inner window.

Locality is not weakened anywhere: every statement is read against test
functions supported in the window, and the conclusion says nothing about the
states off it.  What the bridge changes is only which carrier the fact is
phrased on, so that the parabolic bootstrap can consume it.

No equation, dimension, application or residual appears.
-/

namespace Hypostructure.PDE.Localization

open TopologicalSpace
open Hypostructure.PDE.Solution.ParabolicRegularity
open scoped Distributions SchwartzMap LineDeriv

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [SecondCountableTopology Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {domain : Opens Point} {window : Compacts Point}

section Balance

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- **The heat operator on the local carrier.**

Literally `ParabolicRegularity.heatOperator`'s formula with `lineDerivOp`
replaced by `Distribution.lineDerivCLM`: a time derivative minus the sum of the
second derivatives along the remaining basis directions.  Writing it out is
what lets a baseline state its balance without ever mentioning a tempered
distribution. -/
noncomputable def localHeatOperator (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (local_ : 𝓓'(domain, Value)) : 𝓓'(domain, Value) :=
  (Distribution.lineDerivCLM (basis timeIndex) :
      𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) local_ -
    ∑ index ∈ Finset.univ.erase timeIndex,
      (Distribution.lineDerivCLM (basis index) :
          𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
        ((Distribution.lineDerivCLM (basis index) :
          𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) local_)

/--
**The bridge carries the heat operator.**

Read against a test function supported where the cutoff is one, the tempered
heat operator applied to the bridged object equals the bridge of the local heat
operator.  The time derivative is one application of the connector, the
Laplacian is a finite sum of its iterated form, and the difference and the sum
pass through by linearity of the bridge.

No smoothness of the object is assumed --- this is an identity of functionals,
not a regularity statement.
-/
theorem temperedOfLocal_heatOperator_apply_of_eqOn_one
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ : 𝓓'(domain, Value)) (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    heatOperator basis timeIndex (temperedOfLocal cutoff inside local_) test =
      temperedOfLocal cutoff inside
        (localHeatOperator basis timeIndex local_) test := by
  rw [localHeatOperator, temperedOfLocal_sub, temperedOfLocal_sum, heatOperator,
    spatialLaplacian]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
  rw [temperedOfLocal_lineDerivOp_apply_of_eqOn_one cutoff inside local_
    (basis timeIndex) test supported unit]
  refine congrArg _ (Finset.sum_congr rfl fun index _ => ?_)
  exact temperedOfLocal_lineDerivOp_lineDerivOp_apply_of_eqOn_one cutoff inside
    local_ (basis index) (basis index) test supported unit

/--
**A local balance is a tempered balance on the inner window.**

This is the statement a registered baseline hands to the framework's parabolic
bootstrap.  The hypothesis is the balance the baseline already carries, on its
own carrier; the conclusion is the same balance between bridged states, valid
against every test function supported where the cutoff is one --- that is, on
the inner window and nowhere else, which is all a local argument ever uses.
-/
theorem heatOperator_temperedOfLocal_apply_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ forcing : 𝓓'(domain, Value))
    (balance : localHeatOperator basis timeIndex local_ = forcing)
    (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    heatOperator basis timeIndex (temperedOfLocal cutoff inside local_) test =
      temperedOfLocal cutoff inside forcing test := by
  rw [temperedOfLocal_heatOperator_apply_of_eqOn_one cutoff inside basis
    timeIndex local_ test supported unit, balance]

/-- The same, stated as the vanishing of the difference --- the form
`Solution.InteriorRegularity.SmoothOn.congr_sub` consumes when it upgrades
"the forcing is smooth" to "the state is smooth". -/
theorem heatOperator_temperedOfLocal_sub_apply_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ forcing : 𝓓'(domain, Value))
    (balance : localHeatOperator basis timeIndex local_ = forcing)
    (test : 𝓢(Point, ℂ))
    (supported : tsupport (test : Point → ℂ) ⊆ window)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    (heatOperator basis timeIndex (temperedOfLocal cutoff inside local_) -
        temperedOfLocal cutoff inside forcing) test = 0 := by
  rw [ContinuousLinearMap.sub_apply,
    heatOperator_temperedOfLocal_apply_of_balance cutoff inside basis timeIndex
      local_ forcing balance test supported unit, sub_self]

/-! ## Into the bootstrap's own vocabulary

`Solution/InteriorRegularity.lean` reads a state only through bumps, and
`SmoothOn.congr_sub` upgrades "the forcing is smooth here" to "the state's heat
image is smooth here" as soon as the two agree under every bump supported in
the region.  That agreement is exactly the window balance above, because
multiplying a probe by a bump supported in the window produces a probe
supported in the window --- which is the only hypothesis the transport needs.

The result is the hypothesis `ParabolicRegularity.smoothOn_ball_of_heat_smoothOn`
and `Strategy.LocalRegularityChain.smoothOn_curl_of_heat_smoothOn` consume, so
after this a baseline's own local balance feeds the parabolic bootstrap with
nothing global anywhere on the path.
-/

open Hypostructure.PDE.Solution.InteriorRegularity in
/-- **The window balance, read by a bump.**  Every localization of the
difference between the bridged heat image and the bridged forcing vanishes, for
bumps supported in the window. -/
theorem localize_heatOperator_temperedOfLocal_sub_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ forcing : 𝓓'(domain, Value))
    (balance : localHeatOperator basis timeIndex local_ = forcing)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    (bump : Bump Point) (supported : tsupport bump.weight ⊆ (window : Set Point)) :
    localize bump
      (heatOperator basis timeIndex (temperedOfLocal cutoff inside local_) -
        temperedOfLocal cutoff inside forcing) = 0 := by
  ext probe
  rw [localize_eq, TemperedDistribution.smulLeftCLM_apply_apply,
    ContinuousLinearMap.zero_apply]
  exact heatOperator_temperedOfLocal_sub_apply_of_balance cutoff inside basis
    timeIndex local_ forcing balance _
    ((AgreeOn.tsupport_smulLeftCLM_subset bump probe).trans supported) unit

open Hypostructure.PDE.Solution.InteriorRegularity in
/--
**A baseline's local balance makes the bridged heat image smooth on the
window.**

This is the last connector before the parabolic bootstrap: its hypothesis is
the balance the baseline already carries plus smoothness of the bridged
forcing, and its conclusion is literally the `heat_smooth` argument of
`smoothOn_ball_of_heat_smoothOn`.

`region` is any subset of the window --- in practice the inner ball --- so the
statement is read on the window and asserts nothing outside it.
-/
theorem smoothOn_heatOperator_temperedOfLocal_of_balance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ forcing : 𝓓'(domain, Value))
    (balance : localHeatOperator basis timeIndex local_ = forcing)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point))
    (forcing_smooth : SmoothOn region (temperedOfLocal cutoff inside forcing)) :
    SmoothOn region
      (heatOperator basis timeIndex (temperedOfLocal cutoff inside local_)) :=
  SmoothOn.congr_sub
    (fun bump supported =>
      localize_heatOperator_temperedOfLocal_sub_of_balance cutoff inside basis
        timeIndex local_ forcing balance unit bump
        (supported.trans region_subset))
    forcing_smooth

end Balance

/-! ## The operator algebra, once

With `AgreeOn` in hand every named operator gets two facts and no argument of
its own:

* a **congruence** --- states agreeing on the window have images agreeing on
  the window, because each operator is a finite combination of derivatives and
  vector-space operations, and `AgreeOn` is closed under both;
* a **transport** --- the bridge carries the operator, which is the string
  connector plus linearity of the bridge.

Composites then need nothing: `AgreeOn.trans` chains a congruence onto a
transport, so `heatOperator (curl (bridged u))` reaches
`bridge (localHeat (localCurl u))` in two steps, and any other composite the
same way.  This is what makes the layer reusable across problems: a new
equation names a different combination of the same operators, and every
combination is already covered.
-/

section Operators

open Hypostructure.PDE.Distribution.CurlCalculus

variable {frame : Fin 3 → Point}

/-- **Congruence for the heat operator.** -/
theorem AgreeOn.heatOperator {window : Compacts Point}
    {first second : 𝓢'(Point, Value)} (agree : AgreeOn window first second)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    AgreeOn window (Solution.ParabolicRegularity.heatOperator basis timeIndex first)
      (Solution.ParabolicRegularity.heatOperator basis timeIndex second) :=
  (agree.lineDerivOp (basis timeIndex)).sub
    (AgreeOn.sum _ fun index _ =>
      (agree.lineDerivOp (basis index)).lineDerivOp (basis index))

/-- **Congruence for the curl.** -/
theorem AgreeOn.curl {window : Compacts Point}
    {first second : Fin 3 → 𝓢'(Point, Value)}
    (agree : ∀ index, AgreeOn window (first index) (second index))
    (index : Fin 3) :
    AgreeOn window (curl frame first index) (curl frame second index) :=
  ((agree (index + 2)).lineDerivOp (frame (index + 1))).sub
    ((agree (index + 1)).lineDerivOp (frame (index + 2)))

/-- **Congruence for the gradient.** -/
theorem AgreeOn.gradient {window : Compacts Point}
    {first second : 𝓢'(Point, Value)} (agree : AgreeOn window first second)
    (index : Fin 3) :
    AgreeOn window (gradient frame first index) (gradient frame second index) :=
  agree.lineDerivOp (frame index)

/-- **Congruence for the divergence.** -/
theorem AgreeOn.divergence {window : Compacts Point}
    {first second : Fin 3 → 𝓢'(Point, Value)}
    (agree : ∀ index, AgreeOn window (first index) (second index)) :
    AgreeOn window (divergence frame first) (divergence frame second) :=
  AgreeOn.sum _ fun index _ => (agree index).lineDerivOp (frame index)

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- **The bridge carries the heat operator**, as an agreement.  The time
derivative is a one-element string, each summand of the Laplacian a
two-element one, and the difference and the sum are moved through the bridge by
`temperedOfLocal_sub` and `temperedOfLocal_sum`. -/
theorem agreeOn_heatOperator_temperedOfLocal
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ : 𝓓'(domain, Value))
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    AgreeOn window
      (Solution.ParabolicRegularity.heatOperator basis timeIndex
        (temperedOfLocal cutoff inside local_))
      (temperedOfLocal cutoff inside
        (localHeatOperator basis timeIndex local_)) :=
  fun test supported =>
    temperedOfLocal_heatOperator_apply_of_eqOn_one cutoff inside basis timeIndex
      local_ test supported unit

/-- The curl on the local carrier, the same cyclic formula as
`CurlCalculus.curl`. -/
noncomputable def localCurl (frame : Fin 3 → Point)
    (field : Fin 3 → 𝓓'(domain, Value)) : Fin 3 → 𝓓'(domain, Value) :=
  fun index =>
    (Distribution.lineDerivCLM (frame (index + 1)) :
        𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) (field (index + 2)) -
      (Distribution.lineDerivCLM (frame (index + 2)) :
        𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) (field (index + 1))

/-- **The bridge carries the curl**, as an agreement. -/
theorem agreeOn_curl_temperedOfLocal (frame : Fin 3 → Point)
    (field : Fin 3 → 𝓓'(domain, Value))
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    (index : Fin 3) :
    AgreeOn window
      (curl frame (fun axis => temperedOfLocal cutoff inside (field axis)) index)
      (temperedOfLocal cutoff inside (localCurl frame field index)) := by
  refine AgreeOn.trans
    (((agreeOn_lineDerivOp_temperedOfLocal cutoff inside (field (index + 2))
        (frame (index + 1)) unit).sub
      (agreeOn_lineDerivOp_temperedOfLocal cutoff inside (field (index + 1))
        (frame (index + 2)) unit)))
    (AgreeOn.of_eq ?_)
  rw [localCurl, temperedOfLocal_sub]

/--
**The composite the vorticity route needs.**

`heatOperator (curl (bridged field))` agrees on the window with the bridge of
`localHeatOperator (localCurl field)`.  Two applications of `AgreeOn.trans`: the
curl transport lifted through the heat operator by its congruence, then the
heat transport.

Nothing here is about any particular equation.  A problem whose balance names a
different composite gets it from the same two combinators.
-/
theorem agreeOn_heatOperator_curl_temperedOfLocal
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (frame : Fin 3 → Point) (field : Fin 3 → 𝓓'(domain, Value))
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) (index : Fin 3) :
    AgreeOn window
      (Solution.ParabolicRegularity.heatOperator basis timeIndex
        (curl frame (fun axis => temperedOfLocal cutoff inside (field axis))
          index))
      (temperedOfLocal cutoff inside
        (localHeatOperator basis timeIndex (localCurl frame field index))) :=
  AgreeOn.trans
    ((agreeOn_curl_temperedOfLocal cutoff inside frame field unit
      index).heatOperator basis timeIndex)
    (agreeOn_heatOperator_temperedOfLocal cutoff inside basis timeIndex _ unit)

open Hypostructure.PDE.Solution.InteriorRegularity in
/-- **The curl costs one grade.**  It is a difference of two first derivatives,
and `SobolevOn.lineDerivOp` prices each of them, so no separate estimate is
needed for the rotational datum. -/
theorem sobolevOn_curl {region : Set Point} {grade : ℝ}
    {field : Fin 3 → 𝓢'(Point, Value)}
    (held : ∀ index, SobolevOn region grade (field index)) (index : Fin 3) :
    SobolevOn region (grade - 1) (curl frame field index) :=
  ((held (index + 2)).lineDerivOp (frame (index + 1))).sub
    ((held (index + 1)).lineDerivOp (frame (index + 2)))

open Hypostructure.PDE.Solution.InteriorRegularity in
/--
**The vorticity bootstrap's hypothesis, from a local balance.**

`Strategy.LocalRegularityChain.smoothOn_curl_of_heat_smoothOn` asks for the heat
image of the curl to be smooth on the outer ball and asks nothing else; this
supplies it from the balance a baseline already carries, on its own carrier.

The balance hypothesis is `localHeatOperator (localCurl u) = localCurl f` --- in
words, taking the curl of the momentum identity, which is where the potential
drops out.  Everything after that is the agreement algebra above.
-/
theorem smoothOn_heatOperator_curl_of_localBalance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (frame : Fin 3 → Point) (field forcing : Fin 3 → 𝓓'(domain, Value))
    (balance : ∀ index,
      localHeatOperator basis timeIndex (localCurl frame field index) =
        localCurl frame forcing index)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point))
    (forcing_smooth : ∀ index, SmoothOn region
      (temperedOfLocal cutoff inside (localCurl frame forcing index)))
    (index : Fin 3) :
    SmoothOn region
      (Solution.ParabolicRegularity.heatOperator basis timeIndex
        (curl frame (fun axis => temperedOfLocal cutoff inside (field axis))
          index)) :=
  AgreeOn.smoothOn
    ((agreeOn_heatOperator_curl_temperedOfLocal cutoff inside basis timeIndex
      frame field unit index).trans
      (AgreeOn.of_eq (congrArg _ (balance index))))
    region_subset (forcing_smooth index)

open Hypostructure.PDE.Solution.InteriorRegularity in
/-- The same for the velocity itself, which is what closes the last step of the
chain once the spatial Laplacian is known smooth. -/
theorem smoothOn_heatOperator_of_localBalance
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (local_ forcing : 𝓓'(domain, Value))
    (balance : localHeatOperator basis timeIndex local_ = forcing)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point))
    (forcing_smooth : SmoothOn region (temperedOfLocal cutoff inside forcing)) :
    SmoothOn region
      (Solution.ParabolicRegularity.heatOperator basis timeIndex
        (temperedOfLocal cutoff inside local_)) :=
  AgreeOn.smoothOn
    ((agreeOn_heatOperator_temperedOfLocal cutoff inside basis timeIndex local_
      unit).trans (AgreeOn.of_eq (congrArg _ balance)))
    region_subset forcing_smooth

open Hypostructure.PDE.Solution.InteriorRegularity in
/-- **The Sobolev input travels too.**  The bootstrap needs the curl to sit at
*some* grade on the outer ball; the bridged object's grade is the one the
baseline's `L²_loc` datum gives, and agreement carries it to the curl of the
bridged field. -/
theorem sobolevOn_curl_temperedOfLocal
    (frame : Fin 3 → Point) (field : Fin 3 → 𝓓'(domain, Value))
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1)
    {region : Set Point} (region_subset : region ⊆ (window : Set Point))
    {grade : ℝ}
    (held : ∀ index, SobolevOn region grade
      (temperedOfLocal cutoff inside (localCurl frame field index)))
    (index : Fin 3) :
    SobolevOn region grade
      (curl frame (fun axis => temperedOfLocal cutoff inside (field axis))
        index) :=
  AgreeOn.sobolevOn
    (agreeOn_curl_temperedOfLocal cutoff inside frame field unit index)
    region_subset (held index)

end Operators

end Hypostructure.PDE.Localization
