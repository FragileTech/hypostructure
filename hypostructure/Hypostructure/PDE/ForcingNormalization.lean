import Hypostructure.PDE.Solution.QuotientRecoveryData

/-!
# Normalizing the source: the curl-free part of a forcing is a potential shift

`Solution/QuotientRecoveryData.lean` builds the recovery relation
`NormalizedRecovery` and discharges its two identities from a lifting of the
*velocity's* harmonic component.  Its constructor
`NormalizedRecovery.ofLifting` still carries a fourth input,

> `forcing_harmonic_free : normalization.harmonicSlicePart forcing = 0`,

which by `LocalNormalization.normalized_iff_restrict_eq_quotientSlicePart` is
exactly `normalization.Normalized forcing`: a **gauge condition on the source**,
assumed rather than arranged.  Nothing in the recovery arranges it, because the
recovery never touches the source.

This module removes it, by the argument the appendix already gives for the
pressure normalization: *the curl-free part of the source is not an obstruction,
it is a potential shift*.  In a balance

> `evolution + ∇p = f`

the summand `∇ψ` may be moved from the right-hand side to the left,

> `evolution + ∇(p - ψ) = f - ∇ψ`,

and the first summand — the one carrying the field — is **literally unchanged**.
So a balance for `f` is a balance for the modified source `f - ∇ψ` with a
shifted potential, and every conclusion drawn about the field from the balance
is a conclusion about the same field.  Choosing `ψ` so that `∇ψ` restricts to
the window's harmonic projection of `f` makes the modified source normalized,
and `harmonicSlicePart` of it vanishes **as a theorem about the construction**.

## What is constructed

* `ForcingNormalization` — the construction.  Its data is a single scalar `ψ`
  together with the statement that `∇ψ` restricts to `harmonicSlicePart f` on
  the window.  This is the *same* shape of input the velocity side already
  takes (`NormalizedRecovery.ofLifting`'s `lifts`), and for the same reason: it
  represents the projection, it does not assume anything about `f`.
* `ForcingNormalization.normalizedForcing` — the modified source `f - ∇ψ`.
* `ForcingNormalization.harmonicSlicePart_normalizedForcing` — **the point**:
  `harmonicSlicePart (f - ∇ψ) = 0`, with no hypothesis on `f` whatsoever.
* `ForcingNormalization.balance_normalizedForcing` — the modified source solves
  the *same* balance with the shifted potential `p - ψ` and the *same*
  `evolution` term.  This is why the substitution is legitimate.
* `ForcingNormalization.curl_normalizedForcing` — the modified source has the
  same rotational datum as the original, because the discarded summand is a
  gradient.  This is why the vorticity half of any argument is untouched too.
* `ForcingNormalization.normalizedRecovery` — the corollary: the fourth input of
  `NormalizedRecovery.ofLifting` is discharged, and the recovery relation holds
  for the modified source with no gauge condition anywhere among the inputs.

## Where the last conditional input goes

`ForcingNormalization.ofGradientRepresentation` builds the construction **for
every source at once**, from a single named fact:

> every element of the window's harmonic kernel is `restrict (∇ψ)` for some
> scalar `ψ`.

That is the Poincaré/gradient-representation statement of the appendix — a
divergence-free curl-free field on a ball is the gradient of a harmonic
potential — and it is a genuine theorem about the geometry of a ball, not a
gauge choice.  `PDE/DivCurlPotential.lean` is where the framework proves the
analytic half of it (`hasFDerivAt_radialPotential`, the Poincaré lemma for
one-forms on a ball); it is deliberately **not** restated here, and is taken as
the explicit named parameter `represents` so that the two compose.

Nothing below names a dimension, a domain, or an equation.  The whole module is
parametric in the state space, the window's `L²` and the two operator targets,
exactly as `LocalNormalization` and `QuotientRecoveryData` are.
-/

namespace Hypostructure.PDE.DivCurl

/-! ## The gauge condition, read on the constructed splitting

One lemma that `PDE/DivCurl.lean` does not record: the normalization condition
and the vanishing of the harmonic part are the same statement.  The direction
this module needs is the one producing the vanishing, which is what
`NormalizedRecovery.ofLifting` asks for; the other direction is
`restrict_eq_quotientSlicePart_of_harmonicSlicePart_eq_zero`, already in
`Solution/QuotientRecoveryData.lean`.
-/

section GaugeReading

variable {Field ScalarField : Type*} [AddCommGroup Field] [Zero ScalarField]
  {calculus : CurlDivergenceCalculus Field ScalarField}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice] [CompleteSpace Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]
  {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}

/--
**A normalized state has no harmonic part on the window.**

`restrict u = u^⊥ + h` always, and `Normalized u` says `restrict u = u^⊥`; so
`h = 0`.  Both ingredients are theorems of `PDE/DivCurl.lean`
(`restrict_eq_quotientSlicePart_add_harmonicSlicePart` and
`normalized_iff_restrict_eq_quotientSlicePart`), and this is the form
`NormalizedRecovery.ofLifting` consumes.
-/
theorem LocalNormalization.harmonicSlicePart_eq_zero_of_normalized {field : Field}
    (normalized : normalization.Normalized field) :
    normalization.harmonicSlicePart field = 0 := by
  have split := normalization.restrict_eq_quotientSlicePart_add_harmonicSlicePart field
  rw [(normalization.normalized_iff_restrict_eq_quotientSlicePart field).1 normalized] at split
  simpa using split.symm

/-- The converse, so that the two readings of the gauge are visibly
interchangeable.  It is `restrict_eq_quotientSlicePart_of_harmonicSlicePart_eq_zero`
followed by `quotientSlicePart_mem_orthogonal`. -/
theorem LocalNormalization.normalized_of_harmonicSlicePart_eq_zero {field : Field}
    (harmonic_free : normalization.harmonicSlicePart field = 0) :
    normalization.Normalized field :=
  (normalization.normalized_iff_restrict_eq_quotientSlicePart field).2
    (restrict_eq_quotientSlicePart_of_harmonicSlicePart_eq_zero harmonic_free)

end GaugeReading

/-! ## The construction -/

section Construction

variable {Field ScalarField : Type*} [AddCommGroup Field] [Zero ScalarField]
  {calculus : CurlDivergenceCalculus Field ScalarField}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice] [CompleteSpace Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]

/--
**The forcing normalization of a source on a window.**

The data is a single scalar `ψ` — the amount by which the potential of a balance
is to be shifted — together with the statement that its gradient restricts to
the window's harmonic projection of the source.

Three things this is *not*:

* it is **not** a gauge condition on `forcing`: no property of `forcing` is
  assumed, and every source admits such a `ψ` as soon as the harmonic kernel of
  the window is represented by gradients
  (`ForcingNormalization.ofGradientRepresentation`);
* it is **not** an assumed splitting of `forcing`: the splitting
  `forcing = normalizedForcing + ∇ψ` is *defined* below, not supplied, and the
  properties that make it the right splitting are theorems;
* it carries **no** analytic content — no smoothness, no grade, no estimate, and
  no relation to any equation.

`lifts` is the exact analogue, on the source, of the `lifts` hypothesis that
`NormalizedRecovery.ofLifting` already takes on the velocity, and it is weaker
than the gauge it replaces: it says which object the projection *is*, not that
the projection vanishes.
-/
structure ForcingNormalization
    (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue)
    (forcing : Field) where
  /-- The potential shift `ψ`: the scalar the balance's potential is corrected
  by.  In the appendix this is the term the pressure absorbs. -/
  potentialShift : ScalarField
  /-- `∇ψ` restricts to the window's harmonic projection of the source.  This is
  the gradient representation of the projection, not a condition on the
  source. -/
  lifts : normalization.restrict (calculus.gradient potentialShift) =
    normalization.harmonicSlicePart forcing

namespace ForcingNormalization

variable {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}
  {forcing : Field} (shift : ForcingNormalization normalization forcing)

/-- **The absorbed part** `∇ψ` of the source: the summand that moves into the
potential.  It is a gradient, which is the whole reason it is invisible to the
field. -/
noncomputable def absorbedPart : Field := calculus.gradient shift.potentialShift

/-- **The normalized source** `f^⊥ = f - ∇ψ`.  This is the object that replaces
`forcing` everywhere below; `balance_normalizedForcing` says the replacement
costs only a shift of the potential. -/
noncomputable def normalizedForcing : Field := forcing - shift.absorbedPart

/-- The splitting `f = f^⊥ + ∇ψ`, by construction rather than by hypothesis. -/
theorem eq_normalizedForcing_add_absorbedPart :
    forcing = shift.normalizedForcing + shift.absorbedPart := by
  simp [normalizedForcing]

/-- The absorbed part restricts to the window's harmonic projection — this is
`lifts` read through the definition. -/
theorem restrict_absorbedPart :
    normalization.restrict shift.absorbedPart = normalization.harmonicSlicePart forcing :=
  shift.lifts

/-- The absorbed part carries no divergence on the window: the projection lands
in the harmonic kernel (`sliceDivergence_harmonicSlicePart`). -/
theorem sliceDivergence_restrict_absorbedPart :
    normalization.sliceDivergence (normalization.restrict shift.absorbedPart) = 0 := by
  rw [shift.restrict_absorbedPart, normalization.sliceDivergence_harmonicSlicePart]

/-- The absorbed part carries no rotational datum on the window, for the same
reason (`sliceCurl_harmonicSlicePart`).  Read together with the previous theorem:
the summand that is moved into the potential is invisible to *both* first-order
operators of the window, which is the precise sense in which it is not a real
obstruction. -/
theorem sliceCurl_restrict_absorbedPart :
    normalization.sliceCurl (normalization.restrict shift.absorbedPart) = 0 := by
  rw [shift.restrict_absorbedPart, normalization.sliceCurl_harmonicSlicePart]

section Restriction

variable (restrict_sub : ∀ first second : Field,
  normalization.restrict (first - second) =
    normalization.restrict first - normalization.restrict second)

include restrict_sub

/--
**The normalized source restricts to the constructed quotient part.**

The appendix's own computation `proj(f - h) = proj f - h = 0`, read through the
constructed decomposition `restrict f = u^⊥ + h`: subtracting the summand that
lifts the projection leaves exactly the projection's complement.

Subtractivity of the restriction is the only input beyond `lifts`; it is a
property of every `L²(window)` restriction, and it is carried explicitly for the
same reason `LocalNormalization` carries additivity explicitly.
-/
theorem restrict_normalizedForcing :
    normalization.restrict shift.normalizedForcing =
      normalization.quotientSlicePart forcing := by
  rw [normalizedForcing, restrict_sub, shift.restrict_absorbedPart,
    normalization.restrict_eq_quotientSlicePart_add_harmonicSlicePart forcing]
  abel

/-- **The normalized source is normalized** — the gauge, as an output.  It
restricts to the constructed quotient part, and that is orthogonal to the
harmonic kernel by `quotientSlicePart_mem_orthogonal`. -/
theorem normalized_normalizedForcing :
    normalization.Normalized shift.normalizedForcing := by
  show normalization.restrict shift.normalizedForcing ∈ _
  rw [shift.restrict_normalizedForcing restrict_sub]
  exact normalization.quotientSlicePart_mem_orthogonal forcing

/--
**The obligation, discharged.**

`harmonicSlicePart (f - ∇ψ) = 0` — the fourth hypothesis of
`NormalizedRecovery.ofLifting`, now a theorem about the construction rather than
an assumption about the source.  No property of `forcing` is used: whatever the
source was, the normalized source has no harmonic part on the window.
-/
theorem harmonicSlicePart_normalizedForcing :
    normalization.harmonicSlicePart shift.normalizedForcing = 0 :=
  LocalNormalization.harmonicSlicePart_eq_zero_of_normalized
    (shift.normalized_normalizedForcing restrict_sub)

/-- The normalized source is its own recovered representative — the second
identity of `NormalizedRecovery`, for the modified source.  This is
`QuotientRecoveryData.self_recovered` fed the gauge that was just proved. -/
theorem restrict_normalizedForcing_eq_recover (data : QuotientRecoveryData normalization) :
    normalization.restrict shift.normalizedForcing =
      data.recover shift.normalizedForcing :=
  data.self_recovered (shift.normalized_normalizedForcing restrict_sub)

/--
**The corollary: the recovery relation with no gauge condition anywhere.**

`NormalizedRecovery.ofLifting` with its fourth input supplied by the
construction.  What remains among the hypotheses is exactly what the velocity
side already cost — subtractivity of the restriction, a splitting of the state,
and a lifting of *its* harmonic component — plus the source's potential shift,
which is the construction's own data.  No `Normalized` condition, on the state
or on the source, appears as an input.
-/
theorem normalizedRecovery (data : QuotientRecoveryData normalization)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (lifts : normalization.restrict harmonicField = normalization.harmonicSlicePart field) :
    NormalizedRecovery data field quotientField shift.normalizedForcing :=
  NormalizedRecovery.ofLifting data restrict_sub decomposition lifts
    (shift.harmonicSlicePart_normalizedForcing restrict_sub)

/--
**The normalization is unique on the window.**

Two potential shifts for the same source produce normalized sources with the
same restriction — both are the constructed quotient part.  So the choice of
`ψ` is not a degree of freedom in anything the window can see; it is fixed
modulo the states the window does not distinguish.
-/
theorem restrict_normalizedForcing_congr (other : ForcingNormalization normalization forcing) :
    normalization.restrict shift.normalizedForcing =
      normalization.restrict other.normalizedForcing := by
  rw [shift.restrict_normalizedForcing restrict_sub,
    other.restrict_normalizedForcing restrict_sub]

end Restriction

/-! ### The source's rotational datum is untouched

The summand moved into the potential is a gradient, so it carries no curl at
all — not merely none on the window.  Neither `curl ∘ grad = 0` nor
subtractivity of the curl is a field of `CurlDivergenceCalculus`, and neither is
derivable from `curl_curl_eq`, so both are explicit named hypotheses, exactly as
the analogous linearity facts are elsewhere in the framework.  `curl ∘ grad = 0`
is a theorem for both concrete calculi
(`Distribution/CurlCalculus.curl_gradient`, `PDE/DivCurl.curl_gradient`), and
subtractivity of the curl follows from its additivity
(`Distribution/CurlCalculus.curl_add`).
-/

/--
**The normalized source carries the same rotational datum as the source.**

`curl (f - ∇ψ) = curl f`.  This is why replacing the source by its normalized
form leaves every vorticity argument — `Vorticity.vorticity_of_balance` and
everything downstream of it — verbatim unchanged.
-/
theorem curl_normalizedForcing
    (curl_sub : ∀ first second : Field,
      calculus.curl (first - second) = calculus.curl first - calculus.curl second)
    (curl_gradient : ∀ scalar : ScalarField, calculus.curl (calculus.gradient scalar) = 0) :
    calculus.curl shift.normalizedForcing = calculus.curl forcing := by
  rw [normalizedForcing, curl_sub, absorbedPart, curl_gradient, sub_zero]

end ForcingNormalization

/-! ## The construction exists, for every source at once

The one fact that is not algebra: the window's harmonic kernel is represented by
gradients.  It is the appendix's Poincaré argument on the geometry of a ball,
whose analytic core the framework proves in `PDE/DivCurlPotential.lean`
(`hasFDerivAt_radialPotential`).  It is taken here as an explicit named
parameter rather than restated, so that the two compose once the concrete
instance lands.
-/

/--
**Every source has a forcing normalization**, given the gradient representation
of the window's harmonic kernel.

The projection `harmonicSlicePart f` lies in the harmonic kernel by
`Submodule.starProjection_apply_mem`; `represents` turns it into a gradient, and
that gradient is the potential shift.  No property of `f` enters, so this is a
construction and not a case analysis.
-/
noncomputable def ForcingNormalization.ofGradientRepresentation
    {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}
    (represents : ∀ slice ∈ harmonicKernel normalization.sliceDivergence
        normalization.sliceCurl,
      ∃ scalar : ScalarField, normalization.restrict (calculus.gradient scalar) = slice)
    (forcing : Field) : ForcingNormalization normalization forcing where
  potentialShift :=
    (represents (normalization.harmonicSlicePart forcing)
      (Submodule.starProjection_apply_mem _ _)).choose
  lifts :=
    (represents (normalization.harmonicSlicePart forcing)
      (Submodule.starProjection_apply_mem _ _)).choose_spec

/--
**The obligation is discharged unconditionally, modulo the Poincaré fact.**

`harmonicSlicePart` of the constructed normalized source vanishes, for every
source, with the gradient representation as the sole non-algebraic input.
-/
theorem ForcingNormalization.harmonicSlicePart_ofGradientRepresentation
    {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}
    (represents : ∀ slice ∈ harmonicKernel normalization.sliceDivergence
        normalization.sliceCurl,
      ∃ scalar : ScalarField, normalization.restrict (calculus.gradient scalar) = slice)
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    (forcing : Field) :
    normalization.harmonicSlicePart
        (ForcingNormalization.ofGradientRepresentation represents forcing).normalizedForcing =
      0 :=
  (ForcingNormalization.ofGradientRepresentation represents
    forcing).harmonicSlicePart_normalizedForcing restrict_sub

/--
**The recovery relation, from a state lifting and the Poincaré fact alone.**

The end of the chain: `NormalizedRecovery` for a source that the framework
itself produced, with no gauge condition among the inputs — neither on the state
nor on the source.  The source it holds for is `f - ∇ψ`, and
`ForcingNormalization.balance_normalizedForcing` below is what says that this is
the same problem.
-/
theorem ForcingNormalization.normalizedRecovery_ofGradientRepresentation
    {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}
    (data : QuotientRecoveryData normalization)
    (represents : ∀ slice ∈ harmonicKernel normalization.sliceDivergence
        normalization.sliceCurl,
      ∃ scalar : ScalarField, normalization.restrict (calculus.gradient scalar) = slice)
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    {field quotientField harmonicField forcing : Field}
    (decomposition : field = quotientField + harmonicField)
    (lifts : normalization.restrict harmonicField = normalization.harmonicSlicePart field) :
    NormalizedRecovery data field quotientField
      (ForcingNormalization.ofGradientRepresentation represents forcing).normalizedForcing :=
  (ForcingNormalization.ofGradientRepresentation represents forcing).normalizedRecovery
    restrict_sub data decomposition lifts

end Construction

/-! ## The balance is the same balance

Everything above is about the window.  This section is the reason the
substitution `f ↦ f - ∇ψ` is legitimate at all: the modified source solves the
*same* equation, with the *same* first summand, and only the potential changes.

The statement is deliberately stated for an abstract `evolution : Field` rather
than for any particular operator.  A balance

> `heatOperator basis timeIndex (field index) + gradient frame potential index = source index`

is of this shape with `evolution` the heat term, and `pi_balance_iff` below is
the one-line bridge from that componentwise form to the `Field`-level equation.
Nothing about the heat operator, the time direction or the frame is used: the
potential shift commutes past the first summand because it never touches it.

Subtraction of scalars is needed to *name* the shifted potential `p - ψ`, which
`CurlDivergenceCalculus` does not provide (its scalar space carries only a
zero), so this section strengthens the scalar space to an additive group and
takes linearity of the gradient explicitly, exactly as the framework does
elsewhere.
-/

section Balance

variable {Field ScalarField : Type*} [AddCommGroup Field] [AddCommGroup ScalarField]
  {calculus : CurlDivergenceCalculus Field ScalarField}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice] [CompleteSpace Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]
  {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}
  {forcing : Field} (shift : ForcingNormalization normalization forcing)

/--
**The normalized source solves the same balance, with the potential shifted.**

`evolution + ∇p = f` becomes `evolution + ∇(p - ψ) = f - ∇ψ`.  The first
summand is unchanged — it is the *same* term, not a term proved equal to it — so
every conclusion the balance yields about the field is a conclusion about the
same field.  This is the appendix's pressure normalization, and it is pure group
algebra once the gradient is subtractive.
-/
theorem ForcingNormalization.balance_normalizedForcing
    (gradient_sub : ∀ first second : ScalarField,
      calculus.gradient (first - second) =
        calculus.gradient first - calculus.gradient second)
    {evolution : Field} {potential : ScalarField}
    (balance : evolution + calculus.gradient potential = forcing) :
    evolution + calculus.gradient (potential - shift.potentialShift) =
      shift.normalizedForcing := by
  have expand : shift.normalizedForcing =
      forcing - calculus.gradient shift.potentialShift := rfl
  have regroup : evolution +
        (calculus.gradient potential - calculus.gradient shift.potentialShift) =
      evolution + calculus.gradient potential - calculus.gradient shift.potentialShift := by
    abel
  rw [gradient_sub, regroup, balance, expand]

/-- The converse reading: a balance for the normalized source with the shifted
potential is a balance for the original source with the original potential.  So
no information is lost in the substitution — the two balances are
interchangeable, not merely one-way. -/
theorem ForcingNormalization.balance_of_balance_normalizedForcing
    (gradient_sub : ∀ first second : ScalarField,
      calculus.gradient (first - second) =
        calculus.gradient first - calculus.gradient second)
    {evolution : Field} {potential : ScalarField}
    (balance : evolution + calculus.gradient (potential - shift.potentialShift) =
      shift.normalizedForcing) :
    evolution + calculus.gradient potential = forcing := by
  have expand : shift.normalizedForcing =
      forcing - calculus.gradient shift.potentialShift := rfl
  rw [gradient_sub, expand] at balance
  have regroup : evolution +
        (calculus.gradient potential - calculus.gradient shift.potentialShift) =
      evolution + calculus.gradient potential - calculus.gradient shift.potentialShift := by
    abel
  rw [regroup] at balance
  exact sub_left_inj.1 balance

/--
**The normalized source is divergence-free whenever the source is and the
potential shift is harmonic.**

`div (f - ∇ψ) = div f - Δψ`.  The second summand is the harmonicity of the
potential shift, which is what makes `∇ψ` a member of the harmonic kernel rather
than merely a curl-free field — the same clause the velocity side records as
`divergence_gradient_potential`.
-/
theorem ForcingNormalization.divergence_normalizedForcing
    (divergence_sub : ∀ first second : Field,
      calculus.divergence (first - second) =
        calculus.divergence first - calculus.divergence second) :
    calculus.divergence shift.normalizedForcing =
      calculus.divergence forcing -
        calculus.divergence (calculus.gradient shift.potentialShift) := by
  have expand : shift.normalizedForcing =
      forcing - calculus.gradient shift.potentialShift := rfl
  rw [expand, divergence_sub]

/--
**The normalized state is divergence-free**, which is the form the div--curl
step consumes.

`divergence_normalizedForcing` states the subtraction; this states the
vanishing.  Both hypotheses are the ones the gauge already carries: the state
is divergence-free, and the potential shift is harmonic, i.e. its gradient has
no divergence.  Together they are clause (ii) of
`stokes:lem:harmonic-kernel-normalization`, read on whichever field the
normalization is instantiated at.
-/
theorem ForcingNormalization.divergence_normalizedForcing_eq_zero
    (divergence_sub : ∀ first second : Field,
      calculus.divergence (first - second) =
        calculus.divergence first - calculus.divergence second)
    (divergence_free : calculus.divergence forcing = 0)
    (harmonic :
      calculus.divergence (calculus.gradient shift.potentialShift) = 0) :
    calculus.divergence shift.normalizedForcing = 0 := by
  rw [shift.divergence_normalizedForcing divergence_sub, divergence_free,
    harmonic, sub_zero]

end Balance

/-! ### The componentwise reading -/

section Pointwise

variable {Index Value : Type*} [AddCommGroup Value]

/--
A componentwise balance is a balance of families.  This is the bridge between
the shape a concrete consumer writes,

> `∀ index, evolution index + gradient potential index = source index`,

and the `Field`-level equation the theorems above are stated for, with
`Field := Index → Value`.  It is `funext` in one direction and evaluation in the
other, and it is here only so that no consumer has to rewrite the same two
lines.
-/
theorem pi_balance_iff (evolution potentialGradient source : Index → Value) :
    (∀ index, evolution index + potentialGradient index = source index) ↔
      evolution + potentialGradient = source := by
  constructor
  · intro pointwise
    funext index
    simpa using pointwise index
  · intro equation index
    simpa using congrFun equation index

end Pointwise

end Hypostructure.PDE.DivCurl
