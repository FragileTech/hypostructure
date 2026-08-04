import Hypostructure.PDE.DivCurl

/-!
# The recovery datum of the div–curl step, owned by the framework

A local regularity argument that recovers a field from its rotational datum
consumes a *recovery operator* `T` together with two identities,

> `u^⊥ = T u`   and   `f = T f`,

the first saying that the quotient representative of the state is what `T`
returns, the second that a solenoidal source is already its own representative.
An application that carries `T` as data has to supply both identities as
hypotheses, and then nothing in the statement records that `T` is *the* div–curl
recovery rather than an arbitrary operator.

Nothing about either identity is problem-specific.  `PDE/DivCurl.lean` already
constructs the recovery — it is `harmonicComplement`, read on the window's own
`L²` through a `LocalNormalization` — and proves the three properties that
characterize it:

* `LocalNormalization.quotientSlicePart_mem_orthogonal` — the value is normalized,
  i.e. orthogonal to the harmonic kernel of the window;
* `LocalNormalization.sliceDivergence_quotientSlicePart` — the value carries the
  divergence of the state;
* `LocalNormalization.sliceCurl_quotientSlicePart` — the value carries the
  rotational datum of the state.

This module packages exactly those three as a structure, `QuotientRecoveryData`,
so that the recovery operator can be taken as a black box of that shape, and
then supplies:

* `QuotientRecoveryData.ofLocalNormalization` — the constructor.  It takes **no
  hypotheses beyond completeness of the window's `L²`**, because the operator it
  installs is `LocalNormalization.quotientSlicePart` and the three fields are
  the three theorems above verbatim;
* `QuotientRecoveryData.recover_eq_quotientSlicePart` — every datum of this
  shape *is* that constructor, by the uniqueness theorem
  `eq_harmonicComplement_of_orthogonal`.  So the structure is a singleton: there
  is nothing to choose;
* `QuotientRecoveryData.recovers`, `QuotientRecoveryData.recovers_of_normalized`
  and `QuotientRecoveryData.self_recovered` — the two identities above, as
  **theorems** rather than fields a caller fills.

## Running the normalization

Both identities are then bundled into `NormalizedRecovery`, whose single public
constructor `NormalizedRecovery.ofLifting` takes **no gauge condition**: no
`Normalized` hypothesis appears among its inputs.  It runs the normalization
instead, from the statement that the discarded component of the splitting is the
projection on the window (`lifts`), and the two gauge facts come back out as
`NormalizedRecovery.quotient_normalized` and
`NormalizedRecovery.forcing_normalized`.

That some such input is unavoidable is proved, not asserted:
`QuotientRecoveryData.restrict_eq_zero_of_normalizationDerivation` shows that
deriving the gauge from the algebraic decomposition alone would collapse the
window's harmonic kernel, and
`QuotientRecoveryData.not_self_recovered_of_harmonic` shows the recovery
identity is genuinely false for the modes the gauge excludes.

## What is deliberately not here

The recovery operator of an application is usually realized concretely — as a
matrix of Fourier multipliers, say, which is what
`PDE/Distribution/Multiplier.lean` carries and which is where the commutation
of `T` with `∂_v` and with the heat operator is proved.  That realization acts
on the state space, whereas everything below lives on the window's `L²`; the
bridge between the two would need a right inverse of `LocalNormalization.restrict`,
and `PDE/DivCurl.lean` explains at length why there is none.  The two modules are
therefore complementary and independent: this one says *which* operator the
recovery is, that one says what a concrete realization commutes with.

Nothing here mentions a dimension, a domain, or an equation: the whole module is
parametric in the state space, the window's `L²` and the two operator targets,
exactly as `LocalNormalization` is.
-/

namespace Hypostructure.PDE.DivCurl

variable {Field ScalarField : Type*} [AddCommGroup Field] [Zero ScalarField]
  {calculus : CurlDivergenceCalculus Field ScalarField}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]

/--
**The recovery datum of the div–curl step.**

An operator from states to the window's `L²`, together with the three properties
that make it *the* recovery of `stokes`-style div–curl statements: its values are
normalized, and it changes neither the divergence nor the rotational datum read
on the window.

There is no analytic field — no continuity, no estimate, no relation to
smoothness.  The three properties are exactly what the uniqueness theorem
`eq_of_orthogonal_of_curl_eq` consumes, and they are enough to pin the operator
down completely (`recover_eq_quotientSlicePart`) and to prove the two recovery
identities an application would otherwise assume.

Completeness of the window's `L²` is *not* required to state the structure; it is
required only to build one, since the construction is an orthogonal projection.
-/
structure QuotientRecoveryData
    (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue) where
  /-- The recovery operator: a state goes to the representative of its rotational
  datum modulo the harmonic kernel of the window. -/
  recover : Field → Slice
  /-- The recovered representative is normalized — orthogonal to the harmonic
  kernel.  This is the clause without which the rotational datum would not
  determine the field. -/
  recover_mem_orthogonal : ∀ state : Field, recover state ∈
    (harmonicKernel normalization.sliceDivergence normalization.sliceCurl)ᗮ
  /-- Recovering does not change the divergence read on the window. -/
  sliceDivergence_recover : ∀ state : Field,
    normalization.sliceDivergence (recover state) =
      normalization.sliceDivergence (normalization.restrict state)
  /-- Recovering does not change the rotational datum read on the window.  This
  is the identity the whole recovery rests on. -/
  sliceCurl_recover : ∀ state : Field,
    normalization.sliceCurl (recover state) =
      normalization.sliceCurl (normalization.restrict state)

namespace QuotientRecoveryData

variable {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}

section Uniqueness

variable (data : QuotientRecoveryData normalization)

/--
**The rotational datum determines the recovered representative.**

Two states with the same divergence and the same rotational datum on the window
are recovered to the same representative.  This is
`eq_of_orthogonal_of_curl_eq` applied to the two recovered values: both are
normalized, and the two hypotheses transport through the operator by the fields
of the structure.

It is the precise sense in which the operator depends on the rotational datum
alone, and it needs no completeness.
-/
theorem recover_congr {first second : Field}
    (same_divergence : normalization.sliceDivergence (normalization.restrict first) =
      normalization.sliceDivergence (normalization.restrict second))
    (same_curl : normalization.sliceCurl (normalization.restrict first) =
      normalization.sliceCurl (normalization.restrict second)) :
    data.recover first = data.recover second :=
  eq_of_orthogonal_of_curl_eq (data.recover_mem_orthogonal first)
    (data.recover_mem_orthogonal second)
    (by rw [data.sliceDivergence_recover, data.sliceDivergence_recover, same_divergence])
    (by rw [data.sliceCurl_recover, data.sliceCurl_recover, same_curl])

variable [CompleteSpace Slice]

/--
**There is only one recovery datum**: any operator of this shape is the
constructed one, `LocalNormalization.quotientSlicePart`.

This is `eq_harmonicComplement_of_orthogonal` — existence is the orthogonal
projection, uniqueness is the theorem above — and it is what turns the recovery
operator from an assumption into a description.  In particular an application
gains nothing by carrying its own operator: whatever it carries is this one.
-/
theorem recover_eq_quotientSlicePart (state : Field) :
    data.recover state = normalization.quotientSlicePart state :=
  eq_harmonicComplement_of_orthogonal (data.recover_mem_orthogonal state)
    (data.sliceDivergence_recover state) (data.sliceCurl_recover state)

end Uniqueness

section Construction

variable [CompleteSpace Slice]

/--
**The recovery datum exists**, and it takes no hypotheses.

The operator is `LocalNormalization.quotientSlicePart`, the orthogonal
complement of the window's harmonic kernel, and the three fields are the three
theorems `PDE/DivCurl.lean` already proves about it.  Completeness of the
window's `L²` is the only ambient requirement, and it is what the Hilbert
projection theorem needs.

Together with `recover_eq_quotientSlicePart` this says that the recovery datum
is not data at all.
-/
noncomputable def ofLocalNormalization
    (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue) :
    QuotientRecoveryData normalization where
  recover := normalization.quotientSlicePart
  recover_mem_orthogonal := normalization.quotientSlicePart_mem_orthogonal
  sliceDivergence_recover := normalization.sliceDivergence_quotientSlicePart
  sliceCurl_recover := normalization.sliceCurl_quotientSlicePart

@[simp] theorem recover_ofLocalNormalization
    (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue)
    (state : Field) :
    (ofLocalNormalization normalization).recover state =
      normalization.quotientSlicePart state := rfl

end Construction

section Identities

variable [CompleteSpace Slice] (data : QuotientRecoveryData normalization)

/--
**`u^⊥ = T u` is a theorem**, from an assumed algebraic decomposition.

This is the obligation an application carries as the hypothesis "the quotient
velocity is what the recovery operator returns".  Its proof is
`LocalNormalization.restrict_eq_quotientSlicePart_of_decomposition` — the
assumed decomposition `u = u^⊥ + h` with `h` curl-free, `u` and `u^⊥`
divergence-free and `u^⊥` normalized restricts to the constructed quotient part
— composed with the uniqueness of the operator.

Additivity of the restriction is the one property `LocalNormalization` does not
carry, so it is an explicit argument here exactly as it is there.
-/
theorem recovers
    (restrict_add : ∀ first second : Field,
      normalization.restrict (first + second) =
        normalization.restrict first + normalization.restrict second)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (harmonic_curl_free : calculus.curl harmonicField = 0)
    (divergence_free : calculus.divergence field = 0)
    (quotient_divergence_free : calculus.divergence quotientField = 0)
    (normalized : normalization.Normalized quotientField) :
    normalization.restrict quotientField = data.recover field := by
  rw [data.recover_eq_quotientSlicePart]
  exact normalization.restrict_eq_quotientSlicePart_of_decomposition restrict_add
    decomposition harmonic_curl_free divergence_free quotient_divergence_free normalized

/--
**`u^⊥ = T u` again, with the decomposition replaced by the two identities it is
used for**: the candidate is normalized and carries the same divergence and the
same rotational datum on the window.

This is `LocalNormalization.restrict_eq_quotientSlicePart_of_normalized`, and it
is the form to use when the ambient argument already knows
`curl u^⊥ = curl u` rather than a splitting of `u`.
-/
theorem recovers_of_normalized {field quotientField : Field}
    (normalized : normalization.Normalized quotientField)
    (same_divergence : normalization.sliceDivergence (normalization.restrict quotientField) =
      normalization.sliceDivergence (normalization.restrict field))
    (same_curl : normalization.sliceCurl (normalization.restrict quotientField) =
      normalization.sliceCurl (normalization.restrict field)) :
    normalization.restrict quotientField = data.recover field := by
  rw [data.recover_eq_quotientSlicePart]
  exact normalization.restrict_eq_quotientSlicePart_of_normalized normalized same_divergence
    same_curl

/--
**`f = T f` is a theorem**, the second obligation: a normalized state is already
its own recovered representative.

This is the forward direction of
`LocalNormalization.normalized_iff_restrict_eq_quotientSlicePart`, i.e. the
idempotence of the normalization.  Normalization of the source is the whole
content: a source with a curl-free component is *not* its own representative,
and that component is what a pressure normalization absorbs.
-/
theorem self_recovered {field : Field} (normalized : normalization.Normalized field) :
    normalization.restrict field = data.recover field := by
  rw [data.recover_eq_quotientSlicePart]
  exact (normalization.normalized_iff_restrict_eq_quotientSlicePart field).1 normalized

/--
The converse of `self_recovered`: being one's own recovered representative *is*
the normalization condition.  So the second obligation is not an extra
assumption about the source, it is a restatement of the third clause of the
div–curl characterization.
-/
theorem normalized_iff_self_recovered {field : Field} :
    normalization.Normalized field ↔ normalization.restrict field = data.recover field := by
  rw [data.recover_eq_quotientSlicePart]
  exact normalization.normalized_iff_restrict_eq_quotientSlicePart field

omit [CompleteSpace Slice] in
/--
**The recovered representative is normalized, whatever it was recovered from.**

Read together with `normalized_iff_self_recovered` this closes the circle: the
values of the recovery operator are exactly the states that the operator fixes.
-/
theorem recover_mem_orthogonal_of_recovers {field quotientField : Field}
    (recovers : normalization.restrict quotientField = data.recover field) :
    normalization.Normalized quotientField := by
  show normalization.restrict quotientField ∈ _
  rw [recovers]
  exact data.recover_mem_orthogonal field

/--
**The parasitic mode does not satisfy the recovery identity.**

A state that is divergence-free *and* curl-free, and nonzero on the window, lies
in the harmonic kernel: the recovery operator sends its rotational datum to
nothing, while the state itself does not vanish.  So `u = T u` fails for it
outright, and it is not a legal representative in the first place —
`LocalNormalization.not_normalized_of_restrict_ne_zero`.

This is the second half of the exclusion of the apparent counterexample to the
recovery statement, and it is why the normalization hypothesis carried by
`NormalizedRecovery` below is a gauge choice rather than an extra assumption:
the modes it rules out are exactly the ones for which the identity is false.
-/
theorem not_self_recovered_of_harmonic {field : Field}
    (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0)
    (nonzero : normalization.restrict field ≠ 0) :
    ¬ normalization.restrict field = data.recover field := fun identity =>
  normalization.not_normalized_of_restrict_ne_zero divergence_free curl_free nonzero
    (data.normalized_iff_self_recovered.2 identity)

omit [CompleteSpace Slice] in
/--
**The gauge is not derivable from the algebraic decomposition data.**

Suppose one had a rule producing `Normalized u^⊥` from a splitting
`u = u^⊥ + h` with `h` carrying no rotational datum and `u`, `u^⊥`
divergence-free — that is, from exactly the data an application carries.  Apply
it with `h = 0`, so that `u^⊥ = u`: every divergence-free curl-free state is
then normalized, hence restricts to `0` by
`LocalNormalization.restrict_eq_zero_of_normalized`.

So such a rule exists only when the realization sees no harmonic modes at all.
This is why `NormalizedRecovery.ofLifting` asks for the lifting instead: the
gauge has to come from somewhere, and the decomposition is not that somewhere.
-/
theorem restrict_eq_zero_of_normalizationDerivation
    (derivation : ∀ {state quotientState harmonicState : Field},
      state = quotientState + harmonicState →
      calculus.curl harmonicState = 0 →
      calculus.divergence state = 0 →
      calculus.divergence quotientState = 0 →
      normalization.Normalized quotientState)
    {field : Field}
    (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0) :
    normalization.restrict field = 0 :=
  normalization.restrict_eq_zero_of_normalized
    (derivation (add_zero field).symm calculus.curl_zero divergence_free divergence_free)
    divergence_free curl_free

/--
The same obstruction for the source's identity: a recovery operator that fixed
*every* state would collapse the harmonic kernel of the window.  So
`f = T f` is a genuine condition on `f`, not a property of `T`.
-/
theorem restrict_eq_zero_of_selfRecoveryDerivation
    (derivation : ∀ state : Field, normalization.restrict state = data.recover state)
    {field : Field}
    (divergence_free : calculus.divergence field = 0)
    (curl_free : calculus.curl field = 0) :
    normalization.restrict field = 0 :=
  normalization.restrict_eq_zero_of_normalized
    (data.normalized_iff_self_recovered.2 (derivation field)) divergence_free curl_free

end Identities

end QuotientRecoveryData

/-! ## The realization, built rather than assumed

A consumer of the div–curl step does not want the recovery operator and the two
identities separately: it wants a single object saying "this state, this
representative and this source stand in the recovery relation".  That object is
`NormalizedRecovery` below, and it is *constructed* from a `LocalNormalization` —
its operator is `QuotientRecoveryData.ofLocalNormalization`, which by
`QuotientRecoveryData.recover_eq_quotientSlicePart` is the only operator there
is.

### Where the normalization comes from

The naive input would be the gauge itself: "the representative is normalized".
That is not taken here, because it can be *derived* from something more
primitive — the statement that the discarded component **is** the projection on
the window,

> `restrict h = harmonicSlicePart u`,

called `lifts` below.  Given it, `restrict u^⊥ = restrict u - restrict h =
quotientSlicePart u`, which is simultaneously the recovery identity and, by
`quotientSlicePart_mem_orthogonal`, the normalization.  So the gauge is an
**output** of `NormalizedRecovery.ofLifting`, not an input:
`NormalizedRecovery.quotient_normalized` reads it back off the relation.

`lifts` is genuinely weaker than assuming the answer — it says nothing about
orthogonality, only that the splitting one holds is the projection's — and it is
the same hypothesis the appendix's own normalization lemma carries, for the same
reason: exhibiting the projection as an explicit potential is a Poincaré
argument on the geometry of the window, and `PDE/DivCurl.lean` builds the
projection without ever representing its elements.

### Why the gauge cannot be dropped entirely

It cannot be derived from the algebraic decomposition data alone, and the file
proves this rather than asserting it.
`QuotientRecoveryData.restrict_eq_zero_of_normalizationDerivation` shows that any
rule deriving `Normalized u^⊥` from `u = u^⊥ + h`, `curl h = 0` and the two
divergence hypotheses would force **every** divergence-free curl-free state to
restrict to `0` — take `h = 0`, so that `u^⊥ = u` — i.e. would collapse the
window's harmonic kernel.  That is the parasitic mode of the div–curl
literature, and `QuotientRecoveryData.not_self_recovered_of_harmonic` records
that the recovery identity is genuinely *false* for it.  So some replacement for
the gauge is unavoidable; `lifts` is the honest one.
-/

section Realization

variable [CompleteSpace Slice]
  {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}

/-! ### The normalization, run rather than assumed -/

section Lifting

/--
**Running the normalization.**

If the discarded component of a splitting restricts to the projection on the
window, then the remaining component restricts to the constructed quotient part.
The computation is the appendix's `proj(u - h) = proj u - h = 0`, read through
`LocalNormalization.restrict_eq_quotientSlicePart_add_harmonicSlicePart`.

No divergence hypothesis, no curl hypothesis and no orthogonality hypothesis
enters: subtractivity of the restriction and the lifting are the whole input.
-/
theorem restrict_eq_quotientSlicePart_of_lifting
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (lifts : normalization.restrict harmonicField =
      normalization.harmonicSlicePart field) :
    normalization.restrict quotientField = normalization.quotientSlicePart field := by
  have split : quotientField = field - harmonicField := by
    rw [decomposition]; abel
  rw [split, restrict_sub, lifts,
    normalization.restrict_eq_quotientSlicePart_add_harmonicSlicePart field]
  abel

/--
**The gauge is an output.**  The remaining component of a lifted splitting is
normalized, because it restricts to the constructed quotient part and that is
orthogonal to the harmonic kernel by `quotientSlicePart_mem_orthogonal`.

This is the framework-side form of the appendix's clause
"`proj_𝓗 u^⊥ = 0`", and it is what makes it unnecessary to carry the gauge as a
hypothesis anywhere below.
-/
theorem normalized_of_lifting
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    {field quotientField harmonicField : Field}
    (decomposition : field = quotientField + harmonicField)
    (lifts : normalization.restrict harmonicField =
      normalization.harmonicSlicePart field) :
    normalization.Normalized quotientField := by
  show normalization.restrict quotientField ∈ _
  rw [restrict_eq_quotientSlicePart_of_lifting restrict_sub decomposition lifts]
  exact normalization.quotientSlicePart_mem_orthogonal field

/--
**A state with no harmonic component on the window is its own representative.**

The splitting `restrict f = quotientSlicePart f + harmonicSlicePart f` with the
second summand gone.  This is the appendix's statement that the source enters
the recovery through its solenoidal part alone, its curl-free part having been
absorbed elsewhere; here it is the vanishing of the projection, which is what
"absorbed" means on the window.
-/
theorem restrict_eq_quotientSlicePart_of_harmonicSlicePart_eq_zero {field : Field}
    (harmonic_free : normalization.harmonicSlicePart field = 0) :
    normalization.restrict field = normalization.quotientSlicePart field := by
  rw [normalization.restrict_eq_quotientSlicePart_add_harmonicSlicePart field, harmonic_free,
    add_zero]

end Lifting

/--
**The recovery relation of the div–curl step.**

The two identities an application would otherwise carry as hypotheses of its
regularity theorem: the representative is what the recovery returns from the
state, and the source is its own recovered representative.

The constructor below discharges both fields, and takes no gauge condition.
-/
structure NormalizedRecovery (data : QuotientRecoveryData normalization)
    (field quotientField forcing : Field) : Prop where
  /-- `u^⊥ = T u`. -/
  recovers : normalization.restrict quotientField = data.recover field
  /-- `f = T f`. -/
  forcing_recovered : normalization.restrict forcing = data.recover forcing

namespace NormalizedRecovery

variable (data : QuotientRecoveryData normalization)

/--
**The recovery relation, with the normalization run rather than assumed.**

Neither field of the result is a hypothesis and neither `Normalized` condition
appears among the inputs.  What is asked is:

* subtractivity of the restriction — a property of the realization, true of every
  `L²(window)` restriction, carried explicitly for the same reason
  `LocalNormalization` carries additivity explicitly;
* a splitting of the state whose discarded component restricts to the
  projection;
* vanishing of the source's projection on the window.

The gauge conditions come back out as `quotient_normalized` and
`forcing_normalized`.
-/
theorem ofLifting
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    {field quotientField harmonicField forcing : Field}
    (decomposition : field = quotientField + harmonicField)
    (lifts : normalization.restrict harmonicField =
      normalization.harmonicSlicePart field)
    (forcing_harmonic_free : normalization.harmonicSlicePart forcing = 0) :
    NormalizedRecovery data field quotientField forcing where
  recovers := by
    rw [data.recover_eq_quotientSlicePart]
    exact restrict_eq_quotientSlicePart_of_lifting restrict_sub decomposition lifts
  forcing_recovered := by
    rw [data.recover_eq_quotientSlicePart]
    exact restrict_eq_quotientSlicePart_of_harmonicSlicePart_eq_zero forcing_harmonic_free

variable {data}

/-- The relation determines the representative: it is the constructed quotient
part of the state, by `QuotientRecoveryData.recover_eq_quotientSlicePart`. -/
theorem restrict_eq_quotientSlicePart {field quotientField forcing : Field}
    (recovery : NormalizedRecovery data field quotientField forcing) :
    normalization.restrict quotientField = normalization.quotientSlicePart field := by
  rw [recovery.recovers, data.recover_eq_quotientSlicePart]

omit [CompleteSpace Slice] in
/-- **The gauge, read back off the relation.**  It was never an input; it is a
consequence, which is the sense in which the normalization has been run. -/
theorem quotient_normalized {field quotientField forcing : Field}
    (recovery : NormalizedRecovery data field quotientField forcing) :
    normalization.Normalized quotientField :=
  data.recover_mem_orthogonal_of_recovers recovery.recovers

/-- The same for the source. -/
theorem forcing_normalized {field quotientField forcing : Field}
    (recovery : NormalizedRecovery data field quotientField forcing) :
    normalization.Normalized forcing :=
  data.normalized_iff_self_recovered.2 recovery.forcing_recovered

end NormalizedRecovery

end Realization

end Hypostructure.PDE.DivCurl
