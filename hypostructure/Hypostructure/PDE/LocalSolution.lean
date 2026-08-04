import Hypostructure.PDE.Object
import Hypostructure.PDE.NoSingularityTarget
import Hypostructure.PDE.Distribution.SmoothRepresentative

/-!
# The balance, as the registered baseline

The mirror of `Graph.MinimumDegreeAtLeast`.  A graph problem's baseline is a
*proposition the framework states* --- `k ≤ object.minDegree` --- so it arrives
at every strategy as `input.baseline` and no application ever proves it on
demand.  `Graph/Strategy/MinimumDegreeBaseline.lean:36` is the whole idea:

```lean
theorem minimumDegreeAtLeast_of_problemInput (input) : k ≤ input.object.minDegree :=
  input.baseline
```

`IsLocalSolution` is that proposition for a local regularity problem: the
object's two functions represent its two distributions, the source is smooth,
and the momentum identity `∂_t u − Δ_x u + ∇p = f` holds.  Registering a problem
through `problemWithBalance` pins it, so from then on the balance is
`input.baseline` --- a projection, never an obligation.

Nothing here is an estimate and nothing is global: the momentum identity is
tested against one test function of the object's own domain, in one coordinate.
-/

namespace Hypostructure.PDE

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

universe v w x

/--
**The linear parabolic momentum law**, `∂_t u − Δ_x u + ∇p = f`, read in one
coordinate against one test function of the object's own domain.

This is *the problem's* equation, not the framework's.  `IsLocalSolution`
takes the momentum law as a parameter, so a problem whose equation carries, say,
a transport term registers a different `Momentum` and reuses every other clause,
every strategy family and the whole singularity machinery unchanged.  The
framework never assumes the equation is this one.
-/
def LinearParabolicMomentum (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : Place dimension)
    (spatialDirection : Index → Place dimension)
    (object : FieldObject dimension Value) : Prop :=
  ∀ (test : 𝓓(object.domain, ℝ)) (coordinate : Index),
    reader coordinate
        ((Distribution.lineDerivCLM timeDirection :
          𝓓'(object.domain, Value) →L[ℝ] 𝓓'(object.domain, Value))
            object.fieldState test) -
        reader coordinate
          ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(object.domain, Value) →L[ℝ] 𝓓'(object.domain, Value))
                ((Distribution.lineDerivCLM (spatialDirection axis) :
                  𝓓'(object.domain, Value) →L[ℝ] 𝓓'(object.domain, Value))
                    object.fieldState)) test) +
        (Distribution.lineDerivCLM (spatialDirection coordinate) :
          𝓓'(object.domain, ℝ) →L[ℝ] 𝓓'(object.domain, ℝ))
          object.potential test =
      reader coordinate (object.sourceState test)

/--
**The framework's normalization**, the weak form of `proj_{𝓗(B_ρ)} u = 0`.

On every ball compactly contained in the domain, the field is orthogonal to
every spatially curl-free divergence-free smooth mode --- the parasitic mode of
`stokes:rem:parasitic-counterexample`, which is exactly what
`stokes:lem:harmonic-kernel-normalization` removes.

**Compact support is deliberately not required, and the pairing is over the ball
rather than over everything.**  An earlier version asked for orthogonality to
smooth *compactly supported* curl-free divergence-free modes, and that version
is **vacuous**: curl-freeness gives `∂_i m_j = ∂_j m_i`, so
`Δ_x m_j = ∂_j (div m) = 0` and every component of such a mode is harmonic in
the spatial variables; a compactly supported harmonic function is zero.  The
condition then quantified over nothing but `0` and excluded no field at all ---
in particular it did not exclude `u = a(t) ∇ψ(x)` with `ψ` spatially harmonic
and `a` merely `L²`, which solves the balance with `f = 0` and `p = −a'(t)ψ`,
is divergence-free, and has no smooth representative.  With the ball-local form
below that field is excluded: `m = b(t) ∇ψ(x)` is an admissible mode for every
smooth `b`, and the pairing forces `a = 0` almost everywhere.

`𝓗(B)` is a *closed subspace of `L²(B)`*, not a space of compactly supported
fields, which is why the ball is the right domain of integration and why the
appendix states the normalization slice by slice.

**This is not a parameter, and no application may choose it.**  A problem that
could pick its own normalization could pick one that implies its own conclusion;
`problemWithBalance` therefore pins this one from the coordinate data and offers
no alternative.

It says nothing whatsoever about regularity: it constrains *which mode* the field
carries, and every clause of it is a statement about integrals of `object.field`
against fixed smooth fields.  The orthogonality pairing is written in the
problem's own coordinates through `reader`, so no inner-product instance is
needed and no new geometry is introduced.
-/
def HarmonicKernelNormalized (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → Place dimension)
    (object : FieldObject dimension Value) : Prop :=
  ∀ (centre : Place dimension) (radius : ℝ),
    Metric.closedBall centre radius ⊆ (object.domain : Set (Place dimension)) →
    ∀ mode : Place dimension → Value,
      ContDiff ℝ ∞ mode →
      -- The mode is divergence-free.
      (∀ place : Place dimension,
        ∑ axis : Index,
          reader axis (lineDeriv ℝ mode place (spatialDirection axis)) = 0) →
      -- …and curl-free: its matrix of directional derivatives is symmetric.
      (∀ (first second : Index) (place : Place dimension),
        reader second (lineDeriv ℝ mode place (spatialDirection first)) =
          reader first (lineDeriv ℝ mode place (spatialDirection second))) →
      ∫ place in Metric.ball centre radius, (∑ axis : Index,
        reader axis (object.field place) * reader axis (mode place)) ∂μ = 0

/--
**`object` is a local distributional solution.**

Not an assumption about regularity --- a definition of what solving means.
`fieldRepresents` asks only that `object.field` be *some* locally integrable
representative of `object.fieldState`, which is why it does not, and cannot,
imply that `object.field` is smooth: a representative may be arbitrary on a null
set.  `sourceSmooth` is the problem's data hypothesis (`f ∈ C^∞`), `momentum` is
its equation, and `gauge` its normalization.  None of the five says the
conclusion.

A `Prop`, exactly as `Graph.MinimumDegreeAtLeast k object` is a `Prop`: it says
something about the object and carries no data of its own.  Every field is a
statement about the object's *own* pieces, so an application that registers
through `problemWithBalance` receives all five as projections of
`input.baseline`.

Three clauses are the framework's and say only that the object's functions
present its distributions.  The remaining two are the problem's: `Momentum` is
its equation and `Gauge` its normalization.  Neither is fixed here, so this
structure is not about any particular PDE.
-/
structure IsLocalSolution (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure (Place dimension))
    (Momentum : FieldObject dimension Value → Prop)
    (Gauge : FieldObject dimension Value → Prop)
    (object : FieldObject dimension Value) : Prop where
  /-- The object's field function represents its field distribution. -/
  fieldRepresents : ∀ test : 𝓓(object.domain, ℝ),
    object.fieldState test = ∫ place, test place • object.field place ∂μ
  /-- The field is measurable. -/
  fieldMeasurable : AEStronglyMeasurable object.field μ
  /-- **`u ∈ L²_loc`**, the appendix's standing hypothesis on the field
  (`stokes:thm:global-normalized-representative`: `u ∈ L²_loc(𝒰)`).

  It is here because the framework's own placement constructor
  `Localization.SquareIntegrablePlacement.ofRepresentative` needs exactly this
  to carry a locally represented reading into the graded tempered model, which
  is the only route from the distributional balance to a classical smooth
  representative.  It says nothing about regularity --- square integrability is
  not smoothness --- and, being pinned here, is never an application's
  obligation. -/
  fieldLocallySquareIntegrable : ∀ (centre : Place dimension) (radius : ℝ),
    Metric.ball centre radius ⊆ (object.domain : Set (Place dimension)) →
      MemLp object.field 2 (μ.restrict (Metric.ball centre radius))
  /-- The same for the source. -/
  sourceRepresents : ∀ test : 𝓓(object.domain, ℝ),
    object.sourceState test = ∫ place, test place • object.source place ∂μ
  /-- The source is smooth on the domain.  This is part of what the problem
  *is*, exactly as a minimum-degree bound is part of what a graph problem is. -/
  sourceSmooth : ContDiffOn ℝ ∞ object.source (object.domain : Set (Place dimension))
  /-- **The problem's equation**, whatever it is. -/
  momentum : Momentum object
  /-- **The problem's normalization**, whatever it is. -/
  gauge : Gauge object

/--
**The baseline cannot see a null set.**

Every clause of `IsLocalSolution` that mentions `object.field` is an integral,
an `AEStronglyMeasurable` or a `MemLp`, and the pinned momentum law mentions it
not at all --- it is a statement about `object.fieldState`.  So changing the
field on a set of measure zero carries a local solution to a local solution.

This is exactly why the registered target asks for a *representative*:
`ContDiffOn ℝ ∞ object.field` is **not** invariant under the same change, so a
baseline of this shape cannot imply it, and asking for it would be asking for
something refutable.  The theorem below is that fact, compiled.
-/
theorem isLocalSolution_congr_ae (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : Place dimension)
    (spatialDirection : Index → Place dimension)
    {object : FieldObject dimension Value}
    {replacement : Place dimension → Value}
    (agrees : object.field =ᵐ[μ] replacement)
    (measurable : AEStronglyMeasurable replacement μ)
    (solution : IsLocalSolution dimension Value μ
      (LinearParabolicMomentum dimension Value Index reader timeDirection
        spatialDirection)
      (HarmonicKernelNormalized dimension Value Index μ reader spatialDirection)
      object) :
    IsLocalSolution dimension Value μ
      (LinearParabolicMomentum dimension Value Index reader timeDirection
        spatialDirection)
      (HarmonicKernelNormalized dimension Value Index μ reader spatialDirection)
      { object with field := replacement } where
  fieldRepresents := fun test => by
    rw [solution.fieldRepresents test]
    exact integral_congr_ae
      (agrees.mono fun place same => congrArg (fun value => test place • value) same)
  fieldMeasurable := measurable
  fieldLocallySquareIntegrable := fun centre radius inside =>
    (solution.fieldLocallySquareIntegrable centre radius inside).ae_eq
      (ae_restrict_of_ae agrees)
  sourceRepresents := solution.sourceRepresents
  sourceSmooth := solution.sourceSmooth
  momentum := solution.momentum
  gauge := fun centre radius inside mode smooth divergenceFree curlFree => by
    rw [← solution.gauge centre radius inside mode smooth divergenceFree curlFree]
    exact integral_congr_ae
      (ae_restrict_of_ae (agrees.mono fun place same =>
        congrArg (fun value => ∑ axis : Index,
          reader axis value * reader axis (mode place)) same.symm))

/--
**Register a local regularity problem whose baseline is the balance.**

The framework chooses what `Baseline` says, so `Core.Strategy.ProblemInput`'s
`baseline` field *is* the balance.  Mirrors the way
`Graph.minimumDegreeCycleTarget` and `SealedDag.minimumDegreeCycleDefinition`
are both typed against
`Graph.problemWithPresentation (Graph.MinimumDegreeAtLeast k) …`.
-/
def problemWithBalance (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → Place dimension)
    (Momentum : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) :
    Core.Problem.{w, v} :=
  problemWithPresentation dimension Value
    (IsLocalSolution dimension Value μ Momentum
      (HarmonicKernelNormalized dimension Value Index μ reader spatialDirection))
    BranchState Presentation presentation

@[simp] theorem problemWithBalance_ambient (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → Place dimension)
    (Momentum : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) :
    (problemWithBalance dimension Value Index μ reader spatialDirection Momentum
      BranchState Presentation presentation).Ambient =
      FieldObject dimension Value := rfl

@[simp] theorem problemWithBalance_baseline (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → Place dimension)
    (Momentum : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation)
    (object : FieldObject dimension Value) :
    (problemWithBalance dimension Value Index μ reader spatialDirection Momentum
      BranchState Presentation presentation).Baseline object =
      IsLocalSolution dimension Value μ Momentum
        (HarmonicKernelNormalized dimension Value Index μ reader
          spatialDirection) object := rfl

/--
**The registered target of a balanced problem.**

Takes exactly the arguments `problemWithBalance` takes, so an application never
restates its own baseline and cannot get the two out of step.  Mirrors
`Graph.minimumDegreeCycleTarget`, which likewise hands back the target of the
problem it was given rather than asking the application to rebuild it.
-/
def noSingularityTargetOfBalance (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → Place dimension)
    (Momentum : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) :
    Core.Target
      (problemWithBalance dimension Value Index μ reader spatialDirection
        Momentum BranchState Presentation presentation) :=
  noSingularityTarget dimension Value μ
    (IsLocalSolution dimension Value μ Momentum
      (HarmonicKernelNormalized dimension Value Index μ reader spatialDirection))
    BranchState Presentation presentation

end Hypostructure.PDE
