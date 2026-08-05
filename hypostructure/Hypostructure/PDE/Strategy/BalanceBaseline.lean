import Hypostructure.Core.Strategy.Data
import Hypostructure.PDE.LocalSolution

/-!
# Balance problem-input projection

The mirror of `Hypostructure/Graph/Strategy/MinimumDegreeBaseline.lean`, whose
doc-comment states the principle this file follows verbatim:

> This adapter exposes the baseline theorem already carried by Core's typed
> problem input.  It adds no application data and performs no strategy work:
> the conclusion is the literal registered baseline proposition.

For a problem registered through `PDE.problemWithBalance`, the balance *is* the
baseline, so every piece of it is a projection of `input.baseline`.  A strategy
that needs the momentum identity reads it here; it never asks an application
for it, exactly as a graph strategy never asks for a minimum-degree proof.
-/

namespace Hypostructure.PDE.Strategy

open Hypostructure
open MeasureTheory
open scoped Distributions ContDiff

universe v w x

variable {dimension : ℕ} {Value : Type w}
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  {Index : Type x} [Fintype Index]
  {μ : Measure (PDE.Place dimension)}
  {reader : Index → (Value →L[ℝ] ℝ)}
  {timeDirection : PDE.Place dimension}
  {spatialDirection : Index → PDE.Place dimension}
  {BranchState : PDE.FieldObject dimension Value → Type v}
  {Presentation : Type} {presentation : Presentation}

variable {Momentum : PDE.FieldObject dimension Value → Prop}

/-- The problem input of a canonical balanced problem. -/
abbrev BalancedInput (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Index : Type x) [Fintype Index]
    (μ : Measure (PDE.Place dimension))
    (reader : Index → (Value →L[ℝ] ℝ))
    (spatialDirection : Index → PDE.Place dimension)
    (Momentum : PDE.FieldObject dimension Value → Prop)
    (BranchState : PDE.FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) : Type _ :=
  Core.Strategy.ProblemInput
    (PDE.problemWithBalance dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation)

/-- **A Core problem input for a canonical balanced problem already contains
the balance.**  The literal analogue of
`minimumDegreeAtLeast_of_problemInput`. -/
theorem isLocalSolution_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    PDE.IsLocalSolution dimension Value μ Momentum
      (PDE.HarmonicKernelNormalized dimension Value Index μ reader
        spatialDirection) input.object :=
  input.baseline

/-- **The problem's own equation, as a projection.**  Whatever the registered
`Momentum` is, the selected residual already satisfies it; no strategy ever
re-derives it and no application ever proves it on demand. -/
theorem momentum_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    Momentum input.object :=
  input.baseline.momentum

/-- The problem's normalization, as a projection. -/
theorem gauge_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    PDE.HarmonicKernelNormalized dimension Value Index μ reader spatialDirection
      input.object :=
  input.baseline.gauge

/-- Smoothness of the source, as a projection. -/
theorem sourceSmooth_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    ContDiffOn ℝ ∞ input.object.source
      (input.object.domain : Set (PDE.Place dimension)) :=
  input.baseline.sourceSmooth

/-- The field's representation, as a projection. -/
theorem fieldRepresents_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    ∀ test : 𝓓(input.object.domain, ℝ),
      input.object.fieldState test =
        ∫ place, test place • input.object.field place ∂μ :=
  input.baseline.fieldRepresents

/-- The source's representation, as a projection. -/
theorem sourceRepresents_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    ∀ test : 𝓓(input.object.domain, ℝ),
      input.object.sourceState test =
        ∫ place, test place • input.object.source place ∂μ :=
  input.baseline.sourceRepresents

/-- The linear parabolic law of a residual, spelled out, for a problem that
registered `PDE.LinearParabolicMomentum` as its equation.  This is the *only*
declaration in the balance layer that mentions a particular PDE, and it is a
specialization of `momentum_of_problemInput`, not an extra hypothesis. -/
theorem linearParabolicMomentum_of_problemInput
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      (PDE.LinearParabolicMomentum dimension Value Index reader timeDirection
        spatialDirection)
      BranchState Presentation presentation) :
    ∀ (test : 𝓓(input.object.domain, ℝ)) (coordinate : Index),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection :
            𝓓'(input.object.domain, Value) →L[ℝ] 𝓓'(input.object.domain, Value))
              input.object.fieldState test) -
          reader coordinate
            ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(input.object.domain, Value) →L[ℝ]
                  𝓓'(input.object.domain, Value))
                  ((Distribution.lineDerivCLM (spatialDirection axis) :
                    𝓓'(input.object.domain, Value) →L[ℝ]
                      𝓓'(input.object.domain, Value))
                      input.object.fieldState)) test) +
          (Distribution.lineDerivCLM (spatialDirection coordinate) :
            𝓓'(input.object.domain, ℝ) →L[ℝ] 𝓓'(input.object.domain, ℝ))
            input.object.potential test =
        reader coordinate (input.object.sourceState test) :=
  input.baseline.momentum

/-- The balance, exposed as a residual query.  The query-shaped form a strategy
consumes; it is merely the registered baseline proposition, exactly as
`minimumDegreeThresholdQuery` is merely the registered threshold. -/
def balanceQuery :
    Core.Residual.Query
      (BalancedInput dimension Value Index μ reader spatialDirection Momentum
        BranchState Presentation presentation)
      (fun input =>
        PDE.IsLocalSolution dimension Value μ Momentum
          (PDE.HarmonicKernelNormalized dimension Value Index μ reader
            spatialDirection) input.object) :=
  fun input => input.baseline

@[simp] theorem read_balanceQuery
    (input : BalancedInput dimension Value Index μ reader spatialDirection
      Momentum BranchState Presentation presentation) :
    (balanceQuery (BranchState := BranchState) (presentation := presentation))
      input = input.baseline := rfl

end Hypostructure.PDE.Strategy
