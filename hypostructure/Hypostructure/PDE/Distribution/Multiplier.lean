import Hypostructure.PDE.Solution.ParabolicRegularity

/-!
# Matrices of Fourier multipliers

A solution operator handed to the framework is often known by one property and
one property only: *it is a matrix of Fourier multipliers*.  Nothing else — no
continuity on a Sobolev scale, no estimate, no relation to `SmoothOn` — is
available, and, as this module shows, nothing else is needed for the two facts a
local regularity argument actually consumes:

* the operator commutes with every directional derivative;
* the operator commutes with the heat operator of
  `PDE/Solution/ParabolicRegularity.lean`.

Both are proved from the multiplier structure alone.  The reason is the one-line
observation of that file's `Multipliers` section: composing two Fourier
multipliers is the multiplier of the *product* of their symbols, and
multiplication of functions is commutative.

## What the structure carries, and what it deliberately does not

`QuotientRecovery` carries a symbol matrix and a temperate-growth hypothesis on
each entry — the standing hypothesis under which a Fourier multiplier acts on
tempered distributions at all — and nothing more.  In particular:

* there is **no** hypothesis "the symbol does not depend on the frequency in the
  distinguished direction", the literal reading of *time-independent*.  That
  hypothesis is simply not required: two multipliers commute whatever their
  symbols are.
* there is **no** continuity field.  A consumer that needs an estimate must
  supply it separately; a consumer that needs only commutation gets it here for
  free.

## Generality

The index type of the matrix is arbitrary (finite, so the sum defining the
action makes sense) and the underlying space is an arbitrary finite-dimensional
real inner product space.  Nothing in the argument sees a dimension.

This module sits downstream of `PDE/Solution/ParabolicRegularity.lean`, which
owns `heatOperator` and the commutation lemmas, and nothing in the framework
depends on it, so it introduces no cycle.
-/

namespace Hypostructure.PDE.Distribution.Multiplier

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution.ParabolicRegularity
open scoped SchwartzMap Real LineDeriv

universe uPoint uValue uIndex uComponent

section Matrix

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {Component : Type uComponent} [Fintype Component]

/--
**A recovery operator carried as a matrix of Fourier multipliers.**

This is the whole of the data: for each pair of components a symbol on `Point`,
and the temperate-growth hypothesis that makes it act.  The two theorems below —
commutation with a directional derivative and with the heat operator — are
*proved* from that structure, so an argument that only needs those two facts can
take the operator as a black box of this shape.
-/
structure QuotientRecovery (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] (Component : Type uComponent) where
  /-- The symbol matrix: entry `row column` is the multiplier through which the
  `column` component of the datum enters the `row` component of the output. -/
  symbol : Component → Component → Point → ℂ
  /-- Each symbol has temperate growth, the standing hypothesis under which a
  Fourier multiplier acts on tempered distributions at all. -/
  symbol_temperate : ∀ row column, (symbol row column).HasTemperateGrowth

namespace QuotientRecovery

variable (recovery : QuotientRecovery Point Component)

/-- The recovery operator applied to a datum, component by component. -/
noncomputable def apply (data : Component → 𝓢'(Point, Value)) :
    Component → 𝓢'(Point, Value) :=
  fun row => ∑ column, fourierMultiplierCLM Value (recovery.symbol row column) (data column)

/--
**The recovery operator commutes with distributional differentiation**,
`∂_v (T W) = T (∂_v W)`.

The classical proof of such a statement is a duality computation.  Here it is
three lines: `∂_v` is the Fourier multiplier with symbol `2πi⟪ξ,v⟫`, each entry
of `T` is a Fourier multiplier too, and multipliers commute.  Nothing analytic
about `T` is used, which is exactly why the structure above carries nothing
analytic.
-/
theorem timeDeriv_apply (direction : Point) (data : Component → 𝓢'(Point, Value)) :
    (fun row => ∂_{direction} (recovery.apply data row)) =
      recovery.apply (fun column => ∂_{direction} (data column)) := by
  funext row
  simp only [apply]
  rw [lineDerivOp_finset_sum]
  exact Finset.sum_congr rfl fun column _ =>
    lineDerivOp_fourierMultiplierCLM_comm (recovery.symbol_temperate row column) _ _

/-- **The recovery operator commutes with the heat operator**, for the same
reason and by the same proof.  This is what carries a heat equation satisfied by
the datum over to a heat equation satisfied by the recovered field. -/
theorem heatOperator_apply (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (data : Component → 𝓢'(Point, Value)) (row : Component) :
    heatOperator basis timeIndex (recovery.apply data row) =
      recovery.apply
        (fun column => heatOperator basis timeIndex (data column)) row := by
  simp only [apply]
  rw [heatOperator_finset_sum]
  exact Finset.sum_congr rfl fun column _ =>
    fourierMultiplierCLM_heatOperator_comm (recovery.symbol_temperate row column) _ _ _

end QuotientRecovery

end Matrix

end Hypostructure.PDE.Distribution.Multiplier
