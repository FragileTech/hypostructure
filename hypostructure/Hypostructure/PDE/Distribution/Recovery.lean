import Hypostructure.PDE.Distribution.Multiplier

/-!
# Recovery operators, carried by the two facts a recovery argument uses

`Multiplier.QuotientRecovery` carries a matrix of Fourier multipliers and
*proves* the two commutation facts a div--curl recovery consumes.  That is the
right theorem and the wrong hypothesis: the operator the local argument actually
recovers with is `𝒯_{B_ρ}`, the `L²(B_ρ)`-orthogonal quotient of
`stokes:def:harmonic-kernel`, and it is **not** a Fourier multiplier.  It acts
on one ball, its symbol would be singular at the origin, and
`HasTemperateGrowth` is therefore not a hypothesis any construction of it can
discharge.

So the structure below carries the two facts directly:

* `lineDeriv_apply` --- the operator commutes with directional differentiation.
  For `𝒯_{B_ρ}` this is *time-independence*, and it is the whole reason the
  recovery breaks the circularity: `∂_t^j u^⊥ = 𝒯(∂_t^j ω)` gives every time
  derivative of the recovered field from the vorticity alone, with the pressure
  never entering (`stokes:lem:time-param-quotient`).
* `heatOperator_apply` --- the operator commutes with `∂_t − Δ_x`, which is what
  carries the vorticity's heat equation over to the recovered field.

Neither is an analytic estimate; both are statements that the operator does not
mix the variables it is being commuted past.  `QuotientRecovery.toSliceRecovery`
exhibits the Fourier-multiplier realization as one of these, so nothing that
already builds a multiplier loses anything.

## `heatOperator_apply` is still a multiplier fact

The second field is weaker than `HasTemperateGrowth` but it is *not* weak enough
for `𝒯_{B_ρ}`: commuting a quotient on one ball past `Δ_x` is exactly the
boundary-term question the projection does not answer, and
`stokes:lem:time-param-quotient` never claims it — it claims commutation with
`∂_t` alone and takes the spatial derivatives from elliptic regularity of the
div--curl system instead.  So this structure is the right carrier for a
multiplier realization and the wrong one for a local Hodge quotient.
`PDE/Solution/SliceInversionRegularity.lean` carries the local interface, and its
`SliceInversion` drops `heatOperator_apply` for a `∂_t`-only commutation plus a
fixed-grade spatial-regularity statement, which is what the appendix proves.
-/

namespace Hypostructure.PDE.Distribution.Recovery

open MeasureTheory TemperedDistribution
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Distribution.Multiplier
open scoped SchwartzMap Real LineDeriv

universe uPoint uValue uIndex uComponent

section Abstract

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {Component : Type uComponent}

/--
**A recovery operator**, carried by the two commutation facts and nothing else.

The reading to keep: `apply` sends the *rotational datum* to the *recovered
field*, slice by slice, and the two fields say it does not see the direction it
is being differentiated in.  A concrete local Hodge quotient satisfies both
because it is time-independent and acts within each spatial slice; a Fourier
multiplier satisfies both because multipliers commute.  No third property of a
recovery is ever used downstream.
-/
structure SliceRecovery (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
    [BorelSpace Point]
    (Value : Type uValue) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (Index : Type uIndex) [Fintype Index] [DecidableEq Index]
    (Component : Type uComponent) where
  /-- The operator itself. -/
  apply : (Component → 𝓢'(Point, Value)) → Component → 𝓢'(Point, Value)
  /-- **Commutation with directional differentiation.**  For a time-independent
  slicewise operator this is exactly that: the derivative may be taken before or
  after recovering. -/
  lineDeriv_apply : ∀ (direction : Point) (data : Component → 𝓢'(Point, Value)),
    (fun row => ∂_{direction} (apply data row)) =
      apply fun column => ∂_{direction} (data column)
  /-- **Commutation with the heat operator.**  This is what transports a heat
  equation satisfied by the datum to one satisfied by the recovered field. -/
  heatOperator_apply : ∀ (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (data : Component → 𝓢'(Point, Value)) (row : Component),
    heatOperator basis timeIndex (apply data row) =
      apply (fun column => heatOperator basis timeIndex (data column)) row

namespace SliceRecovery

variable (recovery : SliceRecovery Point Value Index Component)

/-- The commutation read one component at a time, which is the shape a rewrite
usually wants. -/
theorem lineDeriv_apply_row (direction : Point)
    (data : Component → 𝓢'(Point, Value)) (row : Component) :
    ∂_{direction} (recovery.apply data row) =
      recovery.apply (fun column => ∂_{direction} (data column)) row :=
  congrFun (recovery.lineDeriv_apply direction data) row

/-- The iterated form: **every** time derivative of the recovered field is the
recovered field of that time derivative of the datum.  This is
`stokes:lem:time-param-quotient`'s `∂_t^j u^⊥ = 𝒯(∂_t^j ω)`, and it is what
makes the recovery route non-circular --- the pressure never appears. -/
theorem lineDerivIterate_apply (direction : Point) :
    ∀ (order : ℕ) (data : Component → 𝓢'(Point, Value)) (row : Component),
      (fun state : 𝓢'(Point, Value) => ∂_{direction} state)^[order]
          (recovery.apply data row) =
        recovery.apply
          (fun column => (fun state : 𝓢'(Point, Value) => ∂_{direction} state)^[order]
            (data column)) row := by
  intro order
  induction order with
  | zero => intro data row; simp
  | succ previous gained =>
      intro data row
      rw [Function.iterate_succ_apply, recovery.lineDeriv_apply_row direction data,
        gained]
      simp only [Function.iterate_succ_apply]

end SliceRecovery

end Abstract

section Multiplier

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
  {Component : Type uComponent} [Fintype Component]

/-- **A matrix of Fourier multipliers is a recovery operator.**  Both fields are
the theorems `Multiplier.lean` already proves, so this costs nothing and keeps
every existing construction usable at the weaker interface. -/
noncomputable def _root_.Hypostructure.PDE.Distribution.Multiplier.QuotientRecovery.toSliceRecovery
    (recovery : QuotientRecovery Point Component) :
    SliceRecovery Point Value Index Component where
  apply := recovery.apply
  lineDeriv_apply := fun direction data => recovery.timeDeriv_apply direction data
  heatOperator_apply := fun basis timeIndex data row =>
    recovery.heatOperator_apply basis timeIndex data row

@[simp] theorem toSliceRecovery_apply (recovery : QuotientRecovery Point Component)
    (data : Component → 𝓢'(Point, Value)) :
    (recovery.toSliceRecovery (Value := Value) (Index := Index)).apply data =
      recovery.apply data := rfl

end Multiplier

end Hypostructure.PDE.Distribution.Recovery
