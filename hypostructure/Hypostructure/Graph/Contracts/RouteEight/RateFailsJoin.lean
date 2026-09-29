import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Statements.Route8RateFailsJoin

/-!
# Contracts: the failed private-carrier rate against the exact window join

`Graph.Route8Census.Rate` fails at G's canonical packing.  The supply of the rate is
`e(R,W)`, and `lem:exact-window-join-identity` at `P₀` writes
`e(R,W) + X = β·p + σ_W` with `X` the cross-window incidences of `P₀`; the failed
rate therefore reads `δ·n + (δs+1)·X ≤ A·p + D·T(n)`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The arithmetic of the failed rate against the join identity. -/
theorem route8RateFailsJoin_arith
    {δ k c β F p T n R e X σ : Nat}
    (size : R + k * p = n)
    (join : e + X = β * p + σ)
    (fails : δ * R ≤ c * e + δ * (F * T)) :
    δ * n + c * X ≤ (δ * k + c * β) * p + c * σ + δ * (F * T) := by
  subst size
  have h1 : c * (e + X) = c * (β * p + σ) := by rw [join]
  have h3 : c * (e + X) = c * e + c * X := Nat.mul_add c e X
  have h4 : c * (β * p + σ) = c * β * p + c * σ := by ring
  have h5 : δ * (R + k * p) = δ * R + δ * k * p := by ring
  have h6 : (δ * k + c * β) * p = δ * k * p + c * β * p := by ring
  omega

/-- **The failed rate against the exact window join at G.** -/
theorem route8RateFailsJoin (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (threeLe : 3 ≤ data.threshold)
    (fails : Route8RateFailsStatement data object) :
    Route8RateFailsJoinStatement data object := by
  set packing := canonicalWindowPacking data object with hpack
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have join := object.exact_window_join_identity valid baselineAll
  have cut := object.card_windowRemainderIncidences packing
  have remainder := object.remainderSupport_card_add_eq valid
  have supplyEq := Graph.Route8Census.card_supply object packing
  change ¬ ((data.threshold * data.dischargeScale + 1) *
      (Graph.Route8Census.supply object packing).card +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.remainderSupport packing).card) at fails
  rw [supplyEq] at fails
  have failsLe := Nat.not_lt.mp fails
  have prod : coldExternalStubCount data * packing.card =
      data.threshold * (data.windowOrder * packing.card) -
        2 * (data.windowOrder - 1) * packing.card := by
    simp only [coldExternalStubCount]
    rw [Nat.sub_mul, Nat.mul_assoc]
  rw [cut] at join
  have joinE : object.boundaryIncidence (object.remainderSupport packing) +
      (object.crossWindowIncidences packing).card =
      coldExternalStubCount data * packing.card +
        object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
          data.threshold := by
    have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
      have := Nat.mul_le_mul_right data.windowOrder threeLe
      omega
    have debit' : 2 * (data.windowOrder - 1) * packing.card ≤
        data.threshold * (data.windowOrder * packing.card) := by
      have := Nat.mul_le_mul_right packing.card debit
      rw [Nat.mul_assoc data.threshold] at this
      exact this
    generalize 2 * (data.windowOrder - 1) * packing.card = q at join prod debit'
    rw [prod]; omega
  refine ⟨join, ?_⟩
  have arith := route8RateFailsJoin_arith
    (δ := data.threshold) (k := data.windowOrder)
    (c := data.threshold * data.dischargeScale + 1)
    (β := coldExternalStubCount data)
    (F := data.bridgeMassFactor * data.dischargeScale) (p := packing.card)
    (T := data.surplusThreshold object.vertexCount)
    (n := object.vertexCount) (R := (object.remainderSupport packing).card)
    (e := object.boundaryIncidence (object.remainderSupport packing))
    (X := (object.crossWindowIncidences packing).card)
    (σ := object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
      data.threshold)
    remainder joinE
    failsLe
  unfold densityOrderPackingCoeff
  exact arith

/-- **The cross-window incidences against the density cap at G.** -/
theorem route8RateFailsCrossBound (data : Parameters) (object : FiniteObject.{u})
    (scaleCount : data.separatedScaleCount object.vertexCount =
      Nat.log2 object.vertexCount)
    (ceiling : SurplusAtOrBelowStatement data object)
    (baseline : data.threshold ≤ object.minDegree)
    (densityCap : DensityCapStatement data object)
    (join : Route8RateFailsJoinStatement data object) :
    Route8RateFailsCrossBoundStatement data object := by
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have windowSurplus :
      object.ambientSurplus (Graph.FiniteObject.windowSupport
          (canonicalWindowPacking data object)) data.threshold ≤
        data.surplusThreshold object.vertexCount :=
    le_trans (object.ambientSurplus_le_degreeSurplus _ data.threshold baselineAll)
      ceiling
  have cardinality := (canonicalWindowPacking_spec data object).2.1
  have cap0 := densityCap.1
  rw [← cardinality, scaleCount] at cap0
  simp only [Graph.dyadicScaleCount] at cap0
  have lower0 := join.2
  unfold Route8RateFailsCrossBoundStatement
  simp only [boundedDensityOrderSlack, densityOrderSurplusCoeff,
    densityOrderPackingCoeff] at *
  set p := (canonicalWindowPacking data object).card
  set X := (object.crossWindowIncidences (canonicalWindowPacking data object)).card
  set L := Nat.log2 object.vertexCount
  set T := data.surplusThreshold object.vertexCount
  set σ := object.ambientSurplus (Graph.FiniteObject.windowSupport
    (canonicalWindowPacking data object)) data.threshold
  set A := data.threshold * data.windowOrder +
    (data.threshold * data.dischargeScale + 1) * coldExternalStubCount data
  set c := data.threshold * data.dischargeScale + 1
  set F := data.bridgeMassFactor * data.dischargeScale
  set r := data.windowRate
  set δ := data.threshold
  set n := object.vertexCount
  have lower : δ * n + c * X ≤ A * p + (c + δ * F) * T := by
    have := Nat.mul_le_mul_left c windowSurplus
    have e : (c + δ * F) * T = c * T + δ * (F * T) := by ring
    omega
  have cap : 2 * (r * L * p) ≤ (L + 1) * (δ * n + T) +
      data.densitySlack * (r * L) * T := by
    exact cap0
  have step1 : 2 * r * L * (δ * n + c * X) ≤
      2 * r * L * (A * p + (c + δ * F) * T) := Nat.mul_le_mul_left _ lower
  have step2 : 2 * r * L * (A * p + (c + δ * F) * T) =
      A * (2 * (r * L * p)) + L * T * (2 * r * (c + δ * F)) := by ring
  have step3 : A * (2 * (r * L * p)) ≤
      A * ((L + 1) * (δ * n + T) + data.densitySlack * (r * L) * T) :=
    Nat.mul_le_mul_left _ cap
  have step4 : A * ((L + 1) * (δ * n + T) + data.densitySlack * (r * L) * T) +
      L * T * (2 * r * (c + δ * F)) =
      A * ((L + 1) * (δ * n + T)) +
        L * T * (A * (data.densitySlack * r) + 2 * r * (c + δ * F)) := by ring
  omega

end Hypostructure.Graph.Contracts.RouteEight
