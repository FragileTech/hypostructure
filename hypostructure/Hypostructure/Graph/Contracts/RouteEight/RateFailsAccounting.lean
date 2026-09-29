import Hypostructure.Graph.Contracts.RouteEight.RateFailsFlow
import Hypostructure.Graph.Statements.Route8RateFailsAccounting

/-!
# Contracts: the stub-deficit identity, the window/deficit dichotomy, the entry count
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- `e(X) + exc(X) = def⁺(X) + σ(X)`: per vertex, `(d − i) + (i − δ)⁺ = (δ − i)⁺ + (d − δ)`. -/
theorem boundaryIncidence_add_excess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.boundaryIncidence support +
        remainderInternalExcess object support threshold =
      object.positiveDeficiency support threshold +
        object.ambientSurplus support threshold := by
  -- The generic identity is `Graph/StubDeficit.lean`'s (single proof; dedup
  -- g-audit-int with g-audit-54's `K .stubDeficitIdentity`).
  unfold remainderInternalExcess
  rw [object.boundaryIncidence_add_internalExcess support threshold baseline, Nat.add_comm]

theorem excess_le_surplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    remainderInternalExcess object support threshold ≤
      object.ambientSurplus support threshold := by
  unfold FiniteObject.ambientSurplus remainderInternalExcess FiniteObject.internalExcess
  refine Finset.sum_le_sum fun vertex _ => ?_
  have := object.internalDegree_le_degree support vertex
  omega

/-- **The stub-deficit identity at G.** -/
theorem route8StubDeficit (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (join : Route8RateFailsJoinStatement data object) :
    Route8StubDeficitStatement data object := by
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have ident := boundaryIncidence_add_excess object
    (object.remainderSupport (canonicalWindowPacking data object)) data.threshold
    baselineAll
  have joinEq := join.1
  unfold Route8StubDeficitStatement
  dsimp only
  refine ⟨ident, excess_le_surplus _ _ _, ⟨object.card_positiveDeficiencyUnits _ _, ?_⟩, ?_⟩
  · rw [object.card_positiveDeficiencyUnits, object.card_windowRemainderIncidences]
    exact object.positiveDeficiency_le_boundaryIncidence _ _ baselineAll
  · omega

/-- **The deficit against the window stubs, or the isolated windows.** -/
theorem route8DeficitVsStubs (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold)
    (stub : Route8StubDeficitStatement data object) :
    Route8DeficitVsStubsStatement data object := by
  have ident := stub.2.2.2
  have sub := stub.2.1
  have prod : coldExternalStubCount data * (canonicalWindowPacking data object).card =
      data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) -
        2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card := by
    simp only [coldExternalStubCount]
    rw [Nat.sub_mul, Nat.mul_assoc]
  have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
    have := Nat.mul_le_mul_right data.windowOrder threeLe
    omega
  have debit' : 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card ≤
      data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) := by
    have := Nat.mul_le_mul_right (canonicalWindowPacking data object).card debit
    rw [Nat.mul_assoc data.threshold] at this
    exact this
  unfold Route8DeficitVsStubsStatement
  dsimp only
  generalize 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card = q
    at ident prod debit'
  rw [prod]
  by_cases h : data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) - q ≤
      object.positiveDeficiency (object.remainderSupport (canonicalWindowPacking data object))
        data.threshold
  · left
    refine ⟨h, ?_, ?_⟩ <;> omega
  · right
    refine ⟨by omega, by omega⟩

/-- **The route-8 entries from a source before the rate.** -/
theorem route8EntryLowerBound (data : Parameters) (object : FiniteObject.{u})
    (burden : Route8BasinBurden data object)
    (join : Route8RateFailsJoinStatement data object) :
    Route8EntryLowerBoundStatement data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨basinCount, hcount, scaled, hscaled, hle⟩ := burden
  unfold Route8EntryLowerBoundStatement
  refine ⟨basinCount, hcount, ?_, ?_⟩
  · rw [← hscaled]; exact hle
  · by_cases lbd : (object.remainderSupport (canonicalWindowPacking data object)).card ≤
        Graph.TypeBEnvelopeCharge.route8Deficit object
            (object.remainderSupport (canonicalWindowPacking data object))
            data.threshold data.dischargeScale
            ((object.canonicalPieces
              (object.remainderSupport (canonicalWindowPacking data object))).filter
              (Route8Survives data object (canonicalWindowPacking data object))) +
          data.dischargeScale * object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
          data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount
    · left
      refine ⟨lbd, ?_⟩
      have joinEq := join.1
      have step : data.dischargeScale * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
          data.dischargeScale * (object.crossWindowIncidences
            (canonicalWindowPacking data object)).card +
          data.dischargeScale * (2 * (data.windowOrder - 1) *
            (canonicalWindowPacking data object).card) =
          data.dischargeScale * (data.threshold * (data.windowOrder *
            (canonicalWindowPacking data object).card) +
            object.ambientSurplus (object.windowSupport (canonicalWindowPacking data object))
              data.threshold) := by
        rw [← Nat.mul_add, ← Nat.mul_add, ← joinEq]; ring
      have step2 := Nat.mul_add data.dischargeScale
        (object.crossWindowIncidences (canonicalWindowPacking data object)).card
        (2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card)
      rw [← hscaled] at lbd
      omega
    · right
      exact Nat.lt_of_not_le lbd

end Hypostructure.Graph.Contracts.RouteEight
