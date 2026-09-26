import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contracts: forced curvature cost and the two-budget entropy split, `[47]`--`[54]`

Proof-agnostic contract lemmas for `cor:forced-curvature-cost`,
`def:remainder-entropy`, `prop:two-budget` (a) and `prop:entropy-high-theta`.
Each lemma is stated over a `Graph.FiniteObject` with the registered
`Parameters` as a parameter and every paper hypothesis explicit; its conclusion
is exactly the statement of the fact it proves.  This module imports no
strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Nodes `[47]`--`[48]`, `cor:forced-curvature-cost`.**  Substituting the
exact full rank `r_Ω(R) = W₂(R)` into the demand floor of `lem:wedge-lower`
and applying the registered cost to both sides. -/
theorem forcedCurvatureCost_of_fullRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (wedgeSupply : WedgeSupplyStatement data object)
    (rank : CurvatureFullRankStatement data object) :
    ForcedCurvatureCostStatement data object := by
  have floor := wedgeSupply.2
  rcases rank with ⟨packing, _canonical, valid, maximal, rankEq⟩
  refine ⟨packing, valid, maximal, ?_⟩
  have demand := floor packing valid
  -- `W₂(R) ≤ r_Ω(R)`, from the exact full-rank equality.
  have supply :
      remainderWedgeSupply object packing ≤
        remainderCurvatureTargetRank data object packing :=
    rankEq.ge
  calc data.curvatureCost *
        (data.threshold * (object.remainderSupport packing).card +
          2 * (2 * (data.windowOrder - 1) * packing.card))
      ≤ data.curvatureCost *
          (remainderCurvatureTargetRank data object packing +
            2 * (data.threshold * (data.windowOrder * packing.card) +
              data.surplusThreshold object.vertexCount)) :=
        Nat.mul_le_mul_left _
          (le_trans demand (Nat.add_le_add_right supply _))
    _ = _ := by ring

/-- **Node `[50]`, high arm.**  At the fixed maximum packing,
`n^{|R|} ≤ |𝒢(R)|^d` is the high-entropy branch. -/
theorem remainderEntropyHigh_of_atLeast (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (high :
      Graph.AtLeastEntropyRate object.vertexCount data.entropyDenominator
        data.windowOrder data.threshold
        (object.positiveDeficiency
          (object.remainderSupport (canonicalWindowPacking data object))
          data.threshold)
        (object.internalEdgeCount
          (object.remainderSupport (canonicalWindowPacking data object)))
        (object.remainderSupport (canonicalWindowPacking data object)).card) :
    RemainderEntropyHighStatement data object :=
  ⟨canonicalWindowPacking data object, rfl,
    (Classical.choose_spec
      (object.exists_windowPacking_card_eq data.windowOrder)).1, high⟩

/-- **Node `[50]`, low arm.**  At the fixed maximum packing, failure of
`n^{|R|} ≤ |𝒢(R)|^d` is the strict low-entropy comparison. -/
theorem remainderEntropyLow_of_not_atLeast (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (notHigh :
      ¬ Graph.AtLeastEntropyRate object.vertexCount data.entropyDenominator
        data.windowOrder data.threshold
        (object.positiveDeficiency
          (object.remainderSupport (canonicalWindowPacking data object))
          data.threshold)
        (object.internalEdgeCount
          (object.remainderSupport (canonicalWindowPacking data object)))
        (object.remainderSupport (canonicalWindowPacking data object)).card) :
    RemainderEntropyLowStatement data object :=
  ⟨canonicalWindowPacking data object, rfl,
    (Classical.choose_spec
      (object.exists_windowPacking_card_eq data.windowOrder)).1,
    (Graph.not_atLeastEntropyRate_iff _ _ _ _ _ _ _).mp notHigh⟩

/-- **Node `[52]`, `prop:two-budget` (a): the joint demand.**  Raising the
joint demand to the `d`-th power and substituting the high-entropy arm's
`n^{|R|} ≤ |𝒢(R)|^d` for the remainder factor. -/
theorem entropyPackageDemand_of_high (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (high : RemainderEntropyHighStatement data object) :
    EntropyPackageDemandStatement data object := by
  simp only [EntropyPackageDemandStatement]
  obtain ⟨_packing, rfl, _valid, high⟩ := high
  rw [jointPackageDemand, mul_pow]
  exact Nat.mul_le_mul (le_refl _) high

/-- **Node `[54]`, `prop:entropy-high-theta`: the joint demand fits the
labelled skeleton budget.**  If the hot family is retained, the package rate
puts the joint demand below its retained code, and the realized-code and
skeleton-dominance clauses put that code below the budget.  If no family is
retained, the hot family is empty and the remainder glue gives the bound. -/
theorem entropyCapBound_of_hotColdPartition (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (split : HotColdWindowStatement data object)
    (package : WindowPackageSeparatedStatement data object)
    (dominates : SkeletonDominatesStatement object) :
    EntropyCapBoundStatement data object := by
  change jointPackageDemand data object ≤ Graph.skeletonBudget object
  obtain ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint,
    _cover⟩ := split
  obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
    _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  rcases hotFacts.2.1 with retained | allCold
  · obtain ⟨State, stateOf, _packageStates, retainedCodeLe⟩ := retained
    have demandLe : jointPackageDemand data object ≤
        retainedCode data object (canonicalHotWindows data object) := by
      unfold jointPackageDemand retainedCode
      calc
        2 ^ (data.windowRate *
              data.separatedScaleCount object.vertexCount *
              (canonicalHotWindows data object).card) *
            remainderStates data object (canonicalWindowPacking data object)
            ≤ 2 ^ (windowPackageBits data object *
                  (canonicalHotWindows data object).card) *
                remainderStates data object (canonicalWindowPacking data object) :=
              Nat.mul_le_mul_right _
                (Nat.pow_le_pow_right (by omega)
                  (Nat.mul_le_mul_right _ rateLe))
        _ = 2 ^ (windowPackageBits data object *
                  (canonicalHotWindows data object).card) *
                remainderStates data object (canonicalWindowPacking data object) *
                  1 := by
              rw [Nat.mul_one]
        _ ≤ 2 ^ (windowPackageBits data object *
                  (canonicalHotWindows data object).card) *
                remainderStates data object (canonicalWindowPacking data object) *
                2 ^ (data.curvatureCost *
                  remainderCurvatureTargetRank data object
                    (canonicalWindowPacking data object)) :=
              Nat.mul_le_mul_left _ Nat.one_le_two_pow
    exact demandLe.trans (retainedCodeLe.trans (dominates.2 State stateOf))
  · unfold jointPackageDemand
    rw [allCold.1, Finset.card_empty, Nat.mul_zero, pow_zero, Nat.one_mul]
    exact Graph.RemainderGlue.remainderStateCount_le_skeletonBudget _ _ _ _

end Hypostructure.Graph.Contracts.Spine
