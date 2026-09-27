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

universe u v

/-- **Nodes `[47]`--`[48]`, `cor:forced-curvature-cost`.**  Substituting the
exact full rank `r_Ω(R) = W₂(R)` into the demand floor of `lem:wedge-lower`
and applying the registered cost to both sides. -/
theorem forcedCurvatureCost_of_fullRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (wedgeSupply : WedgeSupplyStatement data object)
    (rank : CurvatureFullRankStatement data object) :
    ForcedCurvatureCostStatement data object := by
  have demand := wedgeSupply.2
  have rankEq := rank
  set packing := canonicalWindowPacking data object with packingDef
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
  high

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
  (Graph.not_atLeastEntropyRate_iff _ _ _ _ _ _ _).mp notHigh

/-- **Node `[52]`, `prop:two-budget` (a): the joint demand.**  Raising the
joint demand to the `d`-th power and substituting the high-entropy arm's
`n^{|R|} ≤ |𝒢(R)|^d` for the remainder factor. -/
theorem entropyPackageDemand_of_high (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (high : RemainderEntropyHighStatement data object) :
    EntropyPackageDemandStatement data object := by
  simp only [EntropyPackageDemandStatement]
  rw [jointPackageDemand, mul_pow]
  exact Nat.mul_le_mul (le_refl _) high

/-- Node `[48]` bounds its forced obstruction bits by the full-rank cost:
`K|R| − o(|R|) ≤ c_Ω·r_Ω(R₀)`. -/
theorem forcedObstructionBits_le_cost (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (cost : ForcedCurvatureCostStatement data object) :
    forcedObstructionBits data object ≤
      data.curvatureCost *
        remainderCurvatureTargetRank data object (canonicalWindowPacking data object) := by
  unfold forcedObstructionBits
  exact Nat.sub_le_iff_le_add.mpr cost

/-- **The all-cold arm of node `[22]` overflows with the full curvature code.**
On that arm the empty window family is not retained
(`¬ WindowFamilyRealized ∅`); reading the skeletons themselves as states
(`K .skeletonDominates`, `.1`), this says exactly that the remainder states of
`R₀` together with the full curvature code `2^{c_Ω·r_Ω(R₀)}` exceed the labelled
skeleton budget.  This is the Lean evidence recorded for
`OPEN-CONSTRUCTION [54] tex:9921`: on this arm the joint realization
`prop:entropy-high-theta` asserts is false for the full code, and only its
smaller forced part `K|R| − o(|R|) ≤ c_Ω·r_Ω(R₀)` remains undecided. -/
theorem allCold_code_overflow (data : Parameters) (object : Graph.FiniteObject.{u})
    (dominates : SkeletonDominatesStatement object)
    (allCold : ¬ WindowFamilyRealized data object ∅) :
    Graph.skeletonBudget object <
      remainderStates data object (canonicalWindowPacking data object) *
        2 ^ (data.curvatureCost *
          remainderCurvatureTargetRank data object (canonicalWindowPacking data object)) := by
  by_contra le
  push Not at le
  apply allCold
  refine ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton object.vertexCount
    object.edgeCount), ULift.up, ?_, ?_⟩ <;>
  · have range : Nat.card (Set.range (ULift.up.{u} :
        Graph.PackedWindowRealization.Skeleton object.vertexCount object.edgeCount →
          _)) = Graph.skeletonBudget object := by
      rw [Set.range_eq_univ.mpr (fun x => ⟨x.down, rfl⟩), Nat.card_univ,
        Nat.card_ulift, dominates.1]
    rw [range]
    first
    | simpa using Nat.succ_le_of_lt (Graph.skeletonBudget_pos object)
    | simpa [retainedCode] using le

/-- **The unretained arm overflows with the full code.**  When the window
package of the whole fixed packing `P₀` is not retained
(`¬ WindowFamilyRealized P₀`, which by node `[22]`'s maximality is exactly the
arm `𝒫_hot ≠ P₀`, including the all-cold arm), reading the skeletons themselves
as states (`K .skeletonDominates`, `.1`) shows that the full package of `P₀`, or
its retained code with the remainder states and the full curvature code
`2^{c_Ω·r_Ω(R₀)}`, exceeds the labelled skeleton budget.  Lean evidence for
`OPEN-CONSTRUCTION [54] tex:9921`. -/
theorem unretained_package_overflow (data : Parameters) (object : Graph.FiniteObject.{u})
    (dominates : SkeletonDominatesStatement object)
    (unretained : ¬ WindowFamilyRealized data object (canonicalWindowPacking data object)) :
    Graph.skeletonBudget object <
        2 ^ (windowPackageBits data object * (canonicalWindowPacking data object).card) ∨
      Graph.skeletonBudget object <
        retainedCode data object (canonicalWindowPacking data object) := by
  by_contra fits
  push Not at fits
  apply unretained
  have range : Nat.card (Set.range (ULift.up.{u} :
      Graph.PackedWindowRealization.Skeleton object.vertexCount object.edgeCount → _)) =
        Graph.skeletonBudget object := by
    rw [Set.range_eq_univ.mpr (fun x => ⟨x.down, rfl⟩), Nat.card_univ,
      Nat.card_ulift, dominates.1]
  exact ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton object.vertexCount
    object.edgeCount), ULift.up, range ▸ fits.1, range ▸ fits.2⟩

/-- **Node `[54]`, `prop:entropy-high-theta`'s independence claim, on the arm
where the window package of `P₀` is not retained.**

The paper's claim (tex 9921): *"the window package of
`lem:p13-window-package`, the remainder bits, and the forced-obstruction bits
together strictly exceed the near-cubic skeleton budget.  These bits form one
independently target-testable coordinate family, so the number of realized
target-complete states would exceed the number of labelled skeletons,
contradicting `lem:independent-target-entropy`, `lem:skeleton-dominates`."*
`eq:entropy-cap` counts the package of **all** `p₁₃` packed windows
(`jointPackageDemand`).  `lem:independent-target-entropy` needs a family
"arising canonically from graphs in a labelled graph class"; the paper never
constructs a realization of the window package of `P₀`, the remainder states
and the forced obstruction bits by one labelled class -- it asserts it.  On
[54]'s own branch (`[53]` active) the full retained code already exceeds the
budget, so this arm is the only one reached.  Stated at the selected minimal
counterexample `G`; its negation does not follow from its hypotheses
(`lean-vs-paper-discrepancies.md#open-constructions`). -/
theorem entropyCapBound_unretained
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (_selected : SelectionStatement BranchState Presentation presentation data object)
    (_unretained : ¬ WindowFamilyRealized data object (canonicalWindowPacking data object))
    (_cost : ForcedCurvatureCostStatement data object)
    (_high : RemainderEntropyHighStatement data object)
    (_package : EntropyPackageDemandStatement data object) :
    jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
      Graph.skeletonBudget object := by
  sorry -- OPEN-CONSTRUCTION [54] tex:9921 — see lean-vs-paper-discrepancies.md#open-constructions

/-- **Node `[54]`, `prop:entropy-high-theta`: the joint package of all the
windows of `P₀`, with the remainder states and the forced obstruction bits,
fits the labelled skeleton budget.**  If the window package of `P₀` is retained,
the package rate puts the window part below its retained code, node `[48]` puts
the forced bits below the exact curvature code the retained code carries, and
the realized-code and skeleton-dominance clauses put that code below the
budget.  If it is not retained, the bound is the paper's independence claim on
that arm (`entropyCapBound_unretained`). -/
theorem entropyCapBound_of_hotColdPartition
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (package : WindowPackageSeparatedStatement data object)
    (dominates : SkeletonDominatesStatement object)
    (cost : ForcedCurvatureCostStatement data object)
    (high : RemainderEntropyHighStatement data object)
    (demand : EntropyPackageDemandStatement data object) :
    EntropyCapBoundStatement data object := by
  change jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
    Graph.skeletonBudget object
  obtain ⟨_packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  have forcedLe := forcedObstructionBits_le_cost data object cost
  by_cases retained : WindowFamilyRealized data object (canonicalWindowPacking data object)
  · obtain ⟨State, stateOf, _packageStates, retainedCodeLe⟩ := retained
    have demandLe : jointPackageDemand data object *
          2 ^ forcedObstructionBits data object ≤
        retainedCode data object (canonicalWindowPacking data object) := by
      unfold jointPackageDemand retainedCode
      exact Nat.mul_le_mul
        (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ rateLe)))
        (Nat.pow_le_pow_right (by omega) forcedLe)
    exact demandLe.trans (retainedCodeLe.trans (dominates.2 State stateOf))
  · exact entropyCapBound_unretained data object selected retained cost high demand

end Hypostructure.Graph.Contracts.Spine
