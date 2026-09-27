import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Statements.ColdResiduals

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
`[54]`'s returned residual (`AllColdEntropyResidualStatement`): on this arm the joint realization
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
`[54]`'s returned residual. -/
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

/-- **The remainder glue at `G`, on disjoint supports**
(`lem:remainder-glue-injection`, every outer edge set): the remainder states of
`R₀` on the pairs inside `R₀`, times every placement of `G`'s outer edges on the
pairs outside `R₀`, are distinct labelled skeletons of `G`'s class `𝒢_{n,m}`:
`RS(R₀) · remainderOuterRoom ≤ skeletonBudget`. -/
theorem remainderStates_mul_outerRoom_le (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    remainderStates data object (canonicalWindowPacking data object) *
        remainderOuterRoom data object ≤
      Graph.skeletonBudget object :=
  Graph.RemainderGlue.remainderStateCount_mul_outerRoom_le_skeletonBudget
    data.windowOrder data.threshold _ _

/-- **The joint realization at `G` by the glue on disjoint supports.**  The
remainder states of `R₀` live on the pairs inside `R₀`; if the window package
of `P₀` and the forced obstruction bits of node `[48]` fit in the outer room
(`2^{rate·s·p₁₃} · 2^{K|R|−o(|R|)} ≤ remainderOuterRoom`), they are carried by
the outer pairs, disjoint from `R₀`, and the product family is realized by
distinct skeletons of `G`'s class: node `[54]`'s bound holds. -/
theorem entropyCapBound_of_outerRoom (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (room :
      2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
            (canonicalWindowPacking data object).card) *
          2 ^ forcedObstructionBits data object ≤
        remainderOuterRoom data object) :
    EntropyCapBoundStatement data object := by
  change jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
    Graph.skeletonBudget object
  refine le_trans ?_ (remainderStates_mul_outerRoom_le data object)
  unfold jointPackageDemand
  calc 2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
            (canonicalWindowPacking data object).card) *
          remainderStates data object (canonicalWindowPacking data object) *
        2 ^ forcedObstructionBits data object
      = remainderStates data object (canonicalWindowPacking data object) *
          (2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
              (canonicalWindowPacking data object).card) *
            2 ^ forcedObstructionBits data object) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ room

/-- **The obstruction at `G` on `[54]`'s branch.**  On the active arm of node
`[53]` the outer room of `G` at `R₀` is strictly smaller than the window package
of `P₀` times the forced obstruction bits: the glue on disjoint supports (the
only realization map the paper builds on this path) cannot carry the product
family.  With `remainderStates_mul_outerRoom_le`, `[53]`-active gives
`RS · room ≤ B < RS · 2^{rate·s·p₁₃} · 2^F`. -/
theorem outerRoom_lt_of_entropyCapActive (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (active : EntropyCapActiveStatement data object) :
    remainderOuterRoom data object <
      2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
            (canonicalWindowPacking data object).card) *
        2 ^ forcedObstructionBits data object := by
  by_contra fits
  push Not at fits
  exact (Nat.not_lt_of_ge (entropyCapBound_of_outerRoom data object fits)) active

/-- **The independence premise of `prop:entropy-high-theta` is the bound
itself.**  In the finite form of `lem:independent-target-entropy` /
`lem:skeleton-dominates` (a state map on `G`'s labelled skeleton class whose
range has at least the family's number of states), the premise "the window
package of `P₀`, the remainder bits and the forced obstruction bits form one
independently target-testable family arising canonically from `𝒢_{n,m}`" is
equivalent to node `[54]`'s bound `demand · 2^F ≤ skeletonBudget`.  So on the
active arm of `[53]` (its strict negation) the premise is refuted by `G`'s
ledger, and the paper's step (2) at `[54]` is its own conclusion. -/
theorem jointRealization_iff_entropyCapBound (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dominates : SkeletonDominatesStatement object) :
    (∃ (State : Type u)
        (stateOf : Graph.PackedWindowRealization.Skeleton
          object.vertexCount object.edgeCount → State),
        jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
          Nat.card (Set.range stateOf)) ↔
      EntropyCapBoundStatement data object := by
  constructor
  · rintro ⟨State, stateOf, realized⟩
    exact realized.trans (dominates.2 State stateOf)
  · intro bound
    refine ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton object.vertexCount
      object.edgeCount), ULift.up, ?_⟩
    have range : Nat.card (Set.range (ULift.up.{u} :
        Graph.PackedWindowRealization.Skeleton object.vertexCount object.edgeCount →
          _)) = Graph.skeletonBudget object := by
      rw [Set.range_eq_univ.mpr (fun x => ⟨x.down, rfl⟩), Nat.card_univ,
        Nat.card_ulift, dominates.1]
    rw [range]
    exact bound

/-- **Node `[54]` on a retained package** (`prop:entropy-high-theta`): if the
window package of `P₀` is retained (`WindowFamilyRealized P₀`), the package
rate puts the window part below its retained code, node `[48]` puts the forced
bits below the exact curvature code that retained code carries, and the
realized-code and skeleton-dominance clauses put that code below the budget. -/
theorem entropyCapBound_of_retained (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (package : WindowPackageSeparatedStatement data object)
    (dominates : SkeletonDominatesStatement object)
    (cost : ForcedCurvatureCostStatement data object)
    (retained : WindowFamilyRealized data object (canonicalWindowPacking data object)) :
    EntropyCapBoundStatement data object := by
  change jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
    Graph.skeletonBudget object
  obtain ⟨_packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  have forcedLe := forcedObstructionBits_le_cost data object cost
  obtain ⟨State, stateOf, _packageStates, retainedCodeLe⟩ := retained
  have demandLe : jointPackageDemand data object *
        2 ^ forcedObstructionBits data object ≤
      retainedCode data object (canonicalWindowPacking data object) := by
    unfold jointPackageDemand retainedCode
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ rateLe)))
      (Nat.pow_le_pow_right (by omega) forcedLe)
  exact demandLe.trans (retainedCodeLe.trans (dominates.2 State stateOf))

/-- The joint realization inequality is node `[54]`'s bound, with the factors
of the joint package demand written in the paper's order. -/
theorem entropyJointRealization_iff_entropyCapBound (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    EntropyJointRealizationStatement data object ↔
      EntropyCapBoundStatement data object := by
  unfold EntropyJointRealizationStatement
  change _ ↔ jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
    Graph.skeletonBudget object
  unfold jointPackageDemand
  rw [Nat.mul_comm (remainderStates data object (canonicalWindowPacking data object))]

/-- **Node `[54]`, `prop:entropy-high-theta`, on the arm where the joint
realization holds** (tex 9921): the remainder states of `R₀`, the window
package of `P₀` and the forced obstruction bits are realized by one state map
on G's labelled skeleton class (`jointRealization_iff_entropyCapBound`, the
finite form of `lem:independent-target-entropy`), so the joint package fits the
labelled skeleton budget (`lem:skeleton-dominates`). -/
theorem entropyCapBound_of_jointRealization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dominates : SkeletonDominatesStatement object)
    (joint : EntropyJointRealizationStatement data object) :
    EntropyCapBoundStatement data object := by
  have realized := (jointRealization_iff_entropyCapBound data object dominates).2
    ((entropyJointRealization_iff_entropyCapBound data object).1 joint)
  exact (jointRealization_iff_entropyCapBound data object dominates).1 realized

/-- **The residual of `[54]`, constructed at G.**  If the joint realization
inequality `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` fails at G, then: the window package
of `P₀` is not retained (a retained package proves the inequality,
`entropyCapBound_of_retained`); the remainder glue on disjoint supports gives
`RS(R₀)·room ≤ B` (`remainderStates_mul_outerRoom_le`), and the window package
with the forced bits does not fit the outer room (a fit proves the inequality,
`entropyCapBound_of_outerRoom`); node `[48]` bounds `F ≤ c_Ω·r_Ω(R₀)`; and `[53]`
is active. -/
theorem allColdEntropyResidual_of_not_jointRealization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (package : WindowPackageSeparatedStatement data object)
    (dominates : SkeletonDominatesStatement object)
    (cost : ForcedCurvatureCostStatement data object)
    (fails : ¬ EntropyJointRealizationStatement data object) :
    AllColdEntropyResidualStatement data object := by
  have notBound : ¬ EntropyCapBoundStatement data object := fun bound =>
    fails ((entropyJointRealization_iff_entropyCapBound data object).2 bound)
  refine ⟨fun retained => notBound
      (entropyCapBound_of_retained data object package dominates cost retained),
    remainderStates_mul_outerRoom_le data object, rfl,
    forcedObstructionBits_le_cost data object cost, ?_, ?_, fails⟩
  · by_contra fits
    push Not at fits
    exact notBound (entropyCapBound_of_outerRoom data object fits)
  · change ¬ (jointPackageDemand data object * 2 ^ forcedObstructionBits data object ≤
      Graph.skeletonBudget object) at notBound
    exact Nat.lt_of_not_le notBound

/-- **The `[54]` residual refutes the joint realization inequality.** -/
theorem not_jointRealization_of_residual (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (residual : AllColdEntropyResidualStatement data object) :
    ¬ EntropyJointRealizationStatement data object :=
  residual.2.2.2.2.2.2

end Hypostructure.Graph.Contracts.Spine
