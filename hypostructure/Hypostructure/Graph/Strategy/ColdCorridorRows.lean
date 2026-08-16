import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.ColdIncrementArithmetic

/-!
# The cold branch, nodes `[145]`--`[154]`

This module contains only paper-node operations on the literal current
`ExactLedger`: two exclusive decisions and the atomic facts currently proved
through node `[152]`.  No alternate state or detached implication is exported;
the concrete germ family required at `[153]` remains a fact of that residual.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[146]`: decide the route-8 threshold on node `[145]`'s residual. -/
noncomputable def coldRoute8Dichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    (belowFresh : K .coldRoute8Below ∉ known)
    (atOrAboveFresh : K .coldRoute8AtOrAbove ∉ known) :
    Decision (K .coldRoute8Below) (K .coldRoute8AtOrAbove) previous := by
  classical
  let _split := (previous.get (K .coldWindowLedgerSplit)).down
  exact Decision.run previous (K .coldRoute8Below) (K .coldRoute8AtOrAbove)
    `Hypostructure.Graph.Strategy.Spine.coldRoute8Dichotomy
    (if below : ColdRoute8BelowStatement data current.object then
      .inl ⟨below⟩
    else
      .inr ⟨below⟩)
    belowFresh atOrAboveFresh

/-- Node `[148]`: decide the live-hot entropy comparison on `[146]`'s no arm. -/
noncomputable def coldHotEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    (overflowFresh : K .coldHotEntropyOverflow ∉ known)
    (capFresh : K .coldHotEntropyCap ∉ known) :
    Decision (K .coldHotEntropyOverflow) (K .coldHotEntropyCap) previous := by
  classical
  let _split := (previous.get (K .coldWindowLedgerSplit)).down
  exact Decision.run previous (K .coldHotEntropyOverflow) (K .coldHotEntropyCap)
    `Hypostructure.Graph.Strategy.Spine.coldHotEntropyDichotomy
    (if overflow : ColdHotEntropyOverflowStatement data current.object then
      .inl ⟨overflow⟩
    else
      .inr ⟨Nat.le_of_not_lt overflow⟩)
    overflowFresh capFresh

/-- Node `[149]`: on `[148]`'s live-hot closing arm, publish the exact finite
`P₁₃` density cap on that same residual. -/
@[reducible] noncomputable def coldHotEntropyDensityCapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldHotEntropyDensityCap
    { Requires := [K .coldHotEntropyOverflow, K .barrierCap,
        K .surplusAtOrBelow]
      Produces := [K .densityCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _overflow := (inputs.get (K .coldHotEntropyOverflow)).down
      let cap := (inputs.get (K .barrierCap)).down
      let surplus := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .densityCap)
        ⟨by
          let object := inputs.current.object
          have spine : data.threshold * object.vertexCount ≤
              2 * object.edgeCount :=
            Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
              data.threshold fun vertex =>
                le_trans inputs.current.baseline
                  (object.minDegree_le_degree vertex)
          rcases cap with
            ⟨packing, _valid, packingCard, _maximal, capBound, _stable⟩
          change 2 * (data.windowRate *
              data.separatedScaleCount object.vertexCount *
              object.windowPackingNumber data.windowOrder) ≤
            (Graph.dyadicScaleCount object + 1) *
              (data.threshold * object.vertexCount +
                data.surplusThreshold object.vertexCount)
          apply Graph.two_mul_exponent_le_scale_mul_edgeBudget object
            (data.windowRate * data.separatedScaleCount object.vertexCount *
              object.windowPackingNumber data.windowOrder)
            data.threshold (data.surplusThreshold object.vertexCount)
          · simpa [packingCard] using capBound
          · exact spine
          · exact data.three_le_threshold
          · exact surplus⟩
        .nil)

/-- Node `[145]`: append the canonical hot/cold split. -/
@[reducible] noncomputable def coldWindowLedgerSplitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldWindowLedgerSplit
    { Requires := [K .hotColdPartition]
      Produces := [K .coldWindowLedgerSplit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldWindowLedgerSplit)
        ⟨(inputs.get (K .hotColdPartition)).down⟩
        .nil)

/-- Node `[150]`: derive the exact cleared cold-mass inequality. -/
@[reducible] noncomputable def coldMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMass
    { Requires := [K .coldWindowLedgerSplit, K .coldHotEntropyCap]
      Produces := [K .coldMass]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
      let hotBound := (inputs.get (K .coldHotEntropyCap)).down
      .cons (key := K .coldMass)
        ⟨by
          classical
          let packing := canonicalWindowPacking data inputs.current.object
          let hot := canonicalHotWindows data inputs.current.object
          let cold := canonicalColdWindows data inputs.current.object
          let _partition := split
          change coldWindowBitRate data inputs.current.object * hot.card ≤
            coldSkeletonAllowance data inputs.current.object at hotBound
          have count : packing.card = hot.card + cold.card := by
            simpa [packing, hot, cold, canonicalHotWindows,
              canonicalColdWindows] using
              ((canonicalWindowPacking data inputs.current.object).card_filter_add_card_filter_not
                (LiveHotWindow data inputs.current.object)).symm
          change ColdMassStatement data inputs.current.object
          simpa [ColdMassStatement] using
            Graph.ColdCorridor.hotFailure_coldMass
              (coldWindowBitRate data inputs.current.object) 0 0
              (coldSkeletonAllowance data inputs.current.object)
              hot.card cold.card packing.card count (by simpa using hotBound)⟩
        .nil)

/-- Node `[151]`: charge each non-ambient-cubic cold window injectively to a
positive-surplus vertex of the current object. -/
@[reducible] noncomputable def coldAmbientCubicRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldAmbientCubic
    { Requires := [K .coldWindowLedgerSplit, K .surplusAtOrBelow,
        K .selection]
      Produces := [K .coldAmbientCubic]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
      let nearCubic := (inputs.get (K .surplusAtOrBelow)).down
      let _selected := (inputs.get (K .selection)).down
      .cons (key := K .coldAmbientCubic)
        ⟨by
          classical
          rcases split with
            ⟨valid, _attains, _maximal, _hotIff, coldIff, _disjoint, _cover⟩
          have coldSubset : canonicalColdWindows data inputs.current.object ⊆
              canonicalWindowPacking data inputs.current.object := by
            intro window member
            exact (coldIff window).mp member |>.1
          change ColdAmbientCubicStatement data inputs.current.object
          refine ⟨?_, nearCubic⟩
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          letI : FinEnum object.Vertex := object.vertices
          letI : Fintype object.Vertex := inferInstance
          let ambient : Finset object.Vertex := Finset.univ.filter fun vertex =>
            data.threshold < object.degree vertex
          let bad : Finset (Finset object.Vertex) := cold.filter fun window =>
            ¬ AmbientCubicWindow data object window
          have baselineDegree : ∀ vertex : object.Vertex,
              data.threshold ≤ object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (object.minDegree_le_degree vertex)
          have existsHigh (window : {window // window ∈ bad}) :
              ∃ vertex ∈ window.1, data.threshold < object.degree vertex := by
            have notCubic := (Finset.mem_filter.mp window.property).2
            simp only [AmbientCubicWindow] at notCubic
            push Not at notCubic
            obtain ⟨vertex, member, different⟩ := notCubic
            have lower := baselineDegree vertex
            exact ⟨vertex, member, by omega⟩
          let chosen : {window // window ∈ bad} → {vertex // vertex ∈ ambient} :=
            fun window => ⟨Classical.choose (existsHigh window),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                (Classical.choose_spec (existsHigh window)).2⟩⟩
          have chosenMem (window : {window // window ∈ bad}) :
              (chosen window).1 ∈ window.1 :=
            (Classical.choose_spec (existsHigh window)).1
          have chosenInjective : Function.Injective chosen := by
            intro left right same
            apply Subtype.ext
            by_contra different
            have leftPacking : left.1 ∈ packing :=
              coldSubset (Finset.mem_filter.mp left.property).1
            have rightPacking : right.1 ∈ packing :=
              coldSubset (Finset.mem_filter.mp right.property).1
            have disjoint := valid.2 left.1 leftPacking right.1 rightPacking different
            have sameVertex : (chosen left).1 = (chosen right).1 :=
              congrArg Subtype.val same
            exact (Finset.disjoint_left.mp disjoint)
              (chosenMem left) (sameVertex.symm ▸ chosenMem right)
          have badCard : bad.card ≤ ambient.card := by
            simpa using Fintype.card_le_of_injective chosen chosenInjective
          have ambientCard : ambient.card ≤ object.degreeSurplus data.threshold := by
            calc
              ambient.card = ∑ _vertex ∈ ambient, 1 := by simp
              _ ≤ ∑ vertex ∈ ambient,
                    (object.degree vertex - data.threshold) := by
                exact Finset.sum_le_sum fun vertex member => by
                  have high := (Finset.mem_filter.mp member).2
                  omega
              _ ≤ ∑ vertex ∈ (Finset.univ : Finset object.Vertex),
                    (object.degree vertex - data.threshold) := by
                exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
              _ = object.degreeSurplus data.threshold := by
                simpa [Graph.FiniteObject.ambientSurplus] using
                  object.ambientSurplus_univ_eq_degreeSurplus
                    data.threshold baselineDegree
          have badBound : bad.card ≤ object.degreeSurplus data.threshold :=
            badCard.trans ambientCard
          have splitCard := cold.card_filter_add_card_filter_not
            (AmbientCubicWindow data object)
          change cold.card ≤
            (cold.filter (AmbientCubicWindow data object)).card +
              object.degreeSurplus data.threshold
          rw [← splitCard]
          convert Nat.add_le_add_left badBound
            (cold.filter (AmbientCubicWindow data object)).card using 1
          ⟩
        .nil)

/-- Node `[152]`: derive the branch-excess inequality from node `[151]`. -/
@[reducible] noncomputable def coldStubExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldStubExcess
    { Requires := [K .coldAmbientCubic]
      Produces := [K .coldStubExcess]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      .cons (key := K .coldStubExcess)
        ⟨by
          classical
          change ColdStubExcessStatement data inputs.current.object
          simpa [ColdStubExcessStatement, ColdAmbientCubicStatement] using
            Graph.ColdCorridor.branchExcess_ge_of_cubic
              (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data))
              ((canonicalColdWindows data inputs.current.object).filter
                (AmbientCubicWindow data inputs.current.object)).card
              (canonicalColdWindows data inputs.current.object).card
              (inputs.current.object.degreeSurplus data.threshold) cubic.1⟩
        .nil)

/-!
Node `[153]` must next read `K .coldStubExcess`, derive the selected
branch-excess half-edges and their first-failure bounded germs on
`inputs.current`, extract the disjoint family, and append that concrete fact.
There is deliberately no implication-only fallback.
-/

end Hypostructure.Graph.Strategy.Spine
