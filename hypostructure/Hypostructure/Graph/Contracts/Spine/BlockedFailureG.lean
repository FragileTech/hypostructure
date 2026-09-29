import Hypostructure.Graph.Statements.BlockedFailureG
import Hypostructure.Graph.Contracts.Spine.BlockedCompression
import Hypostructure.Graph.Contracts.Spine.BlockedExposure

/-!
# Contracts: G's own record and the prefix compression at the first failing coordinate of `[170]`

Proof-agnostic contract lemmas for `Statements/BlockedFailureG.lean`.  Hypotheses are the
presentation laws of the registered presentation (the dyadic target and the rejected degenerate
closure), read from `K .cubicBaseline`.  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **G's own record** (`BlockedOwnRecordStatement`): G's own skeleton, the member of `𝓑(𝒫)`
given by `K .blockedClassMember`, has a surviving barrier state at every coordinate and lies in
both of its own conditional fibres. -/
theorem blockedOwnRecord_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (degenerateClosureRejected : ¬ data.LengthOK 2)
    (windowBarrierLabel : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (windowBarrierLabel_mem : ∀ index,
      windowBarrierLabel index ∈ Graph.WindowCurvature.Labels data.windowOrder)
    (windowBarrierLabel_injective : Function.Injective windowBarrierLabel)
    (windowBarrierLabel_surjective : ∀ label ∈
        Graph.WindowCurvature.Labels data.windowOrder,
      ∃ index, windowBarrierLabel index = label)
    (windowBarrier_left_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_right_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (windowBarrier_sum_semantic : ∀ row source target,
      (data.windowBarrier.profile.row
        (data.windowBarrier.table.counts.leftLength row +
          data.windowBarrier.table.counts.rightLength row) source).getLsb target =
        decide (Graph.WindowCurvature.Safe
          (data.windowBarrier.table.counts.leftLength row +
            data.windowBarrier.table.counts.rightLength row)
          (windowBarrierLabel source) (windowBarrierLabel target)))
    (blocked : BlockedClassMemberStatement data object) :
    BlockedOwnRecordStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  let own : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  have survives := blockedStateSurvives data object lengthOK_iff_powerOfTwo
    degenerateClosureRejected
  have monotone := blockedGraphFibreMonotone data object
  have stateFibre := blockedStateFibreBound data object lengthOK_iff_powerOfTwo
    degenerateClosureRejected windowBarrierLabel windowBarrierLabel_mem
    windowBarrierLabel_injective windowBarrierLabel_surjective windowBarrier_left_semantic
    windowBarrier_right_semantic windowBarrier_sum_semantic
  refine ⟨own, rfl, fun coordinate ↦ survives own coordinate,
    fun coordinate ↦ ⟨?_, ?_⟩, fun coordinate ↦ stateFibre coordinate own⟩
  · have member : own.1 ∈ BlockedSurvivingConditionalFibre data object own coordinate :=
      ⟨⟨rfl, fun _ _ ↦ rfl⟩, survives own coordinate⟩
    have nonempty : Nonempty
        (BlockedSurvivingConditionalFibre data object own coordinate) := ⟨⟨own.1, member⟩⟩
    have finite : Finite (BlockedSurvivingConditionalFibre data object own coordinate) :=
      inferInstance
    exact Nat.succ_le_of_lt (Nat.card_pos (α :=
      BlockedSurvivingConditionalFibre data object own coordinate))
  · exact monotone coordinate own

/-- The reached classes shrink with the prefix. -/
theorem blockedReachedCount_mono (data : Parameters) (object : Graph.FiniteObject.{u})
    {j k : Nat} (jk : j ≤ k) :
    blockedReachedCount data object k ≤ blockedReachedCount data object j := by
  classical
  unfold blockedReachedCount
  refine Nat.card_le_card_of_injective
    (fun candidate ↦ (⟨candidate.1, ?_⟩ : {candidate : blockedAprioriClassAt data object //
      ∃ member : blockedClassAt data object,
        (blockedAprioriBarrierCode data object candidate).1 =
            (blockedBarrierCode data object member).1 ∧
          ∀ other : blockedCoordinate data object,
            blockedEncodingRank data object other < j →
              (blockedAprioriBarrierCode data object candidate).2 other =
                (blockedBarrierCode data object member).2 other})) ?_
  · obtain ⟨member, outsideEq, agree⟩ := candidate.2
    exact ⟨member, outsideEq, fun other lower ↦ agree other (lt_of_lt_of_le lower jk)⟩
  · intro left right equal
    have same := congrArg Subtype.val equal
    exact Subtype.ext same

/-- The blocked class lies inside every reached class. -/
theorem blockedClass_le_reachedCount (data : Parameters) (object : Graph.FiniteObject.{u})
    (k : Nat) :
    Nat.card (blockedClassAt data object) ≤ blockedReachedCount data object k := by
  classical
  unfold blockedReachedCount
  refine Nat.card_le_card_of_injective
    (fun member : blockedClassAt data object ↦
      (⟨member.1, member, rfl, fun _ _ ↦ rfl⟩ : {candidate : blockedAprioriClassAt data object //
        ∃ member : blockedClassAt data object,
          (blockedAprioriBarrierCode data object candidate).1 =
              (blockedBarrierCode data object member).1 ∧
            ∀ other : blockedCoordinate data object,
              blockedEncodingRank data object other < k →
                (blockedAprioriBarrierCode data object candidate).2 other =
                  (blockedBarrierCode data object member).2 other})) ?_
  intro left right equal
  have same := congrArg Subtype.val equal
  exact Subtype.ext same

/-- **The aggregate failure, quantified** (`BlockedFailureSlackStatement`). -/
theorem blockedFailureSlack_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (blocked : BlockedClassMemberStatement data object)
    (failure : BlockedBarrierFailureStatement data object) :
    BlockedFailureSlackStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  obtain ⟨coordinate, earlier, strict⟩ := failure
  let own : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  haveI : Nonempty (blockedClassAt data object) := ⟨own⟩
  have positive : 1 ≤ Nat.card (blockedClassAt data object) :=
    Nat.succ_le_of_lt (Nat.card_pos (α := blockedClassAt data object))
  have monotone := blockedReachedCount_mono data object
    (Nat.le_succ (blockedEncodingRank data object coordinate))
  refine ⟨coordinate, earlier, strict, monotone, positive,
    blockedClass_le_reachedCount data object _, ?_⟩
  by_contra notLess
  have le : blockedAprioriCountAt data coordinate.2 ≤
      blockedSurvivingCountAt data coordinate.2 := Nat.le_of_not_lt notLess
  exact Nat.lt_irrefl _ (strict.trans_le
    ((Nat.mul_le_mul_right _ le).trans (Nat.mul_le_mul_left _ monotone)))

/-- **The prefix compression** (`BlockedPrefixCompressionStatement`): the exposure counting
on the predecessors of a coordinate, from their aggregate tests. -/
theorem blockedPrefixCompression_holds (data : Parameters) (object : Graph.FiniteObject.{u}) :
    BlockedPrefixCompressionStatement data object := fun coordinate aggregate ↦
  blockedExposureUpTo data object (blockedEncodingRank data object coordinate)
    (blockedRank_lt_card data object coordinate).le
    (fun other lower ↦ aggregate other lower)

end Hypostructure.Graph.Contracts.Spine
