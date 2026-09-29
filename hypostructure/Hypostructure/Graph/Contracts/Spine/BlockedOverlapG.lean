import Hypostructure.Graph.Statements.BlockedOverlapG

/-!
# Contracts: G's overlap support

Proof-agnostic contract lemma for `Statements/BlockedOverlapG.lean`.  Hypotheses are the
presentation law (accepted lengths are the dyadic ones) and `K .blockedClassMember`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **G's overlap support** (`BlockedOverlapSupportStatement`). -/
theorem blockedOverlapSupport_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (blocked : BlockedClassMemberStatement data object) :
    BlockedOverlapSupportStatement data object := by
  classical
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := blocked
  let own : blockedClassAt data object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember object, minDegree⟩, isBlocked⟩
  have walkLength : ∀ (coordinate : blockedCoordinate data object)
      (support : BlockedCompletionSupport data object own coordinate),
      (blockedSupportWalk data object own coordinate support).length =
        2 ^ coordinate.1.2.1 := by
    intro coordinate support
    unfold blockedSupportWalk
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      support.firstArm_length, support.secondArm_length]
    exact support.completion_length
  have throughWindow : ∀ (coordinate : blockedCoordinate data object)
      (support : BlockedCompletionSupport data object own coordinate),
      ∃ vertex ∈ (blockedSupportWalk data object own coordinate support).support,
        vertex ∈ coordinate.1.1.1 := by
    intro coordinate support
    obtain ⟨vertex, vertexMem, vertexWindow⟩ := support.completionThroughWindow
    refine ⟨vertex, ?_, vertexWindow⟩
    unfold blockedSupportWalk
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr vertexMem
  have nonCycle : ∀ (coordinate : blockedCoordinate data object)
      (support : BlockedCompletionSupport data object own coordinate),
      ¬ (blockedSupportWalk data object own coordinate support).IsCycle := by
    intro coordinate support cycle
    obtain ⟨vertex, vertexMem, vertexWindow⟩ := throughWindow coordinate support
    have rotated := cycle.rotate vertexMem
    have lengthEq : ((blockedSupportWalk data object own coordinate support).rotate
        vertex vertexMem).length = 2 ^ coordinate.1.2.1 := by
      rw [SimpleGraph.Walk.length_rotate]
      exact walkLength coordinate support
    have three := rotated.three_le_length
    rw [lengthEq] at three
    have exponent : 2 ≤ coordinate.1.2.1 := by
      by_contra small
      have : coordinate.1.2.1 ≤ 1 := by omega
      have : 2 ^ coordinate.1.2.1 ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have accepted : data.LengthOK
        ((blockedSupportWalk data object own coordinate support).rotate vertex vertexMem).length := by
      rw [lengthEq]
      refine (lengthOK_iff_powerOfTwo _).2 ⟨⟨coordinate.1.2.1, ?_⟩, exponent, rfl⟩
      exact Nat.lt_succ_of_lt (Nat.lt_two_pow_self)
    exact isBlocked.blocked coordinate.1.1.1 coordinate.1.1.2
      ⟨vertex, vertexWindow, _, rotated, accepted⟩
  have supportConnected : ∀ (coordinate : blockedCoordinate data object)
      (u v : Fin object.vertexCount),
      u ∈ blockedSupportVertices data object own coordinate →
      v ∈ blockedSupportVertices data object own coordinate →
      own.1.1.1.graph.Reachable u v := by
    intro coordinate u v hu hv
    by_cases present : Nonempty (BlockedCompletionSupport data object own coordinate)
    · unfold blockedSupportVertices at hu hv
      rw [dif_pos present] at hu hv
      have uMem := List.mem_toFinset.1 hu
      have vMem := List.mem_toFinset.1 hv
      have reachU : own.1.1.1.graph.Reachable present.some.source u :=
        ⟨(blockedSupportWalk data object own coordinate present.some).takeUntil u uMem⟩
      have reachV : own.1.1.1.graph.Reachable present.some.source v :=
        ⟨(blockedSupportWalk data object own coordinate present.some).takeUntil v vMem⟩
      exact reachU.symm.trans reachV
    · unfold blockedSupportVertices at hu
      rw [dif_neg present] at hu
      exact absurd hu (Finset.notMem_empty _)
  have adjSymm : ∀ left right : blockedCoordinate data object,
      blockedOverlapAdj data object own left right →
        blockedOverlapAdj data object own right left := by
    intro left right ⟨sameScale, sameRow, differ, nonempty⟩
    refine ⟨sameScale.symm, sameRow.symm, differ.symm, ?_⟩
    rwa [Finset.inter_comm, Finset.union_comm]
  have reachSymm : ∀ first last : blockedCoordinate data object,
      Relation.ReflTransGen (blockedOverlapAdj data object own) first last →
        Relation.ReflTransGen (blockedOverlapAdj data object own) last first := by
    intro first last reach
    induction reach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.head (adjSymm _ _ step) ih
  have chain : ∀ first last : blockedCoordinate data object,
      Relation.ReflTransGen (blockedOverlapAdj data object own) first last →
      ∀ u ∈ blockedSupportVertices data object own first,
      ∀ v ∈ blockedSupportVertices data object own last,
      own.1.1.1.graph.Reachable u v := by
    intro first last reach
    induction reach with
    | refl => intro u hu v hv; exact supportConnected _ u v hu hv
    | tail _ step ih =>
        intro u hu v hv
        obtain ⟨_, _, _, shared, sharedMem⟩ := step
        obtain ⟨inBoth, _⟩ := Finset.mem_sdiff.1 sharedMem
        obtain ⟨inMiddle, inLast⟩ := Finset.mem_inter.1 inBoth
        exact (ih u hu shared inMiddle).trans (supportConnected _ shared v inLast hv)
  refine ⟨own, rfl, ?_, ?_, ?_⟩
  · intro coordinate
    by_cases present : Nonempty (BlockedCompletionSupport data object own coordinate)
    · unfold blockedSupportVertices
      rw [dif_pos present]
      calc (blockedSupportWalk data object own coordinate present.some).support.toFinset.card
          ≤ (blockedSupportWalk data object own coordinate present.some).support.length :=
            List.toFinset_card_le _
        _ = 2 ^ coordinate.1.2.1 + 1 := by
            rw [SimpleGraph.Walk.length_support, walkLength]
    · unfold blockedSupportVertices
      rw [dif_neg present]
      simp
  · intro coordinate nonempty
    by_cases present : Nonempty (BlockedCompletionSupport data object own coordinate)
    · refine ⟨_, blockedSupportWalk data object own coordinate present.some,
        walkLength coordinate present.some, nonCycle coordinate present.some, ?_,
        throughWindow coordinate present.some⟩
      unfold blockedSupportVertices
      rw [dif_pos present]
    · exfalso
      obtain ⟨vertex, vertexMem⟩ := nonempty
      unfold blockedSupportVertices at vertexMem
      rw [dif_neg present] at vertexMem
      exact Finset.notMem_empty _ vertexMem
  · intro coordinate u v ⟨first, firstReach, hu⟩ ⟨last, lastReach, hv⟩
    exact chain first last
      ((reachSymm _ _ firstReach).trans lastReach) u hu v hv

end Hypostructure.Graph.Contracts.Spine
