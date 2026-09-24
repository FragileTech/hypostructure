import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
# Absent completions do not produce an overlap obstruction

These regression examples use the actual barrier code and conditional graph
fibres. They are diagnostic evidence, not a closure of the selected residual.
No production row imports this file.

At a scale below the sum of the positive arm lengths, every completion support
is absent. The code records `none`, which survives. Thus the surviving and
a-priori fibres coincide, and every strictly improving F/W bound fails on a
nonempty blocked fibre. In the current code the first scale is 2^0 = 1;
the registered barrier pairs have two positive lengths.

Deleting that bounded scale would not repair the general implication: a fibre
can also have only a few surviving state VALUES with unequal graph
multiplicities. The last example records that separate obstruction, with both
a-priori values actually realized and with no absent-completion state.
-/

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

-- Check the actual code, without a surrogate state model.
example {n order left right scale : Nat} (H : Graph.LabelledOn n)
    (interiors window : Finset (Fin n)) (tooShort : scale < left + right) :
    Graph.BarrierSystem.barrierState order H interiors left right scale window = none := by
  classical
  have absent : ¬ Nonempty
      (Graph.BarrierSystem.CompletionSupport order H interiors window left right scale) := by
    rintro ⟨support⟩
    have length := support.completion_length
    omega
  simp [Graph.BarrierSystem.barrierState, absent]

example (data : Data) (object : Graph.FiniteObject)
    (coordinate : blockedCoordinate data object)
    (member₀ : blockedClassAt data object)
    (tooShort : 2 ^ coordinate.1.2.val <
      data.windowBarrier.table.counts.leftLength coordinate.2 +
        data.windowBarrier.table.counts.rightLength coordinate.2)
    (strictSaving : blockedSurvivingCountAt data coordinate.2 <
      blockedAprioriCountAt data coordinate.2) :
    ¬ BlockedRelativeFibreBoundAt data object coordinate := by
  classical
  have allNone : ∀ member : blockedAprioriClassAt data object,
      (blockedAprioriBarrierCode data object member).2 coordinate = none := by
    intro member
    change Graph.BarrierSystem.barrierState data.windowOrder member.1.1
      ((blockedWindowLabels data object).biUnion id)
      (barrierLegs data coordinate.2).1 (barrierLegs data coordinate.2).2
      (2 ^ coordinate.1.2.val) coordinate.1.1 = none
    have absent : ¬ Nonempty (Graph.BarrierSystem.CompletionSupport
        data.windowOrder member.1.1 ((blockedWindowLabels data object).biUnion id)
        coordinate.1.1 (barrierLegs data coordinate.2).1
        (barrierLegs data coordinate.2).2 (2 ^ coordinate.1.2.val)) := by
      rintro ⟨support⟩
      have length := support.completion_length
      simp only [barrierLegs] at length
      omega
    simp [Graph.BarrierSystem.barrierState, absent]
  have equalFibres : BlockedSurvivingConditionalFibre data object member₀ coordinate =
      BlockedAprioriConditionalFibre data object member₀ coordinate := by
    ext member
    simp [BlockedSurvivingConditionalFibre, allNone, IsBlockedSurvivingState]
  have inhabited : Nonempty (BlockedAprioriConditionalFibre data object member₀ coordinate) :=
    ⟨⟨member₀.1, rfl, fun _ _ => rfl⟩⟩
  letI := inhabited
  have positive : 0 < Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) :=
    Nat.card_pos
  intro relative
  have bound := relative member₀
  rw [equalFibres] at bound
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right strictSaving positive)) bound

-- Both label values occur, exactly one survives, but two of three graphs
-- have that value. State-count ratio 1/2 does not imply graph-count ratio 1/2.
example :
    let state : Fin 3 → Bool := fun graph => graph.val < 2
    let survivors := Finset.univ.filter fun graph => state graph = true
    (Finset.univ.image state).card = 2 ∧
      (survivors.image state).card = 1 ∧
      1 * (Finset.univ : Finset (Fin 3)).card < 2 * survivors.card := by
  decide
