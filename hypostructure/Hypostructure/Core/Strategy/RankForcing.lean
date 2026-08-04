import Hypostructure.Core.OrderThresholdSplit
import Hypostructure.Core.Strategy.Data

/-!
# Reusable rank-forcing strategy

The node-level rank-drop/full-rank decisions are the same strategy in Graph
and PDE proofs. This module exposes that decision without importing an
application node or baking in a domain quantity.
-/

namespace Hypostructure.Core.Strategy

universe uAmbient uBranch uData

open Hypostructure.Core

structure RankForcingData
    (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P) where
  profile : ProblemInput P -> Core.OrderThresholdSplit.Profile Nat
  closeRankDrop : Option (PLift (forall input : ProblemInput P,
    PLift ((profile input).threshold < (profile input).value) ->
      T.Predicate input.object)) := none
  closeFullRank : Option (PLift (forall input : ProblemInput P,
    PLift ((profile input).value ≤ (profile input).threshold) ->
      T.Predicate input.object)) := none
  metadata : Documentation := {}
  rankDropMetadata : Documentation := {}
  fullRankMetadata : Documentation := {}

noncomputable def RankForcingData.toDichotomy
  (data : RankForcingData P T) :
    Core.DichotomyData P T where
  LeftPayload := fun input =>
    PLift ((data.profile input).threshold < (data.profile input).value)
  RightPayload := fun input =>
    PLift ((data.profile input).value ≤ (data.profile input).threshold)
  classify := fun input => by
    letI : Decidable ((data.profile input).threshold <
        (data.profile input).value) := Classical.propDecidable _
    if h : (data.profile input).threshold < (data.profile input).value then
      exact Sum.inl ⟨h⟩
    else
      exact Sum.inr ⟨le_of_not_gt h⟩
  closeLeft := data.closeRankDrop
  closeRight := data.closeFullRank
  metadata := data.metadata
  leftMetadata := data.rankDropMetadata
  rightMetadata := data.fullRankMetadata

theorem RankForcingData.exhaustive
    (data : RankForcingData P T) (input : ProblemInput P) :
    (data.profile input).threshold < (data.profile input).value ∨
      (data.profile input).value ≤ (data.profile input).threshold :=
  lt_or_ge _ _

end Hypostructure.Core.Strategy
