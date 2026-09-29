import Hypostructure.Graph.Statements.Spine

/-!
# Statements: G's own record at the failure of `lem:scale-additivity` (`[170]`, `[172a]`)

`Statements/Spine.lean`'s `BlockedBarrierFailureStatement` retains a failing coordinate and a
blocked member `member₀` whose outside record and prefix fix the two graph fibres.  The
blocked class `𝓑(𝒫)` is built from G's canonical packing, and G's own skeleton is a member of
it (`BlockedClassMemberStatement`); the manuscript's remaining obligation is the transfer from
that comparison record to G.  The statements here are G's own facts at the same coordinates:

* `BlockedOwnRecordStatement`: G's own skeleton, as the member of `𝓑(𝒫)`, has a surviving
  barrier state at every coordinate, and lies in its own conditional fibres, so both of its
  fibres are nonempty, at every coordinate;
* `BlockedFailureSlackStatement`: at the retained first failing coordinate the strict reverse
  inequality forces a nonempty surviving fibre inside the a-priori fibre and `F_{a,b} < W_{a,b}`;
* `BlockedDominantStateStatement`: at a failed coordinate one surviving barrier state carries a
  fixed fraction of the a-priori fibre;
* `BlockedRecordTransferStatement`: the transfer from a comparison record to G: whenever a
  blocked record agrees with G's own outside record and prefix before a coordinate, both of its
  conditional fibres at that coordinate are G's own;
* `BlockedPrefixCompressionStatement`: the exposure counting of `lem:blocked-graphs-compress`
  run on the predecessors of any coordinate whose predecessors all satisfy the cleared bound:
  the blocked class is already compressed by the predecessors alone.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The product of the registered a-priori carriers `W_{a,b}` over the coordinates of encoding
rank below `r`. -/
noncomputable def blockedPrefixAprioriCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) (r : Nat) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        blockedEncodingRank data object coordinate < r),
    blockedAprioriCountAt data coordinate.2

/-- The product of the registered surviving carriers `F_{a,b}` over the coordinates of
encoding rank below `r`. -/
noncomputable def blockedPrefixSurvivingCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) (r : Nat) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        blockedEncodingRank data object coordinate < r),
    blockedSurvivingCountAt data coordinate.2

/-- **G's own record at the barrier states.**  G's own skeleton is the member `own` of `𝓑(𝒫)`;
its barrier state is surviving at every coordinate, and G lies in its own a-priori and
surviving conditional fibres, so at every coordinate `1 ≤ |S| ≤ |A|` at G's own outside record
and prefix. -/
def BlockedOwnRecordStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ own : blockedClassAt data object,
    own.1.1 = Graph.BlockedClass.objectSkeletonMember object ∧
    (∀ coordinate : blockedCoordinate data object,
      IsBlockedSurvivingState data coordinate.2
        ((blockedBarrierCode data object own).2 coordinate)) ∧
    ∀ coordinate : blockedCoordinate data object,
      1 ≤ Nat.card (BlockedSurvivingConditionalFibre data object own coordinate) ∧
        Nat.card (BlockedSurvivingConditionalFibre data object own coordinate) ≤
          Nat.card (BlockedAprioriConditionalFibre data object own coordinate)

/-- **The strict failure, quantified.**  At the first failing coordinate of `[170]` (all
earlier coordinates satisfy the cleared bound at every record), the reverse strict inequality
at some blocked record forces `0 < |S| ≤ |A|` and `F_{a,b} < W_{a,b}` at that coordinate's
barrier row. -/
def BlockedFailureSlackStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ coordinate : blockedCoordinate data object,
    (∀ other : blockedCoordinate data object,
      blockedEncodingRank data object other <
          blockedEncodingRank data object coordinate →
        BlockedRelativeFibreBoundAt data object other) ∧
    ∃ member₀ : blockedClassAt data object,
      blockedSurvivingCountAt data coordinate.2 *
          Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) <
        blockedAprioriCountAt data coordinate.2 *
          Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ∧
      0 < Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ∧
      Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
        Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) ∧
      blockedSurvivingCountAt data coordinate.2 < blockedAprioriCountAt data coordinate.2

/-- **The prefix compression of `𝓑(𝒫)`.**  At every coordinate all of whose predecessors
satisfy the cleared `F_{a,b}/W_{a,b}` bound at every reached record, the blocked class times the
product of the predecessors' `W_{a,b}` is at most the a-priori class times the product of their
`F_{a,b}`. -/
def BlockedPrefixCompressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ coordinate : blockedCoordinate data object,
    (∀ other : blockedCoordinate data object,
      blockedEncodingRank data object other <
          blockedEncodingRank data object coordinate →
        BlockedRelativeFibreBoundAt data object other) →
    Nat.card (blockedClassAt data object) *
        blockedPrefixAprioriCount data object
          (blockedEncodingRank data object coordinate) ≤
      Nat.card (blockedAprioriClassAt data object) *
        blockedPrefixSurvivingCount data object
          (blockedEncodingRank data object coordinate)

/-- **The transfer from a comparison record to G.**  With `own` G's own skeleton as the member of
`𝓑(𝒫)`: whenever a blocked member `member₀` has G's outside record and G's barrier states
before a coordinate, its a-priori and surviving conditional fibres at that coordinate are G's
own, so the strict failure at `member₀` is the strict failure at G. -/
def BlockedRecordTransferStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ own : blockedClassAt data object,
    own.1.1 = Graph.BlockedClass.objectSkeletonMember object ∧
    ∀ (coordinate : blockedCoordinate data object) (member₀ : blockedClassAt data object),
      (blockedBarrierCode data object member₀).1 = (blockedBarrierCode data object own).1 →
      (∀ other : blockedCoordinate data object,
        blockedEncodingRank data object other <
            blockedEncodingRank data object coordinate →
          (blockedBarrierCode data object member₀).2 other =
            (blockedBarrierCode data object own).2 other) →
      BlockedAprioriConditionalFibre data object member₀ coordinate =
          BlockedAprioriConditionalFibre data object own coordinate ∧
        BlockedSurvivingConditionalFibre data object member₀ coordinate =
          BlockedSurvivingConditionalFibre data object own coordinate

/-- The graphs of the a-priori conditional fibre whose barrier state at the coordinate is the
given state. -/
def BlockedStateGraphFibre (data : Parameters) (object : Graph.FiniteObject.{u})
    (member₀ : blockedClassAt data object) (coordinate : blockedCoordinate data object)
    (state : Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder)) :
    Set (blockedAprioriClassAt data object) :=
  {member | member ∈ BlockedAprioriConditionalFibre data object member₀ coordinate ∧
    (blockedAprioriBarrierCode data object member).2 coordinate = state}

/-- **The dominant state at a failed coordinate.**  Wherever the cleared bound fails at a
blocked record, the graph fibre `S` of surviving graphs is covered by the at most `F_{a,b} + 1`
surviving states, so one surviving state `s` has `|S| ≤ (F_{a,b} + 1)·|A_s|` graphs in the
a-priori fibre, and then `F_{a,b}·|A| < W_{a,b}·(F_{a,b} + 1)·|A_s|`: a single barrier state
carries at least the fraction `F_{a,b}/(W_{a,b}(F_{a,b} + 1))` of the a-priori fibre. -/
def BlockedDominantStateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (coordinate : blockedCoordinate data object) (member₀ : blockedClassAt data object),
    blockedSurvivingCountAt data coordinate.2 *
        Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) <
      blockedAprioriCountAt data coordinate.2 *
        Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) →
    ∃ state, IsBlockedSurvivingState data coordinate.2 state ∧
      Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
        (blockedSurvivingCountAt data coordinate.2 + 1) *
          Nat.card (BlockedStateGraphFibre data object member₀ coordinate state) ∧
      blockedSurvivingCountAt data coordinate.2 *
          Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) <
        blockedAprioriCountAt data coordinate.2 *
          ((blockedSurvivingCountAt data coordinate.2 + 1) *
            Nat.card (BlockedStateGraphFibre data object member₀ coordinate state))

end Hypostructure.Graph.Strategy.Spine
