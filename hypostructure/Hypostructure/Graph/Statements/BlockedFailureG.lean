import Hypostructure.Graph.Statements.Spine

/-!
# Statements: G's own record and the aggregate failure of `lem:scale-additivity` (`[170]`, `[172a]`)

Node `[170]` tests, at each exposure coordinate, the aggregate inequality
`W_{a,b}·A_{k+1} ≤ F_{a,b}·A_k` (`BlockedAggregateBoundAt`), where `A_k = blockedReachedCount k`
is the class of a-priori graphs reached through the blocked records at the first `k` coordinates.
It is a numerical statement about G's class, determined by G's canonical packing, class and
coordinate order, and it is exactly the inequality the exposure product of
`lem:blocked-graphs-compress` consumes.  Its failure (`BlockedBarrierFailureStatement`) names no
record and no member.  The statements here are G's facts on that failure arm:

* `BlockedOwnRecordStatement`: G's own skeleton, as the member of `𝓑(𝒫)`, has a surviving
  barrier state at every coordinate and lies in both of its own conditional fibres;
* `BlockedFailureSlackStatement`: at the first failing coordinate, `A_{k+1} ≤ A_k`,
  `1 ≤ |𝓑(𝒫)| ≤ A_{k+1}` and `F_{a,b} < W_{a,b}`;
* `BlockedPrefixCompressionStatement`: the exposure counting run on the predecessors of any
  coordinate all of whose predecessors satisfy the aggregate test.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The product of the registered a-priori `W_{a,b}` carriers over the coordinates. -/
noncomputable def blockedAllAprioriCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate : blockedCoordinate data object, blockedAprioriCountAt data coordinate.2

/-- The product of the registered surviving `F_{a,b}` carriers over the coordinates. -/
noncomputable def blockedAllSurvivingCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate : blockedCoordinate data object, blockedSurvivingCountAt data coordinate.2

/-- The product of the registered a-priori `W_{a,b}` carriers over the coordinates whose aggregate test holds. -/
noncomputable def blockedPassingAprioriCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        BlockedAggregateBoundAt data object coordinate),
    blockedAprioriCountAt data coordinate.2

/-- The product of the registered surviving `F_{a,b}` carriers over the coordinates whose aggregate test holds. -/
noncomputable def blockedPassingSurvivingCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        BlockedAggregateBoundAt data object coordinate),
    blockedSurvivingCountAt data coordinate.2

/-- The product of the registered a-priori `W_{a,b}` carriers over the coordinates whose aggregate test fails. -/
noncomputable def blockedFailingAprioriCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        ¬ BlockedAggregateBoundAt data object coordinate),
    blockedAprioriCountAt data coordinate.2

/-- The product of the registered surviving `F_{a,b}` carriers over the coordinates whose aggregate test fails. -/
noncomputable def blockedFailingSurvivingCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact ∏ coordinate ∈ Finset.univ.filter
      (fun coordinate : blockedCoordinate data object =>
        ¬ BlockedAggregateBoundAt data object coordinate),
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

/-- **The aggregate failure, quantified.**  At the first failing coordinate `c` (rank `k`; all
earlier aggregate tests hold): the failing inequality `F_{a,b}·A_k < W_{a,b}·A_{k+1}`, the
monotonicity `A_{k+1} ≤ A_k`, the blocked class inside the reached class
`1 ≤ |𝓑(𝒫)| ≤ A_{k+1}`, and `F_{a,b} < W_{a,b}`. -/
def BlockedFailureSlackStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ coordinate : blockedCoordinate data object,
    (∀ other : blockedCoordinate data object,
      blockedEncodingRank data object other <
          blockedEncodingRank data object coordinate →
        BlockedAggregateBoundAt data object other) ∧
    blockedSurvivingCountAt data coordinate.2 *
        blockedReachedCount data object (blockedEncodingRank data object coordinate) <
      blockedAprioriCountAt data coordinate.2 *
        blockedReachedCount data object (blockedEncodingRank data object coordinate + 1) ∧
    blockedReachedCount data object (blockedEncodingRank data object coordinate + 1) ≤
      blockedReachedCount data object (blockedEncodingRank data object coordinate) ∧
    1 ≤ Nat.card (blockedClassAt data object) ∧
    Nat.card (blockedClassAt data object) ≤
      blockedReachedCount data object (blockedEncodingRank data object coordinate + 1) ∧
    blockedSurvivingCountAt data coordinate.2 < blockedAprioriCountAt data coordinate.2

/-- **The prefix compression of `𝓑(𝒫)`.**  At every coordinate all of whose predecessors
satisfy the aggregate test, the blocked class times the product of the predecessors' `W_{a,b}`
is at most the a-priori class times the product of their `F_{a,b}`. -/
def BlockedPrefixCompressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ coordinate : blockedCoordinate data object,
    (∀ other : blockedCoordinate data object,
      blockedEncodingRank data object other <
          blockedEncodingRank data object coordinate →
        BlockedAggregateBoundAt data object other) →
    Nat.card (blockedClassAt data object) *
        blockedPrefixAprioriCount data object
          (blockedEncodingRank data object coordinate) ≤
      Nat.card (blockedAprioriClassAt data object) *
        blockedPrefixSurvivingCount data object
          (blockedEncodingRank data object coordinate)

/-- **The failing set carries the overflow.**  Let `Φ` be the set of coordinates whose aggregate
test fails.  The exposure counting with the failing coordinates removed (a failing step is
only `A_{k+1} ≤ A_k`) and the certified package rate `2^{bits·p}·∏F ≤ ∏W` give
`|𝓑(𝒫)|·2^{bits·p}·∏_Φ F ≤ |𝒢_{n,m}|·∏_Φ W`: the whole package saving over the class
bound is carried by the coordinates of `Φ`. -/
def BlockedFailingSetCarriesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Nat.card (blockedClassAt data object) *
      2 ^ (windowPackageBits data object * (canonicalWindowPacking data object).card) *
      blockedFailingSurvivingCount data object ≤
    Nat.card (blockedAprioriClassAt data object) *
      blockedFailingAprioriCount data object

end Hypostructure.Graph.Strategy.Spine
