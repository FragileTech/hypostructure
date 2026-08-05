import Hypostructure.Graph.SkeletonBudget

/-!
# The cubic baseline budget and the room above it

`def:baseline-spine-demand` fixes the common baseline the later surplus
accounting is measured against:

  `N = C(n,2)`,  `m₀ = ⌈(3/2)n⌉`,  `B₀(n) = log₂ C(N, m₀)`,

and `lem:incremental-skeleton-room` bounds the room a larger edge count buys:

  `log₂ C(N,m) − log₂ C(N,m₀) ≤ s·log₂ n`  for `m = m₀ + s ≤ 2n − 2`.

Both are stated here in exact `Nat` arithmetic, with the logarithms cleared: the
second display is `C(N, m₀+s) ≤ C(N, m₀) · n^s`, which is the same inequality
before taking `log₂` of either side, and it is proved from the one-step identity
`C(N,k+1)·(k+1) = C(N,k)·(N−k)` alone.  `B₀(n)` is the budget itself,
`cubicBaselineBudget`, and a consumer that wants its logarithm takes it with the
framework's own dyadic scale count rather than with a real-valued `log₂`.

`m₀ = ⌈(3/2)n⌉` is `⌈δn/2⌉` at the registered baseline `δ`: the least edge count
a `δ`-regular object on `n` vertices can carry.  The baseline is a parameter and
no numeral occurs.
-/

namespace Hypostructure.Graph

universe v

/-- **`m₀`**: the cubic baseline edge count `⌈δn/2⌉` at the registered
baseline. -/
def cubicBaselineEdgeCount (vertexCount baselineDegree : Nat) : Nat :=
  (baselineDegree * vertexCount + 1) / 2

/-- **`C(N, m₀)`**, whose logarithm is the manuscript's `B₀(n)`: the labelled
skeleton stratum at the cubic baseline edge count. -/
def cubicBaselineBudget (vertexCount baselineDegree : Nat) : Nat :=
  edgeStratumCount vertexCount (cubicBaselineEdgeCount vertexCount baselineDegree)

/-- The cubic baseline edge count is at least the vertex count, because the
registered baseline is at least `2`.  This is the only thing the incremental
room estimate needs of `m₀`, and it is what makes `N = C(n,2) ≤ n·m₀`. -/
theorem vertexCount_le_cubicBaselineEdgeCount (vertexCount : Nat)
    {baselineDegree : Nat} (baseline : 2 ≤ baselineDegree) :
    vertexCount ≤ cubicBaselineEdgeCount vertexCount baselineDegree := by
  have widened : 2 * vertexCount ≤ baselineDegree * vertexCount :=
    Nat.mul_le_mul_right vertexCount baseline
  unfold cubicBaselineEdgeCount
  omega

/-- `N = C(n,2) ≤ n · k` whenever `n ≤ k`: the pair count is at most `n²`. -/
theorem choose_two_le_mul (vertexCount bound : Nat)
    (large : vertexCount ≤ bound) :
    vertexCount.choose 2 ≤ vertexCount * bound := by
  have square : vertexCount.choose 2 ≤ vertexCount * vertexCount := by
    rw [Nat.choose_two_right]
    exact le_trans (Nat.div_le_self _ 2)
      (Nat.mul_le_mul_left vertexCount (Nat.sub_le _ _))
  exact square.trans (Nat.mul_le_mul_left vertexCount large)

/-- **One step of `lem:incremental-skeleton-room`.**

`C(N, k+1) ≤ n · C(N, k)` whenever `n ≤ k+1` and `N ≤ n·(k+1)`: the one-step
identity `C(N,k+1)·(k+1) = C(N,k)·(N−k)` bounds the ratio by `N/(k+1)`, and the
hypothesis bounds that by `n`. -/
theorem choose_succ_le_mul (pairCount vertexCount index : Nat)
    (room : pairCount ≤ vertexCount * (index + 1)) :
    pairCount.choose (index + 1) ≤ vertexCount * pairCount.choose index := by
  have identity : pairCount.choose (index + 1) * (index + 1) =
      pairCount.choose index * (pairCount - index) :=
    Nat.choose_succ_right_eq pairCount index
  have step : pairCount.choose (index + 1) * (index + 1) ≤
      (vertexCount * pairCount.choose index) * (index + 1) := by
    calc pairCount.choose (index + 1) * (index + 1)
        = pairCount.choose index * (pairCount - index) := identity
      _ ≤ pairCount.choose index * (vertexCount * (index + 1)) :=
          Nat.mul_le_mul_left _ (le_trans (Nat.sub_le _ _) room)
      _ = (vertexCount * pairCount.choose index) * (index + 1) := by ring
  exact Nat.le_of_mul_le_mul_right step (Nat.succ_pos index)

/-- **`lem:incremental-skeleton-room`**, with the logarithms cleared:

  `C(N, m₀ + s) ≤ C(N, m₀) · n^s`.

Taking `log₂` of both sides is the manuscript's
`log₂ C(N,m) − log₂ C(N,m₀) ≤ s log₂ n`.  The proof is `s` applications of the
one-step ratio bound, each of which needs only `N ≤ n·(k+1)` — which holds
because `m₀ ≥ n` and `N = C(n,2) ≤ n²`. -/
theorem incremental_skeleton_room (vertexCount : Nat) {baselineDegree : Nat}
    (baseline : 2 ≤ baselineDegree) (increment : Nat) :
    (vertexCount.choose 2).choose
        (cubicBaselineEdgeCount vertexCount baselineDegree + increment) ≤
      (vertexCount.choose 2).choose
          (cubicBaselineEdgeCount vertexCount baselineDegree) *
        vertexCount ^ increment := by
  induction increment with
  | zero => simp
  | succ predecessor hypothesis =>
      have large : vertexCount ≤
          cubicBaselineEdgeCount vertexCount baselineDegree + predecessor + 1 :=
        le_trans (vertexCount_le_cubicBaselineEdgeCount vertexCount baseline)
          (by omega)
      have room : vertexCount.choose 2 ≤
          vertexCount *
            (cubicBaselineEdgeCount vertexCount baselineDegree + predecessor
              + 1) :=
        choose_two_le_mul vertexCount _ large
      calc (vertexCount.choose 2).choose
              (cubicBaselineEdgeCount vertexCount baselineDegree +
                (predecessor + 1))
          = (vertexCount.choose 2).choose
              ((cubicBaselineEdgeCount vertexCount baselineDegree +
                predecessor) + 1) := by
                rw [Nat.add_assoc]
        _ ≤ vertexCount *
              (vertexCount.choose 2).choose
                (cubicBaselineEdgeCount vertexCount baselineDegree +
                  predecessor) :=
            choose_succ_le_mul _ _ _ room
        _ ≤ vertexCount *
              ((vertexCount.choose 2).choose
                  (cubicBaselineEdgeCount vertexCount baselineDegree) *
                vertexCount ^ predecessor) :=
            Nat.mul_le_mul_left _ hypothesis
        _ = (vertexCount.choose 2).choose
              (cubicBaselineEdgeCount vertexCount baselineDegree) *
            vertexCount ^ (predecessor + 1) := by ring

/-- **The room the object's own edge count buys over the cubic baseline.**

An object whose edge count sits at `m₀ + s` carries a labelled skeleton budget
within a factor `n^s` of the cubic baseline budget.  This is
`lem:incremental-skeleton-room` at the object, which is how
`def:baseline-spine-demand` fixes a *common* baseline for a branch whose edge
count is above the cubic one. -/
theorem skeletonBudget_le_cubicBaselineBudget_mul_pow
    (object : Graph.FiniteObject.{v}) {baselineDegree : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount) :
    skeletonBudget object ≤
      cubicBaselineBudget object.vertexCount baselineDegree *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) := by
  have restore : cubicBaselineEdgeCount object.vertexCount baselineDegree +
      (object.edgeCount -
        cubicBaselineEdgeCount object.vertexCount baselineDegree) =
      object.edgeCount := by omega
  have room := incremental_skeleton_room (baselineDegree := baselineDegree)
    object.vertexCount baseline
    (object.edgeCount -
      cubicBaselineEdgeCount object.vertexCount baselineDegree)
  rw [restore] at room
  exact room

end Hypostructure.Graph
