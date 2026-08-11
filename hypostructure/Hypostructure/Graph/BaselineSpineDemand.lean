import Hypostructure.Core.TargetRank
import Hypostructure.Graph.DeclaredCoordinateSignature
import Hypostructure.Graph.SkeletonBudget

/-!
# The baseline spine demand, its exact budget, and its deficit packages

`def:baseline-spine-demand` fixes the common baseline the later surplus
accounting is measured against:

  `N = C(n,2)`,  `m₀ = ⌈(3/2)n⌉`,  `B₀(n) = log₂ C(N, m₀)`,

and calls a family `ℐ_spine` of declared target coordinates a *baseline spine
demand with deficit `E_spine(n)`* when `ℐ_spine` is independently
target-testable and `|ℐ_spine| ≥ B₀(n) − E_spine(n)`.

`lem:exact-cubic-baseline-budget` evaluates the baseline, `B₀(n) = (3/2)n log₂ n
+ O(n)`, and `lem:incremental-skeleton-room` bounds the room a larger edge count
buys:

  `log₂ C(N,m) − log₂ C(N,m₀) ≤ s·log₂ n`  for `m = m₀ + s ≤ 2n − 2`.

`def:spine-lower-bound-deficits` records the three lower-bound packages the
near-cubic branch supplies — window-only, high-remainder-entropy, and
high-entropy with forced curvature — and states that each one's deficit is an
admissible `E_spine`.

Everything is stated here in exact `Nat` arithmetic with the logarithms cleared.
`lem:incremental-skeleton-room` becomes `C(N, m₀+s) ≤ C(N, m₀) · n^s`, which is
the same inequality before taking `log₂` of either side and is proved from the
one-step identity `C(N,k+1)·(k+1) = C(N,k)·(N−k)` alone.
`lem:exact-cubic-baseline-budget` becomes the two-sided power sandwich

  `(n−1)^{m₀} ≤ C(N,m₀) · (2(δ+1))^{m₀}`  and  `C(N,m₀) ≤ (2n)^{m₀}`,

whose logarithms are `m₀(log₂ n − log₂(2(δ+1))) ≤ B₀(n) ≤ m₀(log₂ n + 1)`; at
`m₀ = ⌈δn/2⌉` that is `B₀(n) = (δ/2)n log₂ n + O(n)`, the manuscript's display at
its own baseline.  `|ℐ_spine| ≥ B₀(n) − E_spine(n)` becomes
`C(N,m₀) ≤ 2^{|ℐ_spine| + E_spine(n)}`, and the deficit itself is the *output*
`cubicBaselineExponent − L` at a package's lower bound `L`.

`m₀ = ⌈(3/2)n⌉` is `⌈δn/2⌉` at the registered baseline `δ`: the least edge count
a `δ`-regular object on `n` vertices can carry.  The baseline, the package rates
and the entropy denominator are all parameters and no numeral of any
presentation occurs.
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

/-- Twice the cubic baseline edge count never exceeds `δn + 1`: the ceiling
`⌈δn/2⌉` is what `(δn+1)/2` computes. -/
theorem two_mul_cubicBaselineEdgeCount_le (vertexCount baselineDegree : Nat) :
    2 * cubicBaselineEdgeCount vertexCount baselineDegree ≤
      baselineDegree * vertexCount + 1 := by
  unfold cubicBaselineEdgeCount
  omega

/-- The number of edges above the cubic baseline is at most the degree
surplus.  This is the exact form of `s <= sigma/2 + 1` needed by the final
quadratic absorption (and is deliberately a slightly weaker integral bound). -/
theorem edgeSlack_le_degreeSurplus (object : FiniteObject.{v})
    (baselineDegree : Nat)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount) :
    object.edgeCount - cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.degreeSurplus baselineDegree := by
  have lower : baselineDegree * object.vertexCount ≤
      2 * cubicBaselineEdgeCount object.vertexCount baselineDegree := by
    unfold cubicBaselineEdgeCount
    omega
  unfold FiniteObject.degreeSurplus
  omega

/-- The handshake lower bound places the object at or above the cubic baseline
stratum. -/
theorem cubicBaselineEdgeCount_le_edgeCount_of_handshake
    (object : FiniteObject.{v}) (baselineDegree : Nat)
    (handshake : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount) :
    cubicBaselineEdgeCount object.vertexCount baselineDegree ≤ object.edgeCount := by
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

/-! ## `lem:exact-cubic-baseline-budget`

The manuscript evaluates the baseline in two directions.  Upward it uses the
binomial estimate `C(N,m) ≤ (eN/m)^m` and `eN/m₀ = Θ(n)`; downward it uses the
product estimate `C(N,k) = ∏_{i<k}(N−i)/(k−i) ≥ (N/k)^k` and `N/m₀ = Θ(n)`.
Both are recorded here with the logarithms cleared, so the `e` is Stirling's own
`⌈e⌉ = 3` (`Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`) and the
`Θ(n)` is an explicit factor in the registered baseline.  Nothing rounds and no
numeral of a presentation appears. -/

/-- **The upper binomial estimate, cleared of `e`.**

`C(N,k) ≤ base^k` whenever `3N ≤ k·base`.  This is `C(N,k) ≤ (eN/k)^k` with the
division cleared and `e` replaced by Stirling's `⌈e⌉`: `k! · C(N,k) ≤ N^k` is the
descending-factorial bound, and `k^k ≤ 3^k·k!` converts the `k!` into the `k^k`
the hypothesis compares against. -/
theorem choose_le_pow_of_three_mul_le (pairCount index base : Nat)
    (alphabet : 3 * pairCount ≤ index * base) :
    pairCount.choose index ≤ base ^ index := by
  rcases Nat.eq_zero_or_pos index with zero | positive
  · simp [zero]
  · have factorialBound :
        Nat.factorial index * pairCount.choose index ≤ pairCount ^ index := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    have stirling : index ^ index ≤ 3 ^ index * Nat.factorial index :=
      Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial index
    have chain :
        index ^ index * pairCount.choose index ≤
          index ^ index * base ^ index := by
      calc index ^ index * pairCount.choose index
          ≤ (3 ^ index * Nat.factorial index) * pairCount.choose index :=
            Nat.mul_le_mul stirling (le_refl _)
        _ = 3 ^ index * (Nat.factorial index * pairCount.choose index) := by
            ring
        _ ≤ 3 ^ index * pairCount ^ index :=
            Nat.mul_le_mul (le_refl _) factorialBound
        _ = (3 * pairCount) ^ index := by rw [Nat.mul_pow]
        _ ≤ (index * base) ^ index := Nat.pow_le_pow_left alphabet index
        _ = index ^ index * base ^ index := by rw [Nat.mul_pow]
    exact Nat.le_of_mul_le_mul_left chain (Nat.pow_pos positive)

/-- **The lower product estimate, cleared of division.**

`(N+1−k)^k ≤ k^k · C(N,k)`, which is the manuscript's
`C(N,k) = ∏_{i<k}(N−i)/(k−i) ≥ (N/k)^k` with the denominators cleared: the
descending factorial dominates `(N+1−k)^k` termwise, and `k! ≤ k^k`. -/
theorem pow_sub_le_pow_mul_choose (pairCount index : Nat) :
    (pairCount + 1 - index) ^ index ≤ index ^ index * pairCount.choose index := by
  calc (pairCount + 1 - index) ^ index
      ≤ pairCount.descFactorial index :=
        Nat.pow_sub_le_descFactorial pairCount index
    _ = Nat.factorial index * pairCount.choose index :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
    _ ≤ index ^ index * pairCount.choose index :=
        Nat.mul_le_mul (Nat.factorial_le_pow index) (le_refl _)

/-- **`lem:exact-cubic-baseline-budget`, upper half:** `C(N, m₀) ≤ (2n)^{m₀}`.

Taking `log₂`, this is `B₀(n) ≤ m₀·(log₂ n + 1) = (δ/2)n log₂ n + O(n)`, the
manuscript's upper bound at the registered baseline.  The alphabet comparison
`3N ≤ m₀·2n` is `m₀ ≥ n` (which is `2 ≤ δ`) against `2N = (n−1)n ≤ n²`. -/
theorem cubicBaselineBudget_le_pow (vertexCount : Nat) {baselineDegree : Nat}
    (baseline : 2 ≤ baselineDegree) :
    cubicBaselineBudget vertexCount baselineDegree ≤
      (2 * vertexCount) ^ cubicBaselineEdgeCount vertexCount baselineDegree := by
  refine choose_le_pow_of_three_mul_le _ _ _ ?_
  have large : vertexCount ≤ cubicBaselineEdgeCount vertexCount baselineDegree :=
    vertexCount_le_cubicBaselineEdgeCount vertexCount baseline
  have pairs : 2 * vertexCount.choose 2 = (vertexCount - 1) * vertexCount :=
    Core.FiniteEntropy.two_mul_choose_two vertexCount
  have doubled :
      2 * (3 * vertexCount.choose 2) ≤
        2 * (cubicBaselineEdgeCount vertexCount baselineDegree *
          (2 * vertexCount)) := by
    calc 2 * (3 * vertexCount.choose 2)
        = 3 * (2 * vertexCount.choose 2) := by ring
      _ = 3 * ((vertexCount - 1) * vertexCount) := by rw [pairs]
      _ ≤ 3 * (vertexCount * vertexCount) :=
          Nat.mul_le_mul (le_refl _)
            (Nat.mul_le_mul (Nat.sub_le _ _) (le_refl _))
      _ ≤ 4 * (vertexCount * vertexCount) :=
          Nat.mul_le_mul (by norm_num) (le_refl _)
      _ ≤ 4 * (cubicBaselineEdgeCount vertexCount baselineDegree *
            vertexCount) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul large (le_refl _))
      _ = 2 * (cubicBaselineEdgeCount vertexCount baselineDegree *
            (2 * vertexCount)) := by ring
  exact Nat.le_of_mul_le_mul_left doubled (by norm_num)

/-- **`lem:exact-cubic-baseline-budget`, lower half:**

  `(n−1)^{m₀} ≤ C(N, m₀) · (2(δ+1))^{m₀}`.

Taking `log₂`, this is `B₀(n) ≥ m₀·(log₂ n − log₂(2(δ+1))) = (δ/2)n log₂ n −
O(n)`, the manuscript's lower bound at the registered baseline.

The hypothesis is that the cubic baseline edge count leaves room in the pair
count, `2m₀ ≤ N`.  It is not decoration: below it the baseline stratum is empty
and `B₀(n)` has no lower bound at all, which is the sense in which the
manuscript's evaluation is an asymptotic statement.  It is the only hypothesis,
and it is a comparison of two observables of the object's own order. -/
theorem pow_pred_le_cubicBaselineBudget_mul (vertexCount : Nat)
    {baselineDegree : Nat}
    (room : 2 * cubicBaselineEdgeCount vertexCount baselineDegree ≤
      vertexCount.choose 2) :
    (vertexCount - 1) ^ cubicBaselineEdgeCount vertexCount baselineDegree ≤
      cubicBaselineBudget vertexCount baselineDegree *
        (2 * (baselineDegree + 1)) ^
          cubicBaselineEdgeCount vertexCount baselineDegree := by
  have edgesLe := two_mul_cubicBaselineEdgeCount_le vertexCount baselineDegree
  have pairsIdentity : 2 * vertexCount.choose 2 = (vertexCount - 1) * vertexCount :=
    Core.FiniteEntropy.two_mul_choose_two vertexCount
  rcases Nat.eq_zero_or_pos
      (cubicBaselineEdgeCount vertexCount baselineDegree) with zero | positive
  · simp [cubicBaselineBudget, edgeStratumCount, zero]
  -- Below the baseline the pair count is zero, so `room` forces the edge count
  -- down with it; the surviving case therefore has a vertex.
  have vertexPos : 0 < vertexCount := by
    rcases Nat.eq_zero_or_pos vertexCount with zeroVertices | pos
    · exfalso
      have empty : vertexCount.choose 2 = 0 := by simp [zeroVertices]
      omega
    · exact pos
  -- `(n−1)·m₀ ≤ 2(δ+1)·(N+1−m₀)`: the baseline edge count is at most
  -- `(δn+1)/2`, and `2m₀ ≤ N` keeps `N+1−m₀` above `N/2`.
  have key : (vertexCount - 1) *
        cubicBaselineEdgeCount vertexCount baselineDegree ≤
      2 * (baselineDegree + 1) *
        (vertexCount.choose 2 + 1 -
          cubicBaselineEdgeCount vertexCount baselineDegree) := by
    have widened :
        2 * ((vertexCount - 1) *
            cubicBaselineEdgeCount vertexCount baselineDegree) ≤
          (baselineDegree + 1) * (2 * vertexCount.choose 2) := by
      calc 2 * ((vertexCount - 1) *
              cubicBaselineEdgeCount vertexCount baselineDegree)
          = (vertexCount - 1) *
              (2 * cubicBaselineEdgeCount vertexCount baselineDegree) := by ring
        _ ≤ (vertexCount - 1) * (baselineDegree * vertexCount + 1) :=
            Nat.mul_le_mul (le_refl _) edgesLe
        _ ≤ (vertexCount - 1) * ((baselineDegree + 1) * vertexCount) := by
            refine Nat.mul_le_mul (le_refl _) ?_
            have expand : (baselineDegree + 1) * vertexCount =
                baselineDegree * vertexCount + vertexCount := by ring
            omega
        _ = (baselineDegree + 1) * ((vertexCount - 1) * vertexCount) := by ring
        _ = (baselineDegree + 1) * (2 * vertexCount.choose 2) := by
            rw [pairsIdentity]
    have spread :
        (baselineDegree + 1) * (2 * vertexCount.choose 2) ≤
          (baselineDegree + 1) *
            (2 * (2 * (vertexCount.choose 2 + 1 -
              cubicBaselineEdgeCount vertexCount baselineDegree))) :=
      Nat.mul_le_mul (le_refl _) (by omega)
    have folded :
        (baselineDegree + 1) *
            (2 * (2 * (vertexCount.choose 2 + 1 -
              cubicBaselineEdgeCount vertexCount baselineDegree))) =
          2 * (2 * (baselineDegree + 1) *
            (vertexCount.choose 2 + 1 -
              cubicBaselineEdgeCount vertexCount baselineDegree)) := by ring
    have combined := le_trans widened spread
    rw [folded] at combined
    exact Nat.le_of_mul_le_mul_left combined (by norm_num)
  have chain :
      (vertexCount - 1) ^ cubicBaselineEdgeCount vertexCount baselineDegree *
          cubicBaselineEdgeCount vertexCount baselineDegree ^
            cubicBaselineEdgeCount vertexCount baselineDegree ≤
        cubicBaselineBudget vertexCount baselineDegree *
            (2 * (baselineDegree + 1)) ^
              cubicBaselineEdgeCount vertexCount baselineDegree *
          cubicBaselineEdgeCount vertexCount baselineDegree ^
            cubicBaselineEdgeCount vertexCount baselineDegree := by
    calc (vertexCount - 1) ^ cubicBaselineEdgeCount vertexCount baselineDegree *
            cubicBaselineEdgeCount vertexCount baselineDegree ^
              cubicBaselineEdgeCount vertexCount baselineDegree
        = ((vertexCount - 1) *
            cubicBaselineEdgeCount vertexCount baselineDegree) ^
              cubicBaselineEdgeCount vertexCount baselineDegree := by
          rw [Nat.mul_pow]
      _ ≤ (2 * (baselineDegree + 1) *
            (vertexCount.choose 2 + 1 -
              cubicBaselineEdgeCount vertexCount baselineDegree)) ^
              cubicBaselineEdgeCount vertexCount baselineDegree :=
          Nat.pow_le_pow_left key _
      _ = (2 * (baselineDegree + 1)) ^
              cubicBaselineEdgeCount vertexCount baselineDegree *
            (vertexCount.choose 2 + 1 -
              cubicBaselineEdgeCount vertexCount baselineDegree) ^
              cubicBaselineEdgeCount vertexCount baselineDegree := by
          rw [Nat.mul_pow]
      _ ≤ (2 * (baselineDegree + 1)) ^
              cubicBaselineEdgeCount vertexCount baselineDegree *
            (cubicBaselineEdgeCount vertexCount baselineDegree ^
                cubicBaselineEdgeCount vertexCount baselineDegree *
              (vertexCount.choose 2).choose
                (cubicBaselineEdgeCount vertexCount baselineDegree)) :=
          Nat.mul_le_mul (le_refl _)
            (pow_sub_le_pow_mul_choose _ _)
      _ = cubicBaselineBudget vertexCount baselineDegree *
              (2 * (baselineDegree + 1)) ^
                cubicBaselineEdgeCount vertexCount baselineDegree *
            cubicBaselineEdgeCount vertexCount baselineDegree ^
              cubicBaselineEdgeCount vertexCount baselineDegree := by
          unfold cubicBaselineBudget edgeStratumCount
          ring
  exact Nat.le_of_mul_le_mul_right chain (Nat.pow_pos positive)

/-! ## The baseline in bits, and the deficit it leaves

`def:baseline-spine-demand` compares a coordinate count against `B₀(n)`, so the
branch needs the baseline as a *number of bits*, not as the stratum count.
`cubicBaselineExponent` is that number: the upper half of
`lem:exact-cubic-baseline-budget` read at the object's own dyadic scale count,
which is `Graph.dyadicScaleCount` at the object's order.  `spineDeficit` is the
manuscript's `E_spine(n) = B₀(n) − L` at a package's lower bound `L`, and it is
an *output* of this node rather than a hypothesis carried into it. -/

/-- **`B₀(n)` in bits.**  `m₀·(log₂ n + 2)`, the upper half of
`lem:exact-cubic-baseline-budget` with the base `2n` replaced by the dyadic
scale that dominates it.  At the registered cubic baseline this is
`(3/2)n log₂ n + O(n)`. -/
def cubicBaselineExponent (vertexCount baselineDegree : Nat) : Nat :=
  cubicBaselineEdgeCount vertexCount baselineDegree * (Nat.log2 vertexCount + 2)

/-- The baseline stratum fits in its own bit count. -/
theorem cubicBaselineBudget_le_two_pow (vertexCount : Nat)
    {baselineDegree : Nat} (baseline : 2 ≤ baselineDegree) :
    cubicBaselineBudget vertexCount baselineDegree ≤
      2 ^ cubicBaselineExponent vertexCount baselineDegree := by
  have base : 2 * vertexCount ≤ 2 ^ (Nat.log2 vertexCount + 2) := by
    have dyadic : vertexCount < 2 ^ (Nat.log 2 vertexCount + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) vertexCount
    have scale : Nat.log2 vertexCount = Nat.log 2 vertexCount :=
      Nat.log2_eq_log_two
    calc 2 * vertexCount ≤ 2 * 2 ^ (Nat.log 2 vertexCount + 1) :=
          Nat.mul_le_mul (le_refl _) (le_of_lt dyadic)
      _ = 2 ^ (Nat.log 2 vertexCount + 2) := by ring
      _ = 2 ^ (Nat.log2 vertexCount + 2) := by rw [scale]
  calc cubicBaselineBudget vertexCount baselineDegree
      ≤ (2 * vertexCount) ^
          cubicBaselineEdgeCount vertexCount baselineDegree :=
        cubicBaselineBudget_le_pow vertexCount baseline
    _ ≤ (2 ^ (Nat.log2 vertexCount + 2)) ^
          cubicBaselineEdgeCount vertexCount baselineDegree :=
        Nat.pow_le_pow_left base _
    _ = 2 ^ cubicBaselineExponent vertexCount baselineDegree := by
        rw [← pow_mul, cubicBaselineExponent, Nat.mul_comm]

/-- **`def:spine-lower-bound-deficits`' deficit.**

`E_spine(n) = B₀(n) − L` at a package supplying `L` independent target
coordinates.  Truncated subtraction is exactly right: a package that already
exceeds the baseline leaves no deficit. -/
def spineDeficit (vertexCount baselineDegree lowerBound : Nat) : Nat :=
  cubicBaselineExponent vertexCount baselineDegree - lowerBound

/-- The deficit is admissible at its own package: `B₀(n) ≤ L + E_spine(n)` in
bits, for every lower bound `L`.  This is what makes `spineDeficit` an output
rather than a registered constant. -/
theorem cubicBaselineBudget_le_two_pow_add_spineDeficit (vertexCount : Nat)
    {baselineDegree : Nat} (baseline : 2 ≤ baselineDegree)
    (lowerBound : Nat) :
    cubicBaselineBudget vertexCount baselineDegree ≤
      2 ^ (lowerBound + spineDeficit vertexCount baselineDegree lowerBound) := by
  refine le_trans (cubicBaselineBudget_le_two_pow vertexCount baseline) ?_
  refine Nat.pow_le_pow_right (by norm_num) ?_
  unfold spineDeficit
  omega

/-- A larger package leaves a smaller deficit. -/
theorem spineDeficit_le_of_le (vertexCount baselineDegree : Nat)
    {smaller larger : Nat} (supply : smaller ≤ larger) :
    spineDeficit vertexCount baselineDegree larger ≤
      spineDeficit vertexCount baselineDegree smaller :=
  Nat.sub_le_sub_left supply _

/-! ## `def:baseline-spine-demand` -/

universe w

/-- A concrete family in the closed declared-coordinate signature used when a
branch fixes its common baseline spine demand.  The lifted finite label keeps
the coordinate type in the finite object's universe. -/
abbrev FiniteObject.BaselineSpineCoordinate (object : FiniteObject.{w})
    (bits : Nat) :=
  DeclaredSignature.Coordinate object.Vertex (ULift.{w} (Fin bits))

/-- One declared sparse-surplus coordinate of the baseline family. -/
noncomputable def FiniteObject.baselineSpineCoordinate
    (object : FiniteObject.{w}) {bits : Nat} (bit : ULift.{w} (Fin bits)) :
    object.BaselineSpineCoordinate bits :=
  .base .sparseSurplus bit ∅

/-- The concrete declared family with one coordinate for every baseline bit. -/
noncomputable def FiniteObject.baselineSpineFamily
    (object : FiniteObject.{w}) (bits : Nat) :
    Finset (object.BaselineSpineCoordinate bits) := by
  classical
  exact Finset.univ.image object.baselineSpineCoordinate

/-- The support map belonging to the concrete declared baseline family. -/
noncomputable def FiniteObject.baselineSpineSupport
    (object : FiniteObject.{w}) {bits : Nat} :
    object.BaselineSpineCoordinate bits → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact DeclaredSignature.Coordinate.support

@[simp] theorem FiniteObject.card_baselineSpineFamily
    (object : FiniteObject.{w}) (bits : Nat) :
    (object.baselineSpineFamily bits).card = bits := by
  classical
  rw [FiniteObject.baselineSpineFamily, Finset.card_image_iff.mpr]
  · simp [Fintype.card_ulift]
  · intro left _ right _ equality
    simp only [FiniteObject.baselineSpineCoordinate,
      DeclaredSignature.Coordinate.base.injEq] at equality
    exact equality.2.1

/-- **`def:baseline-spine-demand`.**

A family `ℐ_spine` of declared target coordinates is a *baseline spine demand
with deficit `E_spine(n)`* when it is independently target-testable and
`|ℐ_spine| ≥ B₀(n) − E_spine(n)`.

Independent target-testability is the framework's own: the family attains full
target rank under the admissible quotient system it is presented with, which is
`Core.TargetRank`'s `targetRank = card`.  The demand inequality is stated with
the logarithm cleared, `C(N,m₀) ≤ 2^{|ℐ_spine| + E_spine(n)}`, which is
`|ℐ_spine| ≥ B₀(n) − E_spine(n)` before taking `log₂` of the baseline. -/
structure IsBaselineSpineDemand {Coordinate : Type w}
    {family : Finset Coordinate}
    (system : Core.TargetRank.QuotientSystem.{w, w + 1} Coordinate family)
    (vertexCount baselineDegree deficit : Nat) : Prop where
  /-- `ℐ_spine` is independently target-testable. -/
  independent : Core.TargetRank.targetRank system = family.card
  /-- `|ℐ_spine| ≥ B₀(n) − E_spine(n)`, cleared of `log₂`. -/
  demand : cubicBaselineBudget vertexCount baselineDegree ≤
    2 ^ (family.card + deficit)

/-- **Every lower-bound package supplies a baseline spine demand.**

`def:spine-lower-bound-deficits` closes with *"each deficit is an admissible
upper bound for `E_spine(n)` in `def:baseline-spine-demand`, for the
corresponding lower-bound package"*, and this is that sentence: a family that
survives its quotient system and carries at least the package's `L` coordinates
is a baseline spine demand with deficit `spineDeficit … L`.

Nothing about which package is used enters the proof, which is why the three
packages of `def:spine-lower-bound-deficits` need no separate argument. -/
theorem isBaselineSpineDemand_of_package {Coordinate : Type w}
    {family : Finset Coordinate}
    (system : Core.TargetRank.QuotientSystem.{w, w + 1} Coordinate family)
    (vertexCount : Nat) {baselineDegree : Nat} (baseline : 2 ≤ baselineDegree)
    (lowerBound : Nat)
    (testable : system.Survives ↑family)
    (supply : lowerBound ≤ family.card) :
    IsBaselineSpineDemand system vertexCount baselineDegree
      (spineDeficit vertexCount baselineDegree lowerBound) where
  independent :=
    (Core.TargetRank.targetRank_eq_card_iff_survives system).mpr testable
  demand := by
    refine le_trans
      (cubicBaselineBudget_le_two_pow_add_spineDeficit vertexCount baseline
        lowerBound) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## `def:spine-lower-bound-deficits`: the three packages

The manuscript's three packages are three counts of independent target
coordinates the near-cubic branch supplies, each written with the registered
rates rather than with a numeral:

* the *window-only* package `L_win = c₁₃ θ n log₂ n = c₁₃ · p₁₃ · log₂ n`;
* the *high-remainder-entropy* package, which adds `(1/d)|R| log₂ n` on the
  branch `η(R) ≥ (1/d) log₂ n`;
* the *high-entropy plus forced-curvature* package, which adds `K|R|`.

`c₁₃` is the registered per-window barrier rate, `d` the registered entropy
denominator, and `K = c_Ω·ω` the registered curvature cost; `p₁₃`, `|R|` and
`log₂ n` are read off the branch.  The entropy term rounds *down*, which is the
safe direction for a lower bound and is where the manuscript's `−o(n)` goes. -/

/-- **(a) The window-only package**, `L_win = c₁₃ · p₁₃ · log₂ n`. -/
def windowPackageBound (windowRate packing scaleCount : Nat) : Nat :=
  windowRate * packing * scaleCount

/-- **(b) The high-remainder-entropy package**, `L_he = L_win + |R|·log₂ n / d`. -/
def highEntropyPackageBound
    (windowRate packing scaleCount remainder entropyDenominator : Nat) : Nat :=
  windowPackageBound windowRate packing scaleCount +
    remainder * scaleCount / entropyDenominator

/-- **(c) The high-entropy plus forced-curvature package**,
`L_{he+Ω} = L_he + K·|R|`. -/
def curvaturePackageBound
    (windowRate packing scaleCount remainder entropyDenominator
      curvatureCost : Nat) : Nat :=
  highEntropyPackageBound windowRate packing scaleCount remainder
      entropyDenominator +
    curvatureCost * remainder

/-- The packages are increasing: each adds coordinates to the one before it. -/
theorem windowPackageBound_le_highEntropyPackageBound
    (windowRate packing scaleCount remainder entropyDenominator : Nat) :
    windowPackageBound windowRate packing scaleCount ≤
      highEntropyPackageBound windowRate packing scaleCount remainder
        entropyDenominator :=
  Nat.le_add_right _ _

/-- The packages are increasing: the forced-curvature package adds `K|R|`. -/
theorem highEntropyPackageBound_le_curvaturePackageBound
    (windowRate packing scaleCount remainder entropyDenominator
      curvatureCost : Nat) :
    highEntropyPackageBound windowRate packing scaleCount remainder
        entropyDenominator ≤
      curvaturePackageBound windowRate packing scaleCount remainder
        entropyDenominator curvatureCost :=
  Nat.le_add_right _ _

end Hypostructure.Graph
