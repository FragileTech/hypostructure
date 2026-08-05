import Hypostructure.Core.FiniteEntropy
import Hypostructure.Graph.Finite

/-!
# The labelled skeleton budget

`lem:skeleton-dominates` counts the labelled simple graphs on a fixed vertex
set with a fixed number of edges, and `prop:p13-density` spends that count as
an entropy budget.  Both are statements about two natural numbers read off an
object -- its vertex count and its edge count -- so both are stated here, in
exact `Nat` arithmetic, with no rounding term and no numeral of any
presentation.

Every threshold a consumer needs is a parameter: the minimum-degree baseline
`baselineDegree`, the node-`[19]` surplus threshold, and the exponent being
capped are all supplied by the caller from its own presentation.  Nothing in
this file knows which problem is being argued.
-/

namespace Hypostructure.Graph

open Hypostructure

universe v

/-- `lem:skeleton-dominates`: the number of labelled simple graphs on the
residual object's own vertex set carrying exactly as many edges as the
residual object itself.  A labelled simple graph on `[n]` is determined by
its edge set, a subset of the `C(n,2)` unordered pairs, so the class with `m`
edges has exactly `C(C(n,2), m)` members. -/
def skeletonBudget (object : Graph.FiniteObject.{v}) : Nat :=
  (object.vertexCount.choose 2).choose object.edgeCount

/-- The skeleton budget is positive: the residual object's own edge count is
one of the admissible edge counts on its own vertex set, so the class it
indexes is nonempty.  The bound `m ≤ C(n,2)` is the literal graph fact
`FiniteObject.edgeCount_le_choose_two`, not an assumption. -/
theorem skeletonBudget_pos (object : Graph.FiniteObject.{v}) :
    0 < skeletonBudget object :=
  Nat.choose_pos (object.edgeCount_le_choose_two)

/-- The near-cubic skeleton budget never exceeds the count of *all* labelled
graphs on the same vertex set, which is the capacity the adapter used to
register.  Fixing the edge count is therefore a strict sharpening of the
ambient class, and every cap the density comparison now survives is at least
as strong as the one it survived before. -/
theorem skeletonBudget_le_two_pow (object : Graph.FiniteObject.{v}) :
    skeletonBudget object ≤ 2 ^ (object.vertexCount.choose 2) :=
  Nat.choose_le_two_pow _ _

/-- **The skeleton budget carries its own `m!`.**

`skeletonBudget_le_two_pow` is far too weak to bound a packing density: it
throws away the whole `m`-subset structure and leaves `2 ^ C(n,2)`, which is
`n²` in the exponent where the manuscript has `n log₂ n`.  The exact statement
is that the labelled skeleton class is an `m`-subset family, so its count times
`m !` is at most `C(n,2) ^ m`:

  `m ! · C(C(n,2), m) = descFactorial (C(n,2)) m ≤ C(n,2) ^ m`.

Taking `log₂`, the `m !` is exactly the factor that turns the crude
`m · log₂ C(n,2) ≈ 2 · (3/2) n log₂ n` into the manuscript's
`(3/2) n log₂ n + O(n)` of `lem:near-cubic-budget` — a factor `2` in the
leading term, and the whole difference between a vacuous and a live density
cap.  Both `n` and `m` are read off the residual object; nothing is chosen
here. -/
theorem factorial_mul_skeletonBudget_le_pow (object : Graph.FiniteObject.{v}) :
    Nat.factorial object.edgeCount * skeletonBudget object ≤
      (object.vertexCount.choose 2) ^ object.edgeCount := by
  have identity :
      (object.vertexCount.choose 2).descFactorial object.edgeCount =
        Nat.factorial object.edgeCount * skeletonBudget object :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  rw [← identity]
  exact Nat.descFactorial_le_pow _ _

/-- The entropy form of `factorial_mul_skeletonBudget_le_pow`: whatever
exponent the density comparison certifies against the skeleton budget is
certified against `C(n,2) ^ m` with the `m !` retained.

Composed with
`Core.Strategy.FiniteDensityBudget.Profile.CapResidual.two_pow_rate_mul_packingCount_le_ambientCapacity`
at `exponent := rate * packingCount`, this is `prop:p13-density`'s comparison
in exact `Nat` form:

  `2 ^ (c_hot · log₂ n · p₁₃) · m ! ≤ C(n,2) ^ m`,

with `c_hot · log₂ n` read from the barrier `Summary` and the object's dyadic
scale count, and `n`, `m` read off the object.  No numeral appears on either
side. -/
theorem two_pow_mul_factorial_le_pow
    (object : Graph.FiniteObject.{v}) (exponent : Nat)
    (demand : 2 ^ exponent ≤ skeletonBudget object) :
    2 ^ exponent * Nat.factorial object.edgeCount ≤
      (object.vertexCount.choose 2) ^ object.edgeCount := by
  calc 2 ^ exponent * Nat.factorial object.edgeCount
      ≤ skeletonBudget object * Nat.factorial object.edgeCount :=
        Nat.mul_le_mul demand (le_refl _)
    _ = Nat.factorial object.edgeCount * skeletonBudget object :=
        Nat.mul_comm _ _
    _ ≤ (object.vertexCount.choose 2) ^ object.edgeCount :=
        factorial_mul_skeletonBudget_le_pow object

/-- **The near-cubic edge count, read rather than assumed.**

`def:near-cubic-spine` is a branch state, not a global hypothesis, and the
branch that records it is node `[19]`'s `scaleThresholdDichotomy`.  Its
at-or-below arm publishes exactly `σ(G) ≤ T(n)`, where `σ` is
`FiniteObject.degreeSurplus baselineDegree` and `T` is whatever threshold table
the presentation registered — read off the residual by
`Graph.NearCubicSpine.nearCubicSpine_of_atOrBelow`, whose conclusion is
literally this theorem's hypothesis.

The handshake `Σ_v deg v = 2m` then converts that surplus bound into an edge
bound.  `degreeSurplus` is *defined* as `2m - baselineDegree · n`
(`Graph.Finite`), which is the subtraction form of the handshake
`σ + baselineDegree · n = 2m`; truncated subtraction makes the conversion
unconditional, so no extra positivity is needed.

Every quantity is read: `baselineDegree` is the registered minimum-degree
baseline of the presentation, `threshold` is the registered table's value at
the object's own order, and `edgeCount`/`vertexCount` are the object's.  At the
EG presentation's `baselineDegree = 3` this specializes to `m ≤ 3n/2 + σ/2`,
but the `3` is the presentation's, never this file's. -/
theorem two_mul_edgeCount_le_of_degreeSurplus_le
    (object : Graph.FiniteObject.{v}) (baselineDegree threshold : Nat)
    (surplusBound : object.degreeSurplus baselineDegree ≤ threshold) :
    2 * object.edgeCount ≤
      baselineDegree * object.vertexCount + threshold := by
  have expanded :
      2 * object.edgeCount - baselineDegree * object.vertexCount ≤ threshold :=
    surplusBound
  rw [Nat.add_comm]
  exact Nat.sub_le_iff_le_add.mp expanded

/-- **The complementary near-cubic edge bound, also read rather than assumed.**

`two_mul_edgeCount_le_of_degreeSurplus_le` caps `2m` from above off the node
`[19]` branch.  The density comparison also needs `2m` from *below*, and that
half is not a branch fact at all: it is the handshake against the presentation's
own closed minimum-degree baseline, `Σ_v deg v = 2m` with `deg v ≥ δ` at every
vertex, i.e. `δ n ≤ 2m`.

The proof is the handshake itself and nothing else: summing the constant `δ`
over the vertices is `δ n`, summing the degrees is `2m`, and the baseline
compares the two summands pointwise.  `δ` is the baseline the presentation
registered to produce `degreeSurplus`, the same one
`two_mul_edgeCount_le_of_degreeSurplus_le` subtracts. -/
theorem baselineDegree_mul_vertexCount_le_two_mul_edgeCount
    (object : Graph.FiniteObject.{v}) (baselineDegree : Nat)
    (lower : ∀ vertex : object.Vertex, baselineDegree ≤ object.degree vertex) :
    baselineDegree * object.vertexCount ≤ 2 * object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have constant :
      (∑ _vertex : object.Vertex, baselineDegree) =
        baselineDegree * object.vertexCount := by
    simp [Finset.sum_const, Finset.card_univ, FiniteObject.vertexCount,
      FinEnum.card_eq_fintypeCard, Nat.mul_comm]
  have handshake :
      (∑ vertex : object.Vertex, object.degree vertex) =
        2 * object.edgeCount := by
    simpa [FiniteObject.degree, FiniteObject.edgeCount] using
      object.graph.sum_degrees_eq_twice_card_edges
  calc baselineDegree * object.vertexCount
      = ∑ _vertex : object.Vertex, baselineDegree := constant.symm
    _ ≤ ∑ vertex : object.Vertex, object.degree vertex :=
        Finset.sum_le_sum fun vertex _ => lower vertex
    _ = 2 * object.edgeCount := handshake

/-! ### From the surviving cap to a linear packing bound

The three facts above -- the retained cap, the skeleton budget's own `m !`, and
the two-sided near-cubic edge count -- combine into a bound on the packing that
is *linear in the order*, which is the whole point of `prop:p13-density`.  The
combination is done here once, entirely in `Nat`, with no `o(·)` term and no
numeral: `3` below is `⌈e⌉` from Stirling
(`Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`), and every other
quantity is read off the residual object or supplied by the caller. -/

/-- The alphabet-versus-edge comparison that makes the skeleton budget's `m !`
bite.

`\binom n2` is the number of edge slots; `m` is how many are filled.  The
labelled skeleton class therefore costs `\binom n2 ^m / m !` rather than
`\binom n2 ^m`, and by Stirling that is at most `(\lceil e\rceil \binom n2 /
m)^m`.  This lemma is exactly the statement that the base of that power is
bounded by `budgetBase`:

  `⌈e⌉ · \binom n2 ≤ m · budgetBase`.

Both hypotheses are the two halves of `def:near-cubic-spine`'s edge count.
Written out with `2\binom n2 = (n-1)n`, the proof is the single chain

  `2·(3\binom n2) = (3(n-1))·n ≤ (δ·budgetBase)·n = (δ n)·budgetBase
     ≤ (2m)·budgetBase`,

so no positivity of `δ` is needed anywhere. -/
theorem three_mul_choose_two_le_edgeCount_mul
    (object : Graph.FiniteObject.{v}) (baselineDegree budgetBase : Nat)
    (spine : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount)
    (budget :
      3 * (object.vertexCount - 1) ≤ baselineDegree * budgetBase) :
    3 * (object.vertexCount.choose 2) ≤ object.edgeCount * budgetBase := by
  have doubled :
      2 * (3 * (object.vertexCount.choose 2)) ≤
        2 * (object.edgeCount * budgetBase) := by
    calc 2 * (3 * (object.vertexCount.choose 2))
        = 3 * (2 * (object.vertexCount.choose 2)) := by ring
      _ = (3 * (object.vertexCount - 1)) * object.vertexCount := by
          rw [Core.FiniteEntropy.two_mul_choose_two]; ring
      _ ≤ (baselineDegree * budgetBase) * object.vertexCount :=
          Nat.mul_le_mul budget (le_refl _)
      _ = (baselineDegree * object.vertexCount) * budgetBase := by ring
      _ ≤ (2 * object.edgeCount) * budgetBase :=
          Nat.mul_le_mul spine (le_refl _)
      _ = 2 * (object.edgeCount * budgetBase) := by ring
  exact Nat.le_of_mul_le_mul_left doubled (by norm_num)

/-- **`prop:p13-density` as one exact `Nat` power comparison.**

Whatever exponent the surviving density cap certifies against the labelled
skeleton budget is certified against `budgetBase ^ m`, where `budgetBase` is
any number the alphabet comparison above admits:

  `2 ^ exponent ≤ \binom{\binom n2}{m}` ⟹ `2 ^ exponent ≤ budgetBase ^ m`.

This is where the `m !` is spent.  Without it the only available bound is
`2 ^ exponent ≤ \binom n2 ^m`, whose base is quadratic in `n`; with it the base
drops to `budgetBase`, which the near-cubic spine makes *linear* in `n`.  That
factor `2` in `\log_2` is precisely `lem:near-cubic-budget`'s
`\tfrac32 n\log_2 n + O(n)` against the crude `3n\log_2 n`, and it is the whole
difference between a vacuous and a live cap.

The `m = 0` case is not excluded by hypothesis: an object with no edges has
skeleton budget `\binom{\binom n2}{0} = 1`, which already forces
`exponent = 0`. -/
theorem two_pow_le_pow_of_skeletonBudget_cap
    (object : Graph.FiniteObject.{v})
    (exponent baselineDegree budgetBase : Nat)
    (cap : 2 ^ exponent ≤ skeletonBudget object)
    (spine : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount)
    (budget :
      3 * (object.vertexCount - 1) ≤ baselineDegree * budgetBase) :
    2 ^ exponent ≤ budgetBase ^ object.edgeCount := by
  rcases Nat.eq_zero_or_pos object.edgeCount with edgeZero | edgePos
  · have budgetOne : skeletonBudget object = 1 := by
      simp [skeletonBudget, edgeZero]
    rw [budgetOne] at cap
    rw [edgeZero, pow_zero]
    exact cap
  · have alphabet :
        3 * (object.vertexCount.choose 2) ≤ object.edgeCount * budgetBase :=
      three_mul_choose_two_le_edgeCount_mul object baselineDegree budgetBase
        spine budget
    have factorialCap :
        Nat.factorial object.edgeCount * 2 ^ exponent ≤
          (object.vertexCount.choose 2) ^ object.edgeCount :=
      le_trans (Nat.mul_le_mul (le_refl _) cap)
        (factorial_mul_skeletonBudget_le_pow object)
    have scaled :
        3 ^ object.edgeCount *
            (Nat.factorial object.edgeCount * 2 ^ exponent) ≤
          3 ^ object.edgeCount *
            (object.vertexCount.choose 2) ^ object.edgeCount :=
      Nat.mul_le_mul (le_refl _) factorialCap
    have left :
        object.edgeCount ^ object.edgeCount * 2 ^ exponent ≤
          3 ^ object.edgeCount *
            (Nat.factorial object.edgeCount * 2 ^ exponent) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul
        (Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial
          object.edgeCount)
        (le_refl _)
    have right :
        3 ^ object.edgeCount *
            (object.vertexCount.choose 2) ^ object.edgeCount ≤
          object.edgeCount ^ object.edgeCount *
            budgetBase ^ object.edgeCount := by
      simpa [mul_pow] using Nat.pow_le_pow_left alphabet object.edgeCount
    have chain :
        object.edgeCount ^ object.edgeCount * 2 ^ exponent ≤
          object.edgeCount ^ object.edgeCount *
            budgetBase ^ object.edgeCount :=
      le_trans left (le_trans scaled right)
    exact Nat.le_of_mul_le_mul_left chain (Nat.pow_pos edgePos)

/-- The same comparison with the alphabet comparison discharged by the
minimum-degree baseline alone.

`budgetBase := n - 1` is admissible as soon as the registered baseline is at
least `⌈e⌉`, because the alphabet hypothesis becomes
`3(n-1) ≤ δ(n-1)`.  For a presentation whose minimum-degree baseline is the
cubic one this reads

  `2 ^ (c₁₃ · log₂ n · p₁₃) ≤ (n-1) ^ m`,

which is `prop:p13-density` verbatim and exactly, with no rounding term. -/
theorem two_pow_le_pow_pred_vertexCount
    (object : Graph.FiniteObject.{v})
    (exponent baselineDegree : Nat)
    (cap : 2 ^ exponent ≤ skeletonBudget object)
    (spine : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount)
    (baseline : 3 ≤ baselineDegree) :
    2 ^ exponent ≤ (object.vertexCount - 1) ^ object.edgeCount :=
  two_pow_le_pow_of_skeletonBudget_cap object exponent baselineDegree
    (object.vertexCount - 1) cap spine
    (Nat.mul_le_mul baseline (le_refl _))

/-- The entropy (`log₂`) form of an exact power comparison: a base bounded by
`2 ^ budgetLog` turns `2 ^ exponent ≤ base ^ count` into the linear bound
`exponent ≤ budgetLog · count`.  Nothing here is graph-specific; it is the
`Nat` replacement for taking logarithms. -/
theorem exponent_le_of_two_pow_le_pow
    (exponent base budgetLog count : Nat)
    (bounded : 2 ^ exponent ≤ base ^ count)
    (baseBound : base ≤ 2 ^ budgetLog) :
    exponent ≤ budgetLog * count := by
  have raised : base ^ count ≤ (2 ^ budgetLog) ^ count :=
    Nat.pow_le_pow_left baseBound count
  rw [← Nat.pow_mul] at raised
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    (le_trans bounded raised)

/-- The separated dyadic scales carried by an object of order `n`, namely the
range `2⁰, 2¹, …, 2^{⌊log₂ n⌋ - 1}` of dyadic scales strictly below `n`.  Read
off the residual object's own vertex count, so the window package's entropy
demand is residual-derived.

The manuscript writes this count as `⌊log₂ n⌋ - O(1)`, the unquantified
additive loss absorbing endpoint collisions with the finitely many reserved
boundary and tie-breaking choices inside the canonical packing; that bounded
loss is exactly what its `c₁₃ - o(1)` per-window rate carries, and it does not
change the `log₂ n` growth registered here. -/
def dyadicScaleCount (object : Graph.FiniteObject.{v}) : Nat :=
  Nat.log2 object.vertexCount

/-- The registered scale range is the exact dyadic range of the object: `2` to
the scale count never exceeds the object's own order. -/
theorem two_pow_dyadicScaleCount_le (object : Graph.FiniteObject.{v})
    (positive : 0 < object.vertexCount) :
    2 ^ dyadicScaleCount object ≤ object.vertexCount := by
  simpa [dyadicScaleCount, Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (Nat.ne_of_gt positive)

/-- Complementary exactness of the registered scale range: the object's order
is strictly below the next dyadic scale.  Together with
`two_pow_dyadicScaleCount_le` this pins `2 ^ dyadicScaleCount` to `n` up to a
factor `2`, which is the sense in which a demand of `safe ^ dyadicScaleCount`
is a demand of `n ^ log₂ safe`. -/
theorem lt_two_pow_succ_dyadicScaleCount (object : Graph.FiniteObject.{v}) :
    object.vertexCount < 2 ^ (dyadicScaleCount object + 1) := by
  simpa [dyadicScaleCount, Nat.log2_eq_log_two] using
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) object.vertexCount

/-- **The linear form of the surviving cap: `exponent ≤ (log₂ n + 1) · m`.**

`two_pow_le_pow_pred_vertexCount` bounds the cap's exponent by `(n-1)^m`; the
object's own dyadic scale count converts that base to a power of two through
`lt_two_pow_succ_dyadicScaleCount`, giving the entropy statement the manuscript
writes as

  `c₁₃ · p₁₃ · log₂ n ≤ m · log₂ n + O(m)`.

Both `log₂ n` and `m` are read off the residual object.  The `+1` is the exact
`Nat` cost of `n` not being a power of two; it is the only slack in the whole
chain and it is `m` bits against a budget of `m log₂ n`.  The slack-free
statement is `two_pow_le_pow_pred_vertexCount` itself. -/
theorem exponent_le_dyadicScaleCount_succ_mul_edgeCount
    (object : Graph.FiniteObject.{v})
    (exponent baselineDegree : Nat)
    (cap : 2 ^ exponent ≤ skeletonBudget object)
    (spine : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount)
    (baseline : 3 ≤ baselineDegree) :
    exponent ≤ (dyadicScaleCount object + 1) * object.edgeCount :=
  exponent_le_of_two_pow_le_pow exponent (object.vertexCount - 1)
    (dyadicScaleCount object + 1) object.edgeCount
    (two_pow_le_pow_pred_vertexCount object exponent baselineDegree cap spine
      baseline)
    (le_trans (Nat.sub_le _ _)
      (le_of_lt (lt_two_pow_succ_dyadicScaleCount object)))

/-- **`prop:p13-density`, fully composed: the packing is linear in the order.**

The surviving density cap, the skeleton budget's `m !`, the minimum-degree
handshake and the node-`[19]` at-or-below branch fact combine into

  `2 · exponent ≤ (log₂ n + 1) · (δ n + T(n))`,

with `exponent = rate · p₁₃` on the left.  Every symbol is read: `rate` from the
registered barrier `Summary` (through
`Core.Strategy.FiniteBarrierEnumeration.two_pow_rate_mul_scaleCount_mul_flatProduct_le_safeProduct`
its value is the scale-free rate times `dyadicScaleCount`), `δ` is the
presentation's registered minimum-degree baseline, and `T` is the node-`[19]`
threshold table at the object's own order.

Dividing through, this is `θ = p₁₃/n ≤ (δ/2)(1 + 1/log₂ n)/rate₀ + O(T/n)`: a
bound on the packing density by the *reciprocal of the registered barrier
rate*, converging to `δ/(2·rate₀)` as the order grows.  That is the
manuscript's `θ ≤ θ_win`, and it is the only route to
`Δ_net(R) ≤ 15θ/(1-13θ) < 1/4`. -/
theorem two_mul_exponent_le_scale_mul_edgeBudget
    (object : Graph.FiniteObject.{v})
    (exponent baselineDegree threshold : Nat)
    (cap : 2 ^ exponent ≤ skeletonBudget object)
    (spine : baselineDegree * object.vertexCount ≤ 2 * object.edgeCount)
    (baseline : 3 ≤ baselineDegree)
    (nearCubic : object.degreeSurplus baselineDegree ≤ threshold) :
    2 * exponent ≤
      (dyadicScaleCount object + 1) *
        (baselineDegree * object.vertexCount + threshold) := by
  have linear : exponent ≤ (dyadicScaleCount object + 1) * object.edgeCount :=
    exponent_le_dyadicScaleCount_succ_mul_edgeCount object exponent
      baselineDegree cap spine baseline
  have edges :
      2 * object.edgeCount ≤
        baselineDegree * object.vertexCount + threshold :=
    two_mul_edgeCount_le_of_degreeSurplus_le object baselineDegree threshold
      nearCubic
  calc 2 * exponent
      ≤ 2 * ((dyadicScaleCount object + 1) * object.edgeCount) :=
        Nat.mul_le_mul (le_refl _) linear
    _ = (dyadicScaleCount object + 1) * (2 * object.edgeCount) := by ring
    _ ≤ (dyadicScaleCount object + 1) *
          (baselineDegree * object.vertexCount + threshold) :=
        Nat.mul_le_mul (le_refl _) edges

end Hypostructure.Graph
