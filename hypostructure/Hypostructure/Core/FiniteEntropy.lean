import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Hypostructure.Core.FiniteEntropy

universe u

/-! A symbolic entropy profile.  The finite carrier is supplied by a contract;
the framework derives its cardinality and normalized entropy. -/

structure Profile where
  State : Type u
  finiteState : Finite State
  supportSize : Nat

attribute [instance] Profile.finiteState

namespace Profile

noncomputable def stateCount (profile : Profile) : Nat := Nat.card profile.State

noncomputable def normalized (profile : Profile) : ℝ :=
  Real.logb 2 profile.stateCount / profile.supportSize

def semanticChecks (_profile : Profile) : Nat := 0

@[simp] theorem semanticChecks_eq_zero (profile : Profile) :
    profile.semanticChecks = 0 := rfl

end Profile

/-! ## Canonical-state pigeonhole

`lem:independent-target-entropy`, `lem:state-count-comparison`, and the
abstract half of `lem:skeleton-dominates` are all the same one fact, once
stated at this generality: a canonical (i.e. deterministic, choice-free) map
from a finite ambient class to a state type cannot realize more states than
there are ambient objects, because the map sending an object to its state is
a function, not a relation -- two distinct realized states can never come
from the same object. This needs nothing but `Ambient` being finite; it does
not care what a "graph" or a "target-complete state" is, so it holds
identically for a Graph problem's labelled skeletons or a PDE problem's
finite discretizations.

What remains genuinely problem-specific is only the final substitution of
concrete numbers: EG's `n`/`m` playing `Slot`/`m` below, the asymptotic
simplification `m = 1.5n + O(\sqrt n) ⟹ O(\sqrt n \log n)` error term
(`lem:near-cubic-budget`'s own arithmetic), and the P13-specific enumerated
constant `c_{13}` (`lem:p13-window-package`'s appendix computation). Every
other ingredient those lemmas use -- the skeleton-count formula, the
binomial entropy bound, and the disjoint-window independence composition --
needs nothing from `Problem` beyond a bare finite carrier, so all three are
built generically below. -/

/-- Canonical-state pigeonhole: a map from a finite ambient class to a state
type realizes no more states than there are ambient objects. -/
theorem card_range_le_card_ambient {Ambient State : Type*} [Finite Ambient]
    (stateOf : Ambient -> State) :
    Nat.card (Set.range stateOf) ≤ Nat.card Ambient := by
  have hrange : Set.range stateOf = stateOf '' (Set.univ : Set Ambient) :=
    (Set.image_univ).symm
  rw [hrange]
  have := Nat.card_image_le (f := stateOf) (Set.finite_univ (α := Ambient))
  simpa using this

/-- `lem:independent-target-entropy` / `lem:state-count-comparison`, fully
generic: if a canonical state map realizes at least `2 ^ k` distinct states
(the family of `k` independently target-testable Boolean coordinates), then
`2 ^ k` is bounded by the size of the finite ambient class -- `k ≤ log2 |Ambient|`
follows by taking logarithms, exactly as the paper states it. Zero new
mathematics beyond the pigeonhole fact above: the "independent testability"
content is entirely in how the `realizes` hypothesis gets built for a
concrete problem (e.g. `lem:p13-window-package`'s window count), not in this
inequality itself. -/
theorem two_pow_le_card_ambient_of_realizes {Ambient State : Type*} [Finite Ambient]
    (stateOf : Ambient -> State) {k : Nat}
    (realizes : 2 ^ k ≤ Nat.card (Set.range stateOf)) :
    2 ^ k ≤ Nat.card Ambient :=
  realizes.trans (card_range_le_card_ambient stateOf)

/-! ## Labelled skeleton budget

`lem:skeleton-dominates`'s formula `|G_{n,m}| = \binom{\binom n2}{m}` is an
instance of one generic fact: a "labelled skeleton with `m` marks" is a size-`m`
subset of whatever finite carrier the problem declares as its slot alphabet
(a graph's possible edges, a PDE's mesh cells, ...). This is not a new count
to prove -- it is exactly `Finset.card_powersetCard`, stated so that any
problem gets its own "skeleton budget" for free from its own declared `Slot`
type, without reproving the subset-counting argument per instance. -/

/-- The number of `m`-element subsets of a finite `Slot` alphabet: the
domain-generic form of `lem:skeleton-dominates`'s `\binom{\binom n2}{m}`
formula, with `Slot` playing the role of the declared coordinate/edge-slot
presentation and `Fintype.card Slot` playing `\binom n2`. -/
theorem skeletonBudget_card (Slot : Type*) [Fintype Slot] [DecidableEq Slot]
    (m : Nat) :
    (Finset.univ.powersetCard m : Finset (Finset Slot)).card =
      Nat.choose (Fintype.card Slot) m := by
  simp [Finset.card_powersetCard]

/-! ## Binomial entropy bound

`lem:near-cubic-budget`'s proof cites "the standard binomial estimate
`\binom Nm \le (eN/m)^m`" as a known fact before doing any graph-specific
arithmetic with it. That estimate is exactly `Nat.choose_le_pow_div` (`\binom
Nm \le N^m/m!`) combined with Stirling's factorial lower bound already in
Mathlib (`Stirling.le_factorial_stirling`, `m! \ge \sqrt{2\pi m}(m/e)^m`) --
no graph content anywhere in it, so it holds for any `N`, `m`. -/

/-- **Stirling's factorial lower bound in multiplicative form: `m^m \le e^m
\cdot m!`.**

Mathlib carries factorial *upper* bounds (`Nat.factorial_le_pow`,
`Nat.descFactorial_le_pow`) but the binomial entropy estimate needs the other
direction, and that direction is exactly Stirling: `m! \ge \sqrt{2\pi m}
(m/e)^m \ge (m/e)^m`, since the square-root factor is at least `1` once
`m \ge 1`.  Rearranged multiplicatively it is the statement below, which is
the only form the exact `Nat` density comparison can consume -- it has no
division and no `Real.logb`.

`Real.exp 1` here is Euler's number, a mathematical constant of the estimate,
not a parameter of any problem. -/
theorem pow_self_le_exp_pow_mul_factorial (m : Nat) (hm : 1 ≤ m) :
    (m : ℝ) ^ m ≤ (Real.exp 1) ^ m * (Nat.factorial m : ℝ) := by
  have hstirling : Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m ≤ (Nat.factorial m : ℝ) :=
    Stirling.le_factorial_stirling m
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  have hpow_pos : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hfactorial_ge : ((m : ℝ) / Real.exp 1) ^ m ≤ (Nat.factorial m : ℝ) := by
    calc ((m : ℝ) / Real.exp 1) ^ m
        = 1 * ((m : ℝ) / Real.exp 1) ^ m := by ring
      _ ≤ Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m :=
          mul_le_mul_of_nonneg_right hsqrt_ge_one hpow_pos.le
      _ ≤ (Nat.factorial m : ℝ) := hstirling
  have h1 : ((m : ℝ) / Real.exp 1) ^ m = (m : ℝ) ^ m / (Real.exp 1) ^ m := div_pow _ _ _
  rw [h1, div_le_iff₀ (by positivity)] at hfactorial_ge
  linarith [hfactorial_ge]

/-- **The factorial lower bound as one exact `Nat` inequality: `m^m \le 3^m
\cdot m!`.**

This is `pow_self_le_exp_pow_mul_factorial` with `e` replaced by its ceiling
`\lceil e \rceil = 3` (`Real.exp_one_lt_three`, `Real.ceil_exp_one_eq_three`),
so that the whole statement lives in `Nat` and can be multiplied into the
executable density comparison with no cast, no rounding, and no `o(\cdot)`
term.

It is the missing half of the skeleton budget's entropy: composed with
`m! \cdot \binom{\binom n2}{m} \le \binom n2 ^m`, it turns the crude
`\log_2 \binom{\binom n2}{m} \le m \log_2 \binom n2 \approx 2 \cdot \tfrac32 n
\log_2 n` into the manuscript's `\tfrac32 n \log_2 n + O(n)` of
`lem:near-cubic-budget` -- a factor `2` in the leading term, and the entire
difference between a vacuous and a live density cap. -/
theorem pow_self_le_three_pow_mul_factorial (m : Nat) :
    m ^ m ≤ 3 ^ m * Nat.factorial m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have real := pow_self_le_exp_pow_mul_factorial m hm
    have hexpNonneg : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hexpThree : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    have hpow : (Real.exp 1) ^ m ≤ (3 : ℝ) ^ m :=
      pow_le_pow_left₀ hexpNonneg hexpThree m
    have factorialNonneg : (0 : ℝ) ≤ (Nat.factorial m : ℝ) := by positivity
    have bound : (m : ℝ) ^ m ≤ (3 : ℝ) ^ m * (Nat.factorial m : ℝ) :=
      real.trans (mul_le_mul_of_nonneg_right hpow factorialNonneg)
    exact_mod_cast bound

/-- The exact `Nat` form of `\binom n2 = n(n-1)/2`, with no division: the
descending factorial `n^{\underline 2} = (n-1)n` factors as `2! \cdot
\binom n2`.  Used to compare the labelled skeleton budget's alphabet size
against a linear edge count without ever leaving `Nat`. -/
theorem two_mul_choose_two (n : Nat) : 2 * n.choose 2 = (n - 1) * n := by
  have identity : n.descFactorial 2 = Nat.factorial 2 * n.choose 2 :=
    Nat.descFactorial_eq_factorial_mul_choose n 2
  have expand : n.descFactorial 2 = (n - 1) * n := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
    simp
  rw [expand, show Nat.factorial 2 = 2 from rfl] at identity
  exact identity.symm

/-- The standard binomial entropy bound, generic in `N` and `m`: `Nat.choose
N m \le (e N / m)^m` for `m \ge 1`. This is the one fact `lem:near-cubic-budget`
needs before substituting EG's graph-specific `N = \binom n2`,
`m = 1.5n + O(\sqrt n)`; that substitution and its resulting `O`-term
simplification remain genuinely problem-specific, but the inequality itself
does not. -/
theorem choose_le_exp_bound (N m : Nat) (hm : 1 ≤ m) :
    (Nat.choose N m : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
  have hchoose : (Nat.choose N m : ℝ) ≤ (N : ℝ) ^ m / (Nat.factorial m : ℝ) :=
    Nat.choose_le_pow_div m N
  have hkey : (m : ℝ) ^ m ≤ (Real.exp 1) ^ m * (Nat.factorial m : ℝ) :=
    pow_self_le_exp_pow_mul_factorial m hm
  have hbound : (N : ℝ) ^ m / (Nat.factorial m : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
    have hrw : (Real.exp 1 * N / m) ^ m = (Real.exp 1) ^ m * (N : ℝ) ^ m / (m : ℝ) ^ m := by
      rw [div_pow, mul_pow]
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have hN : (0 : ℝ) ≤ (N : ℝ) ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkey hN]
  exact hchoose.trans hbound

/-! ## Disjoint-window independence composition

`lem:p13-window-package`'s closing argument is not the numeric constant
`c_{13}` -- it is the combination step: "distinct packed windows are
vertex-disjoint, ... the tester for one window does not change the label
state assigned to another ... the window packages are therefore independent
across `P`." That composition step needs nothing about what a window,
P13-path, or curvature tester actually is: it only needs one fact per window
(its own local coordinate family is already independently testable, i.e. its
own local state map is injective) plus disjointness of the index set, and
concludes the combined per-window state assignment is again injective with
cardinality the *product* of the local cardinalities -- so no coordinate is
ever counted twice, exactly as the paper argues. -/

/-- Per-window independently-testable families combine into one
independently-testable family on the disjoint union of windows: if each
window's own local state map is injective, so is the pointwise-combined map
into the dependent product of local states. This is `lem:p13-window-package`'s
"no coordinate counted twice" step, fully generic in the window index type
and each window's local coordinate/state types. -/
theorem injective_pi_of_forall_injective {Window : Type*}
    {Coordinate : Window -> Type*} {LocalState : Window -> Type*}
    (localState : ∀ w, Coordinate w -> LocalState w)
    (hinj : ∀ w, Function.Injective (localState w)) :
    Function.Injective (fun (f : ∀ w, Coordinate w) (w : Window) => localState w (f w)) := by
  intro f g hfg
  funext w
  exact hinj w (congrFun hfg w)

/-- The size of the combined independently-testable family is the product of
the per-window sizes, matching the paper's additive-in-log accounting
(`\sum_{a,b}\gamma_{a,b}` over the disjoint windows becomes one sum because
`log2` turns this product into a sum). Immediate from `Nat.card_pi`, given
`Window` and each `Coordinate w` finite. -/
theorem card_pi_eq_prod_card {Window : Type*} [Fintype Window]
    (Coordinate : Window -> Type*) [∀ w, Finite (Coordinate w)] :
    Nat.card (∀ w, Coordinate w) = ∏ w, Nat.card (Coordinate w) :=
  Nat.card_pi

/-! ## Multiplicative rate-floor pigeonhole

The certificate `lem:p13-window-package` actually needs downstream is not a
`Real.logb`-valued estimate at all: the framework's own already-proven
`p13BarrierRateCertificate` (`examples/erdos_64_eg/Erdos64EG/Node21`) states
the exact same content as one Nat inequality, `2 ^ 118 * flat < safe`,
avoiding logarithms entirely. That certificate is *per window*; the paper's
"distinct packed windows are independent, so the window packages combine"
step is the fact that a per-window rate floor compounds multiplicatively
over any number of disjoint windows -- pure Nat/real arithmetic, nothing
about curvature, P13-paths, or graphs in it. -/

/-- A rate floor compounds multiplicatively across `windowCount` disjoint
copies: `lem:p13-window-package`'s independence-across-windows step, stated
arithmetically. Generic in `k`, `flat`, `safe`, `windowCount` -- none of
which need to be a curvature barrier or a P13 window. -/
theorem rateFloor_pow (k flat safe : Nat) (rate : 2 ^ k * flat < safe)
    (windowCount : Nat) :
    2 ^ (k * windowCount) * flat ^ windowCount ≤ safe ^ windowCount := by
  rcases Nat.eq_zero_or_pos windowCount with hw | hw
  · simp [hw]
  · have hpow : (2 ^ k * flat) ^ windowCount ≤ safe ^ windowCount :=
      Nat.pow_le_pow_left rate.le windowCount
    calc 2 ^ (k * windowCount) * flat ^ windowCount
        = (2 ^ k) ^ windowCount * flat ^ windowCount := by rw [pow_mul]
      _ = (2 ^ k * flat) ^ windowCount := by rw [mul_pow]
      _ ≤ safe ^ windowCount := hpow

/-- The compounded rate floor read as what it is: **a bound on the rank**.
`lem:p13-window-package`'s realization at ONE rank, against ONE fixed cap on
the realized-state count, gives `2 ^ (k * rank) ≤ cap`; taking `log2` this is
`prop:p13-density`'s `rank * log2(safe/flat) < B_skel`.

This is the direction a *rank-pinned* entropy account travels: the residual's
own independent rank is bounded by the ambient budget it has to fit inside.
The opposite reading -- demanding the same realization at *every* rank while
the cap stays fixed -- is not a bound at all but a collapse of the rate floor
(`le_of_forall_pow_le_pow_mul` below). -/
theorem two_pow_mul_le_of_rateFloor
    (k flat safe rank cap : Nat) (hflat : 0 < flat)
    (rate : 2 ^ k * flat < safe)
    (realizes : safe ^ rank ≤ flat ^ rank * cap) :
    2 ^ (k * rank) ≤ cap := by
  have hcompound := rateFloor_pow k flat safe rate rank
  have hflatpow : 0 < flat ^ rank := Nat.pow_pos hflat
  have hstep : 2 ^ (k * rank) * flat ^ rank ≤ flat ^ rank * cap :=
    hcompound.trans realizes
  rw [Nat.mul_comm (flat ^ rank) cap] at hstep
  exact Nat.le_of_mul_le_mul_right hstep hflatpow

/-- The full generic bridge: a per-window rate floor, compounded over
`windowCount` disjoint windows and combined with the canonical-state
pigeonhole, bounds `2 ^ (k * windowCount)` by the ambient class size. The
`realizes` hypothesis is exactly the domain-specific content any problem
must supply -- for EG, that its `windowCount`-fold combination of
`injective_pi_of_forall_injective`-composed per-window classifications
realizes at least `safe ^ windowCount / flat ^ windowCount` combined states,
built from its own already-proven per-window `p13BarrierRateCertificate` --
not something this bridge invents. -/
theorem two_pow_mul_le_card_ambient_of_rateFloor {Ambient State : Type*}
    [Finite Ambient] (stateOf : Ambient -> State)
    (k flat safe windowCount : Nat) (hflat : 0 < flat)
    (rate : 2 ^ k * flat < safe)
    (realizes : safe ^ windowCount ≤
      flat ^ windowCount * Nat.card (Set.range stateOf)) :
    2 ^ (k * windowCount) ≤ Nat.card Ambient :=
  (two_pow_mul_le_of_rateFloor k flat safe windowCount _ hflat rate
      realizes).trans
    (card_range_le_card_ambient stateOf)

/-! ## Rank-uniform accounts carry no rate floor

Both halves of the entropy cap are inequalities between a rank-indexed
realized-state family and two fixed quantities: the compounded rate floor
(`safe ^ rank ≤ flat ^ rank * states`, `lem:p13-window-package`'s realization
half) and the ambient budget (`states ^ exponent < ambient ^ remainder`,
`lem:skeleton-dominates` composed with `def:remainder-entropy`).  The theorem
below is what happens when both are demanded *for every* rank while the four
ambient numbers stay fixed: the rate floor collapses.  That is the exact
arithmetic reason the manuscript's cap is a bound *on* the rank rather than a
statement holding at every rank -- `prop:p13-density` reads the same two
inequalities in the other direction, as `rank * log(safe/flat) < B_skel`. -/

/-- The arithmetic core: a rate floor cannot survive **one fixed cap** holding
at every rank.  If `forced ^ rank ≤ flat ^ rank * cap` at every rank for a
single `cap`, then `forced ≤ flat`.

`cap` is deliberately an arbitrary natural: whatever intermediate carrier an
entropy account routes its realized-state count through -- a rank-indexed
family, a finite ambient class, a skeleton budget -- the account still ends in
one fixed number, so no choice of carrier changes the conclusion.  The only
escape is for the realization to be demanded at one rank rather than at every
rank, i.e. for the rank to be pinned to the residual. -/
theorem le_of_forall_pow_le_pow_mul {forced flat cap : Nat}
    (flatPos : 0 < flat)
    (fit : ∀ rank, forced ^ rank ≤ flat ^ rank * cap) :
    forced ≤ flat := by
  by_contra notLe
  have strict : flat < forced := Nat.lt_of_not_le notLe
  have flatReal : (0 : ℝ) < (flat : ℝ) := by exact_mod_cast flatPos
  have oneLt : (1 : ℝ) < (forced : ℝ) / flat := by
    rw [lt_div_iff₀ flatReal]
    have : (flat : ℝ) < (forced : ℝ) := by exact_mod_cast strict
    linarith
  obtain ⟨rank, exceeds⟩ := pow_unbounded_of_one_lt ((cap : Nat) : ℝ) oneLt
  rw [div_pow, lt_div_iff₀ (by positivity)] at exceeds
  have exceedsNat : cap * flat ^ rank < forced ^ rank := by
    exact_mod_cast exceeds
  have chosen := fit rank
  rw [Nat.mul_comm] at chosen
  omega

/-- A rate floor and a fixed ambient budget cannot both hold at every rank:
if a rank-indexed finite realized-state family satisfies the compounded floor
`forced ^ rank ≤ flat ^ rank * card` at every rank, while its cardinality
stays under one fixed budget `ambient ^ remainder` after raising to a fixed
positive `exponent`, then `forced ≤ flat`.  Contrapositively, a strict rate
floor `flat < forced` bounds the ranks at which both can hold. -/
theorem le_of_forall_pow_le_pow_mul_card
    {State : Nat → Type*} [∀ rank, Finite (State rank)]
    {forced flat ambient remainder exponent : Nat}
    (exponentPos : 0 < exponent) (flatPos : 0 < flat)
    (fit : ∀ rank, forced ^ rank ≤ flat ^ rank * Nat.card (State rank))
    (below : ∀ rank, Nat.card (State rank) ^ exponent < ambient ^ remainder) :
    forced ≤ flat := by
  refine le_of_forall_pow_le_pow_mul (cap := ambient ^ remainder) flatPos ?_
  intro rank
  have cardLt : Nat.card (State rank) < ambient ^ remainder := by
    rcases Nat.eq_zero_or_pos (Nat.card (State rank)) with zero | positive
    · have : 0 < ambient ^ remainder :=
        lt_of_le_of_lt (Nat.zero_le _) (below rank)
      omega
    · exact lt_of_le_of_lt (Nat.le_self_pow exponentPos.ne' _) (below rank)
  exact (fit rank).trans (Nat.mul_le_mul_left _ cardLt.le)

/-- Routing the realized-state count through a finite ambient class does not
rescue a rank-uniform account.  Even when the realized states of every rank
are realized by one finite ambient class (the canonical-assignment pigeonhole
of `lem:skeleton-dominates`) and that class fits the skeleton budget
`ambient ^ remainder`, demanding the compounded realization at every rank
still forces `forced ≤ flat`.

This is why supplying `Ambient`, a realization map, and a skeleton budget is
not by itself a way to make a `∀ rank` entropy account fillable: the rank has
to stop being a free variable. -/
theorem le_of_forall_pow_le_pow_mul_card_of_ambient
    {Ambient : Type*} [Finite Ambient] {State : Nat → Type*}
    {forced flat ambient remainder : Nat} (flatPos : 0 < flat)
    (realize : ∀ rank, Ambient → State rank)
    (realizeSurjective : ∀ rank, Function.Surjective (realize rank))
    (budget : Nat.card Ambient ≤ ambient ^ remainder)
    (fit : ∀ rank, forced ^ rank ≤ flat ^ rank * Nat.card (State rank)) :
    forced ≤ flat := by
  refine le_of_forall_pow_le_pow_mul (cap := ambient ^ remainder) flatPos ?_
  intro rank
  have card_le : Nat.card (State rank) ≤ ambient ^ remainder :=
    (Nat.card_le_card_of_surjective (realize rank)
      (realizeSurjective rank)).trans budget
  exact (fit rank).trans (Nat.mul_le_mul_left _ card_le)

/-! ## Pinning by a bound, not by an equality

The three collapse theorems above say the same thing: a compounded rate floor
demanded at *every* rank against one fixed cap is not an entropy account.
They leave open exactly one escape, and the escape is cheaper than it looks.
The realization inequality `forced ^ rank ≤ flat ^ rank * cap` is **monotone
in the exponent** whenever the rate floor is strict (`flat ≤ forced`): proving
it once at any upper bound for the rank yields it at the rank itself.

So an account does not have to publish the rank *exactly*.  It only has to
publish one residual-derived quantity that dominates it -- which is how the
manuscript's own account reads: invariant 29 caps the curvature rank by
`0.611561 |R|` independent tests, a function of the remainder alone, and
`prop:p13-density` then compares that cap with the skeleton budget.  A
producer obligation of the form `rank ≤ bound residual` is strictly weaker
than `rank = rankOf residual`, and by the lemma below it is already enough. -/

/-- The compounded realization inequality is monotone in its exponent under a
non-strict rate floor: realized once at `bound`, it holds at every `rank`
below `bound`.

This is the arithmetic that makes a rank *bound* sufficient where
`le_of_forall_pow_le_pow_mul` shows a rank *quantifier* is fatal.  Nothing
here is specific to curvature ranks, packing counts, or windows: `forced`,
`flat`, `cap`, `rank`, `bound` are arbitrary naturals. -/
theorem pow_le_pow_mul_of_le_of_rank_le
    {forced flat cap rank bound : Nat}
    (flatPos : 0 < flat) (rateFloor : flat ≤ forced)
    (rankLe : rank ≤ bound)
    (fit : forced ^ bound ≤ flat ^ bound * cap) :
    forced ^ rank ≤ flat ^ rank * cap := by
  have split : bound = rank + (bound - rank) := (Nat.add_sub_cancel' rankLe).symm
  have flatPow : 0 < flat ^ (bound - rank) := Nat.pow_pos flatPos
  have step :
      forced ^ rank * flat ^ (bound - rank) ≤
        flat ^ rank * cap * flat ^ (bound - rank) := by
    calc forced ^ rank * flat ^ (bound - rank)
        ≤ forced ^ rank * forced ^ (bound - rank) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left rateFloor _)
      _ = forced ^ bound := by rw [← pow_add, ← split]
      _ ≤ flat ^ bound * cap := fit
      _ = flat ^ rank * flat ^ (bound - rank) * cap := by rw [← pow_add, ← split]
      _ = flat ^ rank * cap * flat ^ (bound - rank) := by ring
  exact Nat.le_of_mul_le_mul_right step flatPow

/-- Capping the exponent at one residual-derived bound really does defuse the
collapse, and this records why: an account that demands the realization at
`min rank bound` for *every* `rank` demands exactly one inequality, the one
at `bound`.  There is no rank-indexed family left for
`le_of_forall_pow_le_pow_mul` to run its unbounded-growth argument on.

Stated as an iff so that neither direction can be mistaken for the other: the
capped `∀ rank` form and the single instance at `bound` are the same
statement. -/
theorem forall_pow_min_iff_pow_bound
    {forced flat cap bound : Nat}
    (flatPos : 0 < flat) (rateFloor : flat ≤ forced) :
    (∀ rank, forced ^ min rank bound ≤ flat ^ min rank bound * cap) ↔
      forced ^ bound ≤ flat ^ bound * cap := by
  constructor
  · intro capped
    simpa using capped bound
  · intro atBound rank
    exact pow_le_pow_mul_of_le_of_rank_le flatPos rateFloor
      (min_le_right rank bound) atBound

/-- A registered rate-floor import: one bundle for a problem's own
`2 ^ k * flat < safe` fact (`lem:p13-window-package`-style, computed however
the domain computes it -- a finite curvature enumeration for EG, some other
finite check for a PDE problem), so that importing one from an external,
already-proven source (a sibling package's own certificate, a `decide`
computation, anything) is filling in one structure, not scattering `k`/
`flat`/`safe`/`flatPos`/`rate` across separate top-level declarations. -/
structure RateFloorCertificate where
  k : Nat
  flat : Nat
  safe : Nat
  flatPos : 0 < flat
  rate : 2 ^ k * flat < safe

namespace RateFloorCertificate

/-- Build a rate-floor certificate from the computed inequality itself.
All numeric fields are implicit indices inferred from the theorem's type, so
an application never repeats a table-derived exponent or product. -/
def ofComputedRate {k flat safe : Nat}
    (flatPos : 0 < flat) (rate : 2 ^ k * flat < safe) :
    RateFloorCertificate where
  k := k
  flat := flat
  safe := safe
  flatPos := flatPos
  rate := rate

@[simp] theorem ofComputedRate_k {k flat safe : Nat}
    (flatPos : 0 < flat) (rate : 2 ^ k * flat < safe) :
    (ofComputedRate flatPos rate).k = k := rfl

end RateFloorCertificate

end Hypostructure.Core.FiniteEntropy
