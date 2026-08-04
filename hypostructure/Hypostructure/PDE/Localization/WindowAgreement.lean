import Hypostructure.PDE.Localization.TemperedBridge
import Hypostructure.PDE.Solution.InteriorRegularity

/-!
# Agreement on a window

A local argument never needs two states to be *equal*.  It needs them to be
indistinguishable by the tests it actually uses --- those supported in its own
window --- and nothing more.  That relation is `AgreeOn`, and this module is
its algebra.

The point is reuse.  Without it every operator the regularity theory names
(gradient, divergence, curl, Laplacian, heat, and any composite) would need its
own transport lemma across the bridge of
`Localization/TemperedBridge.lean`, each proved by the same induction.  With
it, one fact --- `agreeOn_lineDerivOp_temperedOfLocal`, "differentiating the
bridged object agrees on the window with bridging the differentiated one" ---
plus closure of `AgreeOn` under the vector-space operations and under
differentiation gives every one of them for free, at any depth of nesting, for
any problem.

`AgreeOn.smoothOn` is the exit: agreement on a window transfers `SmoothOn`,
because `SmoothOn` reads a state only through bumps supported in the region.
So a fact established for a bridged object is a fact about the original one
there, and the framework's parabolic bootstrap can be pointed at either.

Nothing here mentions an equation, a dimension, a residual or a problem.
-/

namespace Hypostructure.PDE.Localization

open TopologicalSpace
open Hypostructure.PDE.Solution.InteriorRegularity
open scoped Distributions SchwartzMap LineDeriv

universe uPoint uValue

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {domain : Opens Point} {window : Compacts Point}

/--
**Two tempered states agree on a window** when no test function supported
there can tell them apart.

This is weaker than equality --- it says nothing off the window --- and it is
exactly the hypothesis every local statement in the framework consumes.
-/
def AgreeOn (window : Compacts Point) (first second : 𝓢'(Point, Value)) : Prop :=
  ∀ test : 𝓢(Point, ℂ), tsupport (test : Point → ℂ) ⊆ window →
    first test = second test

namespace AgreeOn

variable {first second third : 𝓢'(Point, Value)}

@[refl] theorem refl (state : 𝓢'(Point, Value)) : AgreeOn window state state :=
  fun _ _ => rfl

theorem symm (agree : AgreeOn window first second) : AgreeOn window second first :=
  fun test supported => (agree test supported).symm

theorem trans (left : AgreeOn window first second)
    (right : AgreeOn window second third) : AgreeOn window first third :=
  fun test supported => (left test supported).trans (right test supported)

theorem of_eq (equal : first = second) : AgreeOn window first second :=
  equal ▸ AgreeOn.refl first

/-! ### Closure under the vector-space operations

Each is the corresponding pointwise operation on values, so the proofs are
`simp` on the applied form. -/

theorem add {a b c d : 𝓢'(Point, Value)} (left : AgreeOn window a b)
    (right : AgreeOn window c d) : AgreeOn window (a + c) (b + d) :=
  fun test supported => by
    simp only [ContinuousLinearMap.add_apply, left test supported,
      right test supported]

theorem sub {a b c d : 𝓢'(Point, Value)} (left : AgreeOn window a b)
    (right : AgreeOn window c d) : AgreeOn window (a - c) (b - d) :=
  fun test supported => by
    simp only [ContinuousLinearMap.sub_apply, left test supported,
      right test supported]

theorem neg (agree : AgreeOn window first second) :
    AgreeOn window (-first) (-second) :=
  fun test supported => by
    simp only [ContinuousLinearMap.neg_apply, agree test supported]

theorem sum {Coordinate : Type*} (indices : Finset Coordinate)
    {left right : Coordinate → 𝓢'(Point, Value)}
    (agree : ∀ index ∈ indices, AgreeOn window (left index) (right index)) :
    AgreeOn window (∑ index ∈ indices, left index)
      (∑ index ∈ indices, right index) :=
  fun test supported => by
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun index mem => agree index mem test supported

/-! ### Closure under differentiation

The one structural fact: a derivative is a transpose, and the derivative of a
test function supported in the window is again supported in the window
(`SchwartzMap.tsupport_lineDerivOp_subset`).  So differentiating cannot expose
a difference that was invisible before. -/

theorem lineDerivOp (agree : AgreeOn window first second) (direction : Point) :
    AgreeOn window (∂_{direction} first) (∂_{direction} second) := by
  intro test supported
  have derivative_supported :
      tsupport ((-∂_{direction} test : 𝓢(Point, ℂ)) : Point → ℂ) ⊆ window :=
    subset_trans (subset_trans (subset_of_eq (tsupport_neg _))
      (SchwartzMap.tsupport_lineDerivOp_subset direction test)) supported
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.lineDerivOp_apply_apply,
    agree _ derivative_supported]

theorem lineDerivs (agree : AgreeOn window first second)
    (directions : List Point) :
    AgreeOn window (temperedLineDerivs directions first)
      (temperedLineDerivs directions second) := by
  induction directions with
  | nil => exact agree
  | cons direction rest inductive_hypothesis =>
    exact inductive_hypothesis.lineDerivOp direction

/-! ### The exit: agreement transfers smoothness

`SmoothOn` reads a state only through bumps supported in the region, and
cutting a probe off by such a bump produces a probe supported in the window.
So the two states have the same localizations there, and
`SmoothOn.congr_localize` does the rest. -/

/-- Cutting a probe off by a bump leaves it supported where the bump is. -/
theorem tsupport_smulLeftCLM_subset (bump : Bump Point) (probe : 𝓢(Point, ℂ)) :
    tsupport ((SchwartzMap.smulLeftCLM ℂ bump.weight probe : 𝓢(Point, ℂ)) :
        Point → ℂ) ⊆ tsupport bump.weight := by
  refine closure_mono (Function.support_subset_iff.mpr fun place nonzero => ?_)
  intro vanishes
  exact nonzero (by
    rw [SchwartzMap.smulLeftCLM_apply bump.hasTemperateGrowth]
    simp [vanishes])

theorem localize (agree : AgreeOn window first second) (bump : Bump Point)
    (supported : tsupport bump.weight ⊆ (window : Set Point)) :
    localize bump first = localize bump second := by
  ext probe
  rw [localize_eq, localize_eq, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  exact agree _ ((tsupport_smulLeftCLM_subset bump probe).trans supported)

/-- **Agreement on a window transfers interior smoothness.**  Everything the
framework proves about the bridged object on a region inside the window is a
statement about the original one there. -/
theorem sobolevOn (agree : AgreeOn window first second) {region : Set Point}
    (region_subset : region ⊆ (window : Set Point)) {grade : ℝ}
    (smooth : SobolevOn region grade second) : SobolevOn region grade first :=
  SobolevOn.congr_localize
    (fun bump supported => agree.localize bump (supported.trans region_subset))
    smooth

theorem smoothOn (agree : AgreeOn window first second) {region : Set Point}
    (region_subset : region ⊆ (window : Set Point))
    (smooth : SmoothOn region second) : SmoothOn region first :=
  SmoothOn.congr_localize
    (fun bump supported => agree.localize bump (supported.trans region_subset))
    smooth

end AgreeOn

/-! ## The bridge, as an agreement

The connector of `Localization/TemperedBridge.lean` says exactly that
differentiating the bridged object and bridging the differentiated one agree on
the window.  Phrased that way it composes with everything above, so no operator
needs its own transport argument.
-/

section Bridge

variable (cutoff : 𝓓_{window}(Point, ℝ))
  (inside : (window : Set Point) ⊆ domain)

/-- **The bridge commutes with one derivative, up to agreement on the
window.** -/
theorem agreeOn_lineDerivOp_temperedOfLocal (local_ : 𝓓'(domain, Value))
    (direction : Point)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    AgreeOn window (∂_{direction} (temperedOfLocal cutoff inside local_))
      (temperedOfLocal cutoff inside
        ((Distribution.lineDerivCLM direction :
          𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) local_)) :=
  fun test supported =>
    temperedOfLocal_lineDerivOp_apply_of_eqOn_one cutoff inside local_ direction
      test supported unit

/-- **The bridge commutes with any string of derivatives, up to agreement.**
Gradient, divergence, curl, Laplacian and heat are finite linear combinations
of these, so each transports by this together with `AgreeOn.add`,
`AgreeOn.sub` and `AgreeOn.sum`. -/
theorem agreeOn_lineDerivs_temperedOfLocal (local_ : 𝓓'(domain, Value))
    (directions : List Point)
    (unit : ∀ place ∈ (window : Set Point), cutoff place = 1) :
    AgreeOn window
      (temperedLineDerivs directions (temperedOfLocal cutoff inside local_))
      (temperedOfLocal cutoff inside (localLineDerivs directions local_)) :=
  fun test supported =>
    temperedOfLocal_lineDerivs_apply_of_eqOn_one cutoff inside local_ directions
      unit test supported

end Bridge

end Hypostructure.PDE.Localization
