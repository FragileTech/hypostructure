import Mathlib
import Hypostructure.PDE.DivCurl
import Hypostructure.PDE.Solution.ParabolicRegularity

/-!
# The first-order vector calculus on tempered distributions

`PDE/DivCurl.lean` builds the div–curl identity twice: once abstractly, as the
structure `CurlDivergenceCalculus`, and once concretely for *smooth* fields.
The concrete layer there is not usable by a consumer that works with states of
finite regularity, because every one of its statements carries a `ContDiff ℝ ∞`
hypothesis.  This module removes that hypothesis by moving the whole calculus
to tempered distributions, where it holds **unconditionally**.

## The one missing fact

Everything reduces to a single lemma, `lineDerivOp_comm`:

> `∂_{v} (∂_{w} T) = ∂_{w} (∂_{v} T)` for every tempered distribution `T`,
> with no hypothesis whatsoever.

Mathlib states the symmetry of second derivatives for functions, always under a
`C²` assumption, and it has no commutation lemma for `TemperedDistribution`.
The distributional statement is nevertheless *stronger*, in the sense that it
has no side condition, and the reason is the duality definition: `∂_{v}` on
distributions is the transpose of `-∂_{v}` on Schwartz test functions, so two
of them produce **two** minus signs, which cancel.  What is left is the
commutation of two derivatives of a Schwartz map — and a Schwartz map is smooth
by construction, so the `C²` hypothesis is discharged rather than assumed.

This mirrors `Hypostructure.PDE.Vorticity.derivativeCLM_comm`, which performs
the same cancellation for `Distribution.lineDerivCLM` on `𝓓'`.  The two files
are independent: that one lives on the compactly supported dual of a fixed open
set, this one on the tempered dual of the whole space, which is what the
Sobolev machinery of `PDE/Solution/` actually consumes.

## What the commutation buys

* `curl_curl` — `curl (curl v) = grad (div v) - Δ v`, for arbitrary
  distributional fields.  Proved once *in the index*, because `curl` is defined
  cyclically (`index + 1`, `index + 2` in `Fin 3`) exactly as in
  `PDE/DivCurl.lean`; the three components are three instances of one formula
  rather than three separate computations.
* `calculus` — the operators bundled as a `CurlDivergenceCalculus`, so that
  `neg_laplacian_eq_curl_curl` and the rest of the abstract layer apply to
  distributions verbatim.
* `curl_gradient` — `curl ∘ grad = 0`.
* `curl_lineDerivOp` — `curl` commutes with differentiation in *any* direction.
  A consumer working on a space–time domain gets the commutation with the time
  derivative from this instance, since there the time derivative is
  `lineDerivOp` along one more direction of the same space.
* `curl_laplacian` — `curl` commutes with the Laplacian.
* `curl_add`, `divergence_add`, `divergence_sub`, `gradient_add`,
  `laplacian_sub` — each operator is linear, so a consumer that splits a state
  into two parts may move all four operators across the split, not only the
  curl.  `divergence_gradient` and `laplacian_gradient` fix the relative
  normalization of the three scalar operators.
* `curl_smoothOn` — `curl` does not leave the class `SmoothOn` of
  `PDE/Solution/InteriorRegularity.lean`, so the output of the identity can be
  handed to a *local* regularity theorem and not only to a whole-space one.
* `laplacian_apply` — the bundle's Laplacian is, componentwise, the *ambient*
  `Δ` of `TemperedDistribution`.  This is the compatibility statement that lets
  the output of the identity be fed straight into the regularity theorems of
  `PDE/Solution/InteriorRegularity.lean` and
  `PDE/Solution/ParabolicRegularity.lean`, both of which are stated in terms of
  `Δ`.  It holds because mathlib's `Δ` is *defined* as the sum of the pure
  second `lineDerivOp`s over an orthonormal basis, and `laplacian_eq_sum` says
  that the sum is independent of which orthonormal basis is chosen.

## Why the frame is a bare family and not a basis

The frame enters every operator only through the three *directions*
`frame 0, frame 1, frame 2` that are differentiated along, and `lineDerivOp_comm`
holds for arbitrary directions.  So the whole calculus — the operators, the
vector identity, and every closure fact — asks nothing of `frame` beyond being
a function `Fin 3 → Point`: no orthonormality, no spanning, not even that the
three directions are distinct.  Declaring it as an `OrthonormalBasis` would
force `Point` to be three-dimensional, which would make the calculus unusable
on a space–time `Point`, where the three directions of interest span only a
proper subspace.  It is therefore declared as a bare family, and the two facts
that genuinely need more are quarantined into their own sections:

* `scalarLaplacian_eq` (§ *Compatibility with the ambient Laplacian*) needs the
  frame to be a **full** orthonormal basis of `Point`, since it identifies the
  frame sum with the ambient `Δ`, and that identification is simply false for a
  frame spanning a proper subspace.
* `scalarLaplacian_eq_spatialLaplacian` (§ *Compatibility with the spatial
  Laplacian*) needs the frame to consist of three members of an orthonormal
  basis of a possibly larger `Point`, together omitting exactly one
  distinguished index.  Then the frame sum is the *spatial* Laplacian of
  `PDE/Solution/ParabolicRegularity.lean`, which is the operator
  `PDE/Solution/SliceRestriction.lean` gains regularity from.

Neither statement is a hypothesis of anything else, so a consumer that needs
only the identity pays for neither.

The ambient space is any real normed space; the values are any complex normed
space.  Nothing here names a boundary condition, an equation, or a physical
quantity.
-/

namespace Hypostructure.PDE.Distribution.CurlCalculus

open TemperedDistribution LineDeriv
open Hypostructure.PDE.DivCurl (CurlDivergenceCalculus)
open scoped SchwartzMap LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

/-! ## Symmetry of second derivatives on Schwartz maps

A Schwartz map is smooth, so Clairaut's theorem applies to it with no
hypothesis to discharge.  The translation from mathlib's `fderiv`-shaped
statement to the `lineDerivOp` form used by the distribution API is the only
work: a line derivative is the Fréchet derivative evaluated at the direction,
and differentiating such an evaluation is evaluating the second differential.
-/

section Symmetry

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {Target : Type uValue} [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- Two nested line derivatives of a Schwartz map are the second Fréchet
derivative evaluated at the two directions.

Isolating this is what lets mathlib's symmetry theorem — which is stated for
`fderiv (fderiv f)` — be applied to a nest of two `lineDerivOp`s.  The step
that is not definitional is differentiating `fun place => fderiv ℝ f place m`,
an evaluation of a continuous linear map at a constant argument, which is
`fderiv_clm_apply`. -/
theorem schwartzMap_lineDerivOp_lineDerivOp_apply
    (outer inner : Point) (test : 𝓢(Point, Target)) (place : Point) :
    (∂_{outer} (∂_{inner} test) : 𝓢(Point, Target)) place =
      fderiv ℝ (fderiv ℝ (⇑test)) place outer inner := by
  have secondDifferentiable : DifferentiableAt ℝ (fderiv ℝ (⇑test)) place :=
    ((test.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) place
  have expand := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ (⇑test))
    (u := fun _ : Point => inner) (x := place) secondDifferentiable (differentiableAt_const inner)
  show fderiv ℝ (fun other => fderiv ℝ (⇑test) other inner) place outer = _
  rw [expand]
  simp

/-- **Line derivatives of a Schwartz map commute.**  Unconditionally: the
smoothness that Clairaut's theorem requires is part of the definition of a
Schwartz map, so there is no hypothesis left for a caller to supply.  This is
the sole analytic input to everything below. -/
theorem schwartzMap_lineDerivOp_comm (first second : Point) (test : 𝓢(Point, Target)) :
    (∂_{first} (∂_{second} test) : 𝓢(Point, Target)) = ∂_{second} (∂_{first} test) := by
  refine DFunLike.ext _ _ fun place => ?_
  rw [schwartzMap_lineDerivOp_lineDerivOp_apply, schwartzMap_lineDerivOp_lineDerivOp_apply]
  exact ((test.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)) first second

end Symmetry

/-! ## Symmetry of second derivatives on tempered distributions

The distributional derivative is the transpose of the negated test-function
derivative.  Two of them therefore contribute two minus signs, which cancel,
and the statement collapses to the Schwartz-level commutation above — with the
`C²` hypothesis already discharged there.  So the distributional commutation is
a theorem with *no* side condition, which is exactly what makes the calculus
below unconditional.
-/

section DistributionSymmetry

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {Value : Type uValue} [AddCommGroup Value] [Module ℂ Value] [TopologicalSpace Value]
  [IsTopologicalAddGroup Value] [ContinuousConstSMul ℂ Value]

/-- **Distributional derivatives commute.**

There is no regularity hypothesis, and none is possible to need: the
distribution is only ever evaluated, and the two derivatives that were moved
onto the test function commute because test functions are smooth.  The two
duality minus signs cancel, which is why the statement is an equality rather
than an equality up to sign.

This is the lemma mathlib does not have for `TemperedDistribution`, and it is
the only new mathematical content of this module. -/
theorem lineDerivOp_comm (first second : Point) (state : 𝓢'(Point, Value)) :
    (∂_{first} (∂_{second} state) : 𝓢'(Point, Value)) = ∂_{second} (∂_{first} state) := by
  ext test
  show (∂_{second} state : 𝓢'(Point, Value)) (-∂_{first} test) = _
  show state (-∂_{second} (-∂_{first} test)) = state (-∂_{first} (-∂_{second} test))
  rw [lineDerivOp_neg, lineDerivOp_neg, neg_neg, neg_neg,
    schwartzMap_lineDerivOp_comm second first test]

/-- Differentiation is subtractive.  Mathlib supplies additivity and negation
separately; the difference is what every component of a curl is built from. -/
theorem lineDerivOp_sub (direction : Point) (first second : 𝓢'(Point, Value)) :
    (∂_{direction} (first - second) : 𝓢'(Point, Value)) =
      ∂_{direction} first - ∂_{direction} second := by
  rw [sub_eq_add_neg, lineDerivOp_add, lineDerivOp_neg, ← sub_eq_add_neg]

end DistributionSymmetry

/-! ## The coordinate operators

The four classical operators, in coordinates against a fixed frame of three
directions.  As in `PDE/DivCurl.lean` the curl is written *cyclically* — its
`index`-th component uses the directions `index + 1` and `index + 2` — and that
is not cosmetic: it makes each component a single instance of one formula, so
the vector identity is proved once in the index instead of three times by
cases.

The frame is a bare family `Fin 3 → Point`.  Everything in this section is
`lineDerivOp_comm` and index bookkeeping, and `lineDerivOp_comm` holds for two
arbitrary directions of an arbitrary real normed space, so no orthonormality,
no spanning and no finite dimensionality is available here — and none is
needed.  The gain is that `Point` may be strictly larger than the span of the
frame, which is what a space–time consumer requires.
-/

section Calculus

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  (frame : Fin 3 → Point)

/-- A sum over `Fin 3` may be started at any index: the three summands
`axis`, `axis + 1`, `axis + 2` exhaust the index type in every case.  Stating
this once is what removes the case split from the identity below, since both
the divergence and the Laplacian have to be re-expanded around whichever
component is being computed. -/
theorem sum_fin_three_eq_from {Carrier : Type*} [AddCommMonoid Carrier]
    (term : Fin 3 → Carrier) (axis : Fin 3) :
    ∑ index, term index = term axis + term (axis + 1) + term (axis + 2) := by
  fin_cases axis <;> simp [Fin.sum_univ_three] <;> abel

/-- The rotational operator: `(curl v)_i = ∂_{i+1} v_{i+2} - ∂_{i+2} v_{i+1}`,
with indices read cyclically in `Fin 3`.  In the standard orientation the two
directions used are exactly the two axes other than `i`, so this is the
classical curl. -/
noncomputable def curl (field : Fin 3 → 𝓢'(Point, Value)) : Fin 3 → 𝓢'(Point, Value) :=
  fun index =>
    ∂_{frame (index + 1)} (field (index + 2)) - ∂_{frame (index + 2)} (field (index + 1))

/-- The trace of the first derivative, `div v = ∑ᵢ ∂ᵢ vᵢ`. -/
noncomputable def divergence (field : Fin 3 → 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  ∑ index, ∂_{frame index} (field index)

/-- The gradient of a scalar state, `(grad p)_i = ∂ᵢ p`. -/
noncomputable def gradient (scalar : 𝓢'(Point, Value)) : Fin 3 → 𝓢'(Point, Value) :=
  fun index => ∂_{frame index} scalar

/-- The Laplacian of a scalar state, `Δ p = ∑ᵢ ∂ᵢ ∂ᵢ p`, written out in the
chosen frame.  `scalarLaplacian_eq` identifies it with the ambient `Δ`. -/
noncomputable def scalarLaplacian (scalar : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  ∑ axis, ∂_{frame axis} (∂_{frame axis} scalar)

/-- The Laplacian of a field, componentwise. -/
noncomputable def laplacian (field : Fin 3 → 𝓢'(Point, Value)) : Fin 3 → 𝓢'(Point, Value) :=
  fun index => scalarLaplacian frame (field index)

variable {frame}

/-! ### The vector identity -/

/-- One component of the double curl, fully expanded and with the two mixed
second derivatives already commuted into the order the right-hand side of the
identity produces.  This is the only place `lineDerivOp_comm` is used in the
proof of `curl_curl`, and it is used exactly twice.

The index bookkeeping — `(i+2)+1 = i`, `(i+2)+2 = i+1`, `(i+1)+1 = i+2`,
`(i+1)+2 = i` — is decidable in `Fin 3` and is discharged in one `decide`. -/
theorem curl_curl_apply (field : Fin 3 → 𝓢'(Point, Value)) (index : Fin 3) :
    curl frame (curl frame field) index =
      (∂_{frame index} (∂_{frame (index + 1)} (field (index + 1)))
          - ∂_{frame (index + 1)} (∂_{frame (index + 1)} (field index)))
        + (∂_{frame index} (∂_{frame (index + 2)} (field (index + 2)))
          - ∂_{frame (index + 2)} (∂_{frame (index + 2)} (field index))) := by
  have rotate : ∀ axis : Fin 3,
      axis + 2 + 1 = axis ∧ axis + 2 + 2 = axis + 1 ∧
        axis + 1 + 1 = axis + 2 ∧ axis + 1 + 2 = axis := by decide
  obtain ⟨shiftTwoOne, shiftTwoTwo, shiftOneOne, shiftOneTwo⟩ := rotate index
  show ∂_{frame (index + 1)} (curl frame field (index + 2))
      - ∂_{frame (index + 2)} (curl frame field (index + 1)) = _
  show ∂_{frame (index + 1)}
        (∂_{frame (index + 2 + 1)} (field (index + 2 + 2))
          - ∂_{frame (index + 2 + 2)} (field (index + 2 + 1)))
      - ∂_{frame (index + 2)}
        (∂_{frame (index + 1 + 1)} (field (index + 1 + 2))
          - ∂_{frame (index + 1 + 2)} (field (index + 1 + 1))) = _
  rw [shiftTwoOne, shiftTwoTwo, shiftOneOne, shiftOneTwo, lineDerivOp_sub, lineDerivOp_sub,
    lineDerivOp_comm (frame (index + 1)) (frame index) (field (index + 1)),
    lineDerivOp_comm (frame (index + 2)) (frame index) (field (index + 2))]
  abel

/-- The right-hand side of the identity, expanded in the same component and in
the same shape.  Both the divergence and the Laplacian are re-summed starting
at `index`, and the two pure second derivatives `∂ᵢ∂ᵢ vᵢ` cancel between them —
which is why the identity carries no zeroth-order term. -/
theorem gradient_divergence_sub_laplacian_apply (field : Fin 3 → 𝓢'(Point, Value))
    (index : Fin 3) :
    (gradient frame (divergence frame field) - laplacian frame field) index =
      (∂_{frame index} (∂_{frame (index + 1)} (field (index + 1)))
          - ∂_{frame (index + 1)} (∂_{frame (index + 1)} (field index)))
        + (∂_{frame index} (∂_{frame (index + 2)} (field (index + 2)))
          - ∂_{frame (index + 2)} (∂_{frame (index + 2)} (field index))) := by
  have gradientExpansion : gradient frame (divergence frame field) index =
      ∂_{frame index} (∂_{frame index} (field index))
        + ∂_{frame index} (∂_{frame (index + 1)} (field (index + 1)))
        + ∂_{frame index} (∂_{frame (index + 2)} (field (index + 2))) := by
    show ∂_{frame index} (∑ axis, ∂_{frame axis} (field axis)) = _
    rw [lineDerivOp_sum]
    exact sum_fin_three_eq_from (fun axis => ∂_{frame index} (∂_{frame axis} (field axis))) index
  have laplacianExpansion : laplacian frame field index =
      ∂_{frame index} (∂_{frame index} (field index))
        + ∂_{frame (index + 1)} (∂_{frame (index + 1)} (field index))
        + ∂_{frame (index + 2)} (∂_{frame (index + 2)} (field index)) :=
    sum_fin_three_eq_from (fun axis => ∂_{frame axis} (∂_{frame axis} (field index))) index
  rw [Pi.sub_apply, gradientExpansion, laplacianExpansion]
  abel

/-- **The vector identity for distributions**, `curl (curl v) = grad (div v) - Δ v`,
equivalently `-Δ v = curl (curl v) - grad (div v)`.

Unlike its smooth counterpart in `PDE/DivCurl.lean` this carries no regularity
hypothesis at all, because `lineDerivOp_comm` carries none.  That is the whole
gain: a consumer holding only a distributional field may still perform the
div–curl reduction, and only afterwards ask an elliptic theory for regularity. -/
theorem curl_curl (field : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (curl frame field) =
      gradient frame (divergence frame field) - laplacian frame field := by
  funext index
  rw [curl_curl_apply field index, gradient_divergence_sub_laplacian_apply field index]

/-! ### The remaining closure facts

Each is again `lineDerivOp_comm` and nothing else.  `curl_componentwise` is the
common shape: an operator acting one component at a time passes through the
curl as soon as it is subtractive and commutes with each directional
derivative.
-/

/-- **The rotational operator is additive.**

Each component is a difference of two directional derivatives, and a
directional derivative on distributions is additive, so a sum passes through
untouched.  A consumer that presents a field as a sum — a particular state plus
a correction, or a state plus its own regularization — needs exactly this to
split the rotational datum along the same decomposition, since without it the
two summands can only be handled together. -/
theorem curl_add (first second : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (first + second) = curl frame first + curl frame second := by
  funext index
  show ∂_{frame (index + 1)} (first (index + 2) + second (index + 2))
      - ∂_{frame (index + 2)} (first (index + 1) + second (index + 1)) = _
  show _ = (∂_{frame (index + 1)} (first (index + 2))
        - ∂_{frame (index + 2)} (first (index + 1)))
      + (∂_{frame (index + 1)} (second (index + 2))
        - ∂_{frame (index + 2)} (second (index + 1)))
  rw [lineDerivOp_add, lineDerivOp_add]
  abel

/-- The rotational operator is subtractive, for the same reason `curl_add` is
additive: each component is a difference of directional derivatives, and
`lineDerivOp_sub` moves a difference through one.

This is what lets a gauge move --- replacing a state by that state minus a
gradient --- be read on the rotational datum, which is where
`curl_sub_gradient` gets its "the curl does not see the gauge" conclusion. -/
theorem curl_sub (first second : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (first - second) = curl frame first - curl frame second := by
  funext index
  show ∂_{frame (index + 1)} (first (index + 2) - second (index + 2))
      - ∂_{frame (index + 2)} (first (index + 1) - second (index + 1)) = _
  show _ = (∂_{frame (index + 1)} (first (index + 2))
        - ∂_{frame (index + 2)} (first (index + 1)))
      - (∂_{frame (index + 1)} (second (index + 2))
        - ∂_{frame (index + 2)} (second (index + 1)))
  rw [lineDerivOp_sub, lineDerivOp_sub]
  abel

/-- The rotational operator annihilates the zero field. -/
@[simp] theorem curl_zero : curl frame (0 : Fin 3 → 𝓢'(Point, Value)) = 0 := by
  funext index
  show ∂_{frame (index + 1)} (0 : 𝓢'(Point, Value))
    - ∂_{frame (index + 2)} (0 : 𝓢'(Point, Value)) = 0
  simp

/-- The gradient annihilates the zero scalar. -/
@[simp] theorem gradient_zero : gradient frame (0 : 𝓢'(Point, Value)) = 0 := by
  funext index
  exact lineDerivOp_zero _

/-- **`curl ∘ grad = 0`.**  Each component is the difference of the two orders
of the same pair of derivatives, so it vanishes by `lineDerivOp_comm`.  This is
also the check that the cyclic definition of `curl` is the classical one and
not a degenerate combination. -/
theorem curl_gradient (scalar : 𝓢'(Point, Value)) :
    curl frame (gradient frame scalar) = 0 := by
  funext index
  show ∂_{frame (index + 1)} (∂_{frame (index + 2)} scalar)
    - ∂_{frame (index + 2)} (∂_{frame (index + 1)} scalar) = 0
  rw [lineDerivOp_comm (frame (index + 1)) (frame (index + 2)) scalar, sub_self]

/-- An operator applied one component at a time passes through the curl,
provided it is subtractive and commutes with every directional derivative.

Both remaining closure facts are instances: a directional derivative and the
Laplacian both act componentwise, and both commute with directional
derivatives. -/
theorem curl_componentwise (operator : 𝓢'(Point, Value) → 𝓢'(Point, Value))
    (subtractive : ∀ first second : 𝓢'(Point, Value),
      operator (first - second) = operator first - operator second)
    (commutes : ∀ (direction : Point) (state : 𝓢'(Point, Value)),
      operator (∂_{direction} state) = ∂_{direction} (operator state))
    (field : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (fun index => operator (field index)) =
      fun index => operator (curl frame field index) := by
  funext index
  show ∂_{frame (index + 1)} (operator (field (index + 2)))
      - ∂_{frame (index + 2)} (operator (field (index + 1)))
    = operator (∂_{frame (index + 1)} (field (index + 2))
      - ∂_{frame (index + 2)} (field (index + 1)))
  rw [subtractive, commutes, commutes]

/-- **The curl commutes with differentiation in any direction.**

The direction is arbitrary and need not belong to the frame, so a consumer
working on a space–time domain obtains the commutation with the *time*
derivative from this one statement: there the time derivative is `lineDerivOp`
along one further direction of the same ambient space, and the argument does
not distinguish it from a spatial one. -/
theorem curl_lineDerivOp (direction : Point) (field : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (fun index => ∂_{direction} (field index)) =
      fun index => ∂_{direction} (curl frame field index) :=
  curl_componentwise (fun state => ∂_{direction} state) (lineDerivOp_sub direction)
    (fun other state => lineDerivOp_comm direction other state) field

/-- The scalar Laplacian is subtractive: it is a finite sum of iterated
derivatives, each of which is. -/
theorem scalarLaplacian_sub (first second : 𝓢'(Point, Value)) :
    scalarLaplacian frame (first - second) =
      scalarLaplacian frame first - scalarLaplacian frame second := by
  show ∑ axis, ∂_{frame axis} (∂_{frame axis} (first - second)) = _
  show _ = ∑ axis, ∂_{frame axis} (∂_{frame axis} first)
    - ∑ axis, ∂_{frame axis} (∂_{frame axis} second)
  simp only [lineDerivOp_sub]
  rw [Finset.sum_sub_distrib]

/-- The scalar Laplacian commutes with differentiation in any direction: two
applications of `lineDerivOp_comm` inside a finite sum. -/
theorem scalarLaplacian_lineDerivOp (direction : Point) (scalar : 𝓢'(Point, Value)) :
    scalarLaplacian frame (∂_{direction} scalar) =
      ∂_{direction} (scalarLaplacian frame scalar) := by
  show ∑ axis, ∂_{frame axis} (∂_{frame axis} (∂_{direction} scalar))
    = ∂_{direction} (∑ axis, ∂_{frame axis} (∂_{frame axis} scalar))
  rw [lineDerivOp_sum]
  refine Finset.sum_congr rfl fun axis _ => ?_
  rw [lineDerivOp_comm (frame axis) direction scalar,
    lineDerivOp_comm (frame axis) direction (∂_{frame axis} scalar)]

/-! ### Linearity of the remaining operators

The curl is the only operator whose linearity needed an index computation; for
the other three it is a finite sum of linear operators, so the content is
`Finset.sum_sub_distrib` and `Finset.sum_add_distrib` and nothing else.  They
are recorded because a consumer that decomposes a state — into a particular
part and a correction, or into a state and its regularization — has to move
each of the four operators across the decomposition, and there is no reason for
the curl to be the only one it can move.
-/

/-- The divergence is subtractive: a finite sum of subtractive operators. -/
theorem divergence_sub (first second : Fin 3 → 𝓢'(Point, Value)) :
    divergence frame (first - second) =
      divergence frame first - divergence frame second := by
  show ∑ index, ∂_{frame index} ((first - second) index) = _
  show _ = ∑ index, ∂_{frame index} (first index)
    - ∑ index, ∂_{frame index} (second index)
  simp only [Pi.sub_apply, lineDerivOp_sub]
  rw [Finset.sum_sub_distrib]

/-- The divergence is additive: a finite sum of additive operators. -/
theorem divergence_add (first second : Fin 3 → 𝓢'(Point, Value)) :
    divergence frame (first + second) =
      divergence frame first + divergence frame second := by
  show ∑ index, ∂_{frame index} ((first + second) index) = _
  show _ = ∑ index, ∂_{frame index} (first index)
    + ∑ index, ∂_{frame index} (second index)
  simp only [Pi.add_apply, lineDerivOp_add]
  rw [Finset.sum_add_distrib]

/-- The gradient is additive, componentwise. -/
theorem gradient_add (first second : 𝓢'(Point, Value)) :
    gradient frame (first + second) = gradient frame first + gradient frame second := by
  funext index
  show ∂_{frame index} (first + second) =
    ∂_{frame index} first + ∂_{frame index} second
  rw [lineDerivOp_add]

/-- The vector Laplacian is subtractive, componentwise. -/
theorem laplacian_sub (first second : Fin 3 → 𝓢'(Point, Value)) :
    laplacian frame (first - second) = laplacian frame first - laplacian frame second := by
  funext index
  exact scalarLaplacian_sub (first index) (second index)

/-! ### The relative normalization of the three scalar operators -/

/-- **`div ∘ grad = Δ`.**  The relative normalization of the three operators is
fixed by their definitions rather than by a convention, so this is definitional.
Recording it is what lets a consumer read a statement about the frame Laplacian
of a scalar as a statement about the divergence of its gradient, and conversely:
`div (grad p) = 0` and `Δ p = 0` are then literally the same proposition, not
two propositions related by an unfolding step the consumer has to perform. -/
theorem divergence_gradient (scalar : 𝓢'(Point, Value)) :
    divergence frame (gradient frame scalar) = scalarLaplacian frame scalar := rfl

/-- **`Δ ∘ grad = grad ∘ Δ`.**  The vector Laplacian of a gradient is the
gradient of the scalar Laplacian: this is `scalarLaplacian_lineDerivOp` read one
component at a time, the direction of that commutation being the frame
direction of the component.  It is the reason a potential annihilated by the
scalar Laplacian has a gradient annihilated by the vector one. -/
theorem laplacian_gradient (scalar : 𝓢'(Point, Value)) :
    laplacian frame (gradient frame scalar) =
      gradient frame (scalarLaplacian frame scalar) := by
  funext index
  exact scalarLaplacian_lineDerivOp (frame index) scalar

/-- **The curl commutes with the Laplacian.** -/
theorem curl_laplacian (field : Fin 3 → 𝓢'(Point, Value)) :
    curl frame (laplacian frame field) = laplacian frame (curl frame field) :=
  curl_componentwise (scalarLaplacian frame) scalarLaplacian_sub
    scalarLaplacian_lineDerivOp field

variable (frame)

/-- **The distributional div–curl calculus.**

The coordinate operators on `Fin 3 → 𝓢'(Point, Value)` realize the abstract
`CurlDivergenceCalculus` of `PDE/DivCurl.lean`, so every consequence proved
there — in particular `neg_laplacian_eq_curl_curl`, the reduction of a
divergence-free field to a vector Poisson equation driven by its rotational
datum — applies to distributions with no regularity hypothesis.

Note that no submodule of "sufficiently smooth" states has to be carved out
here, unlike `DivCurl.smoothCalculus`: the identity holds on the whole space,
so the group of the structure is the full function type. -/
noncomputable def calculus :
    CurlDivergenceCalculus (Fin 3 → 𝓢'(Point, Value)) (𝓢'(Point, Value)) where
  curl := curl frame
  divergence := divergence frame
  gradient := gradient frame
  laplacian := laplacian frame
  curl_curl_eq := curl_curl
  curl_zero := curl_zero
  gradient_zero := gradient_zero

end Calculus

/-! ## Compatibility with the ambient Laplacian

The regularity theorems of `PDE/Solution/` are stated in terms of mathlib's
`Δ` on tempered distributions, never in terms of a frame.  For the identity
above to be usable by them, the bundle's Laplacian must *be* that `Δ`, and it
is: mathlib defines `Δ` as the sum of the pure second `lineDerivOp`s over the
standard orthonormal basis, and `laplacian_eq_sum` records that the sum is the
same for every orthonormal basis.  So the agreement is a rewriting step, not a
new theorem, which is exactly the situation one wants.

Finite dimensionality is required only here — it is what makes `Δ` exist — and
is therefore introduced only in this section, as is the inner product structure
and the requirement that the frame be a full orthonormal **basis**.  That last
requirement is not a convenience: if the frame spanned a proper subspace the
frame sum would omit the missing directions, and the statement below would be
false.  This is precisely why the frame binder of the calculus itself is a bare
family — the one result that needs a basis asks for it here, and only here, so
that consumers on a higher-dimensional `Point` are not blocked by it.
-/

section Compatibility

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  (frame : OrthonormalBasis (Fin 3) ℝ Point)

/-- The scalar Laplacian written in a full orthonormal basis of the ambient
space is the ambient `Δ`. -/
theorem scalarLaplacian_eq (scalar : 𝓢'(Point, Value)) :
    scalarLaplacian (⇑frame) scalar = Δ scalar :=
  (TemperedDistribution.laplacian_eq_sum frame scalar).symm

/-- **The bundle's Laplacian is the ambient one, componentwise.**  This is the
statement a consumer needs in order to feed `curl (curl v)` — or `-Δ v`, after
`neg_laplacian_eq_curl_curl` — to an interior or parabolic regularity theorem,
both of which speak about `Δ`. -/
theorem laplacian_apply (field : Fin 3 → 𝓢'(Point, Value)) (index : Fin 3) :
    laplacian (⇑frame) field index = Δ (field index) :=
  scalarLaplacian_eq frame (field index)

/-- The same statement for the bundled calculus, which is the form in which the
abstract consequences deliver it. -/
theorem calculus_laplacian_apply (field : Fin 3 → 𝓢'(Point, Value)) (index : Fin 3) :
    (calculus (⇑frame)).laplacian field index = Δ (field index) :=
  laplacian_apply frame field index

end Compatibility

/-! ## Compatibility with the spatial Laplacian

The other situation a consumer is in: `Point` is a space–time, an orthonormal
basis of it is fixed, one index of that basis is distinguished as the time
direction, and the frame consists of the remaining three.  The regularity
theory that applies there — `spatialLaplacian` of
`PDE/Solution/ParabolicRegularity.lean`, consumed by
`PDE/Solution/SliceRestriction.lean` — is stated as the sum of the pure second
derivatives over `Finset.univ.erase timeIndex`, an unordered sum over a
sub-`Finset` of the basis index type.

The frame sum, by contrast, runs over `Fin 3` in a chosen order.  So the two
agree for exactly one reason — reindexing — and the hypothesis that makes the
reindexing available is that the three frame members are the images of a map
`Fin 3 → Index` which is injective and whose image is exactly the complement of
the time index.  Nothing analytic happens here; the content is that the *shape*
of the two sums can be matched at all, which is what lets `curl_curl` be fed to
`spatialSmoothOn_of_spatialLaplacian_smoothOn`.

Note what is *not* claimed: the frame sum is not the ambient `Δ`.  On a
space–time it differs from it by the pure second time derivative, and that is
the whole point of the spatial theory.
-/

section SpatialCompatibility

open Hypostructure.PDE.Solution.ParabolicRegularity (spatialLaplacian)

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **The frame-written Laplacian of a spatial frame is the spatial Laplacian.**

`spatialIndex` selects the three spatial members of an orthonormal basis of a
space–time `Point`; `injective` and `exhausts` say that the selection hits each
non-time index exactly once, which is exactly what a reindexing of the sum
needs.  No orthonormality is used — the basis is only ever evaluated — but the
statement is phrased for an `OrthonormalBasis` because `spatialLaplacian` is,
and because a consumer arrives holding one.

This is the bridge that lets the distributional div–curl identity be handed to
the spatial regularity theorems of `PDE/Solution/SliceRestriction.lean`. -/
theorem scalarLaplacian_eq_spatialLaplacian (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (spatialIndex : Fin 3 → Index)
    (injective : Function.Injective spatialIndex)
    (exhausts : Finset.image spatialIndex Finset.univ = Finset.univ.erase timeIndex)
    (scalar : 𝓢'(Point, Value)) :
    scalarLaplacian (fun axis => basis (spatialIndex axis)) scalar =
      spatialLaplacian basis timeIndex scalar := by
  show ∑ axis, ∂_{basis (spatialIndex axis)} (∂_{basis (spatialIndex axis)} scalar) = _
  rw [spatialLaplacian, ← exhausts,
    Finset.sum_image fun first _ second _ equal => injective equal]

/-- The same statement with the image condition replaced by the two facts a
consumer actually has at hand on a four-dimensional space–time: the three
spatial directions are distinct, none of them is the time direction, and the
basis has four members.  The image is then forced, because a three-element
subset of a three-element set is the whole of it. -/
theorem scalarLaplacian_eq_spatialLaplacian_of_card_eq_four
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (spatialIndex : Fin 3 → Index) (injective : Function.Injective spatialIndex)
    (avoidsTime : ∀ axis, spatialIndex axis ≠ timeIndex)
    (dimension : Fintype.card Index = 4) (scalar : 𝓢'(Point, Value)) :
    scalarLaplacian (fun axis => basis (spatialIndex axis)) scalar =
      spatialLaplacian basis timeIndex scalar := by
  refine scalarLaplacian_eq_spatialLaplacian basis timeIndex spatialIndex injective ?_ scalar
  have contained : Finset.image spatialIndex Finset.univ ⊆ Finset.univ.erase timeIndex :=
    fun index member => by
      obtain ⟨axis, _, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_erase.mpr ⟨avoidsTime axis, Finset.mem_univ _⟩
  have imageCard : (Finset.image spatialIndex Finset.univ).card = 3 := by
    rw [Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_fin]
  have eraseCard : (Finset.univ.erase timeIndex).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, dimension]
  exact Finset.eq_of_subset_of_card_le contained (by rw [imageCard, eraseCard])

end SpatialCompatibility

/-! ## Compatibility with local smoothness

The output of the identity is only useful to a consumer that can then say
something about the *regularity* of what it produced, and the regularity
predicate the local theory speaks in is `SmoothOn` of
`PDE/Solution/InteriorRegularity.lean` — every Sobolev grade on a window.  The
one fact needed is that the curl does not leave that class, and it does not,
for a reason that is specific to smoothness rather than to any single grade: a
first-order operator costs exactly one grade (`SobolevOn.lineDerivOp`), and a
state that holds *every* grade can pay that cost from the grade one higher, so
the cost is invisible.

Nothing here is a cycle: `SmoothOn` reaches this module through
`PDE/Solution/ParabolicRegularity.lean`, which is already imported for
`spatialLaplacian` above, and neither of those files knows about this one.  Both
facts the proof needs — `SmoothOn.sub` and `SmoothOn.lineDerivOp` — belong to
`InteriorRegularity`'s own API, so nothing about the class is restated here.
-/

section LocalSmoothness

open Hypostructure.PDE.Solution.InteriorRegularity (SmoothOn)

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value] {frame : Fin 3 → Point}

/-- **The curl preserves smoothness on a window.**

Each component is a difference of two directional derivatives.  A directional
derivative costs one grade, and smoothness is every grade at once, so each
derivative is paid for out of the grade one higher and the difference is taken
inside the class.  This is the statement that lets the output of `curl_curl` be
handed to a local regularity theorem without first proving a grade-by-grade
bookkeeping lemma at the call site. -/
theorem curl_smoothOn {region : Set Point} {field : Fin 3 → 𝓢'(Point, Value)}
    (smooth : ∀ index, SmoothOn region (field index)) (index : Fin 3) :
    SmoothOn region (curl frame field index) :=
  ((smooth (index + 2)).lineDerivOp (frame (index + 1))).sub
    ((smooth (index + 1)).lineDerivOp (frame (index + 2)))

end LocalSmoothness

end Hypostructure.PDE.Distribution.CurlCalculus
