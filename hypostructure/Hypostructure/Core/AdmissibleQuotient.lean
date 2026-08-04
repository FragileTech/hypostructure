import Hypostructure.Core.Problem

/-!
# Admissible rank quotients

Domain-generic formalization of `def:admissible-rank-quotient`'s closed
clause: a quotient on a family of declared coordinates -- an abstract
finite identification map, `value : Coordinate -> Value` -- is *admissible*
exactly when it is either label-injective (identifies no two distinct
coordinates) or witnessed by a strictly smaller representative retaining
the registered baseline.  This is the paper's own dichotomy, not an
invented generalization of it: the paper states the closed case exactly
this way ("an admissible rank quotient must be label-injective... unless it
is represented by a strictly smaller admissible closed representative").

The only input this needs from a problem is a bare exclusion fact --
`∀ subobject, ¬ Baseline (toAmbient subobject)` -- for whatever notion of
"smaller representative" (`Subobject`) that problem already uses.  Any
problem that has already built a minimality certificate for its own
`Subobject` (`Core.Minimality.NoSubobjectBaselineCertificate.excludes`,
`Graph.Minimality.NoProperBaselineCertificate.excludes`, or a PDE analogue)
gets `AdmissibleQuotient.injective_of_minimal` for free: no new
mathematics, only assembly. -/

namespace Hypostructure.Core

universe uSubobject uCoordinate uValue

variable {Ambient : Type*} {Baseline : Ambient -> Prop}
  {Subobject : Type uSubobject} {toAmbient : Subobject -> Ambient}

/-- An admissible rank quotient at `object`: a finite identification map on
some coordinate family that is either label-injective outright, or is
witnessed by a certified representative retaining the registered baseline
(`def:admissible-rank-quotient`'s closed dichotomy). -/
inductive AdmissibleQuotient
    (toAmbient : Subobject -> Ambient) (Baseline : Ambient -> Prop)
    (Coordinate : Type uCoordinate) (Value : Type uValue)
    (value : Coordinate -> Value) : Type (max uSubobject uCoordinate uValue)
  where
  /-- The quotient forgets and identifies nothing: label-injective. -/
  | injective (injective : Function.Injective value) :
      AdmissibleQuotient toAmbient Baseline Coordinate Value value
  /-- The quotient is rank-reducing, but only because a certified
  representative witnesses it -- the paper's "represented by a strictly
  smaller admissible closed representative" clause. -/
  | representative (subobject : Subobject)
      (baseline : Baseline (toAmbient subobject)) :
      AdmissibleQuotient toAmbient Baseline Coordinate Value value

/-- At an object where no certified representative can retain the
baseline, every admissible rank quotient is forced to be label-injective:
the `representative` case is exactly what such an exclusion fact rules
out.  Pure assembly -- zero new mathematics beyond whatever exclusion fact
the problem already has (e.g. a minimality certificate at the selected
minimal counterexample). -/
theorem AdmissibleQuotient.injective_of_excluded
    (excludes : ∀ subobject : Subobject, ¬ Baseline (toAmbient subobject))
    {Coordinate : Type uCoordinate} {Value : Type uValue}
    {value : Coordinate -> Value}
    (quotient : AdmissibleQuotient toAmbient Baseline Coordinate Value value) :
    Function.Injective value := by
  cases quotient with
  | injective injective => exact injective
  | representative subobject baseline =>
      exact absurd baseline (excludes subobject)

/-- Restated in the paper's own vocabulary: given the exclusion fact, an
admissible rank quotient is never rank-reducing (`rank-reducing` is exactly
`Not (Function.Injective value)` by `def:exact-response-profile`'s own
definition). This is `lem:no-silent-global-smearing`'s case-(c) conclusion
in full: the closed exact-response-profile argument the paper spends a
full proof on is, once phrased at this generality, an immediate corollary
of a minimality certificate any problem already has to build anyway. -/
theorem AdmissibleQuotient.not_rankReducing_of_excluded
    (excludes : ∀ subobject : Subobject, ¬ Baseline (toAmbient subobject))
    {Coordinate : Type uCoordinate} {Value : Type uValue}
    {value : Coordinate -> Value}
    (quotient : AdmissibleQuotient toAmbient Baseline Coordinate Value value) :
    ¬ ¬ Function.Injective value :=
  not_not_intro (quotient.injective_of_excluded excludes)

/-! ## Curvature target-rank

`def:curvature-target-rank` defines `r_Ω` as the size of the largest
independently target-testable subfamily of raw coordinates, and
`lem:full-rank`'s conclusion `r_Ω(R) = W_2(R)` says exactly that this
subfamily is the *whole* coordinate family, i.e. that whatever quotient
computes the rank is injective on all of it.  Once phrased with `rank` as
the cardinality of `value`'s image (the standard notion for a finite
identification map), `lem:full-rank` is the same corollary as
`not_rankReducing_of_excluded`, now stated as an equality of cardinalities
rather than a bare injectivity fact -- still zero new mathematics beyond
the exclusion fact any problem already builds.

What this section does *not* supply, and what remains genuinely
problem-specific: which concrete type plays `Coordinate` (the paper's raw
internal length-two curvature tests, `W_2(R)`) and which concrete map plays
`value` (a candidate admissible rank quotient on them).  That is real
graph-theoretic content (`def:exact-response-profile`'s declared-coordinate
signature), not something derivable from `Ambient`/`Baseline` alone. -/

/-- The rank of a finite identification map: the cardinality of its image,
i.e. the size of the largest subfamily it does not collapse. -/
noncomputable def AdmissibleQuotient.rank
    {Coordinate : Type uCoordinate} {Value : Type uValue}
    (value : Coordinate -> Value) : Nat :=
  Nat.card (Set.range value)

/-- Full rank (no coordinate lost to any identification) is exactly
injectivity, for a finite coordinate family. -/
theorem AdmissibleQuotient.rank_eq_card_iff_injective
    {Coordinate : Type uCoordinate} [Finite Coordinate] {Value : Type uValue}
    (value : Coordinate -> Value) :
    AdmissibleQuotient.rank value = Nat.card Coordinate ↔
      Function.Injective value := by
  unfold AdmissibleQuotient.rank
  constructor
  · intro hrank
    classical
    letI : Fintype Coordinate := Fintype.ofFinite Coordinate
    have hrange_finite : (Set.range value).Finite := Set.finite_range value
    letI : Fintype (Set.range value) := hrange_finite.fintype
    have hcard : Fintype.card (Set.range value) = Fintype.card Coordinate := by
      rw [← Nat.card_eq_fintype_card (α := Set.range value),
        ← Nat.card_eq_fintype_card (α := Coordinate)]
      exact hrank
    have hbij : Function.Bijective (Set.rangeFactorization value) :=
      (Fintype.bijective_iff_surjective_and_card _).mpr
        ⟨Set.rangeFactorization_surjective, hcard.symm⟩
    intro a b hab
    exact hbij.injective (Subtype.ext hab)
  · intro hinj
    exact Nat.card_congr (Equiv.ofInjective value hinj).symm

/-- `lem:full-rank`, fully generic: at an object where no certified
representative can retain the baseline, an admissible rank quotient always
achieves full rank -- the exact coordinate count, not merely `W_2(R) -
o(W_2(R))` as the paper's asymptotic statement allows, since this is the
sharp finite fact underneath it.  Zero new mathematics beyond the same
exclusion fact `not_rankReducing_of_excluded` already consumes. -/
theorem AdmissibleQuotient.rank_eq_card_of_excluded
    (excludes : ∀ subobject : Subobject, ¬ Baseline (toAmbient subobject))
    {Coordinate : Type uCoordinate} [Finite Coordinate] {Value : Type uValue}
    {value : Coordinate -> Value}
    (quotient : AdmissibleQuotient toAmbient Baseline Coordinate Value value) :
    AdmissibleQuotient.rank value = Nat.card Coordinate :=
  (AdmissibleQuotient.rank_eq_card_iff_injective value).mpr
    (quotient.injective_of_excluded excludes)

end Hypostructure.Core
