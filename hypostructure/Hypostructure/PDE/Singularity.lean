import Mathlib
import Hypostructure.PDE.Focus

/-!
# The singularity a target-avoiding residual carries

Core's minimal-counterexample selection hands the PDE layer an
`ActiveResidual`: an object that satisfies the baseline and **avoids** the
target.  When the target is interior regularity, avoiding it is not an abstract
fact --- it names a point.

`ContDiffOn ℝ ∞ f s` *is* `∀ x ∈ s, ContDiffWithinAt ℝ ∞ f s x`, by definition
and not by a theorem.  So the negation of interior regularity hands back a
point of the region at which the field is not smooth, with no analysis at all.
That point is the singularity, and it is where the whole local chain is
centred: `PointLocalization.site` built from this module returns it, so every
window the framework derives is a window *around the blowup*, not around an
arbitrary point of the domain.

Nothing here is an estimate, a scale, or a rate.  A singularity in this module
is exactly "a point at which smoothness fails", and the only content is that
such a point exists whenever smoothness fails somewhere.
-/

namespace Hypostructure.PDE

open scoped ContDiff

universe u v w

/-! ## Where smoothness fails -/

section SingularSet

variable {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/--
**Failure of interior regularity names a point.**

`ContDiffOn` unfolds to the pointwise family, so this is `not_forall` twice and
nothing else.  In particular no compactness, no covering and no limit is used,
which is what makes it usable at the very start of a localization.
-/
theorem exists_singular_point_of_not_contDiffOn {field : Place → Value}
    {region : Set Place} (fails : ¬ ContDiffOn ℝ ∞ field region) :
    ∃ point ∈ region, ¬ ContDiffWithinAt ℝ ∞ field region point := by
  by_contra absent
  exact fails fun point mem => not_not.mp fun rough => absent ⟨point, mem, rough⟩

/-- The singular set of a field on a region: the points of the region at which
it is not smooth. -/
def singularSet (field : Place → Value) (region : Set Place) : Set Place :=
  {point ∈ region | ¬ ContDiffWithinAt ℝ ∞ field region point}

theorem mem_singularSet {field : Place → Value} {region : Set Place}
    {point : Place} :
    point ∈ singularSet field region ↔
      point ∈ region ∧ ¬ ContDiffWithinAt ℝ ∞ field region point :=
  Iff.rfl

/-- **Interior regularity is exactly an empty singular set.**  This is the
statement that makes "the minimal counterexample is a singularity" literal. -/
theorem singularSet_eq_empty_iff {field : Place → Value} {region : Set Place} :
    singularSet field region = ∅ ↔ ContDiffOn ℝ ∞ field region := by
  constructor
  · intro empty point mem
    by_contra rough
    exact absurd (Set.eq_empty_iff_forall_notMem.mp empty point) fun absent =>
      absent ⟨mem, rough⟩
  · intro smooth
    refine Set.eq_empty_iff_forall_notMem.mpr fun point singular => ?_
    exact singular.2 (smooth point singular.1)

theorem singularSet_nonempty_of_not_contDiffOn {field : Place → Value}
    {region : Set Place} (fails : ¬ ContDiffOn ℝ ∞ field region) :
    (singularSet field region).Nonempty := by
  obtain ⟨point, mem, rough⟩ := exists_singular_point_of_not_contDiffOn fails
  exact ⟨point, mem, rough⟩

end SingularSet

/-! ## Reading a registered target as interior regularity

A `SingularityProfile` says how a model's target is a smoothness statement:
which field, on which region, and how a point of that region names a point of
the atlas.  It proves nothing about the equation --- `regularity_of_smooth` is
the one direction a localization needs, namely that smoothness *implies* the
target, so that avoiding the target refutes smoothness.
-/

variable {M : LocalModel.{u}} {T : Core.Target M.problem}

/--
**How a registered target is read as interior regularity of a field.**

Supplying one of these is what lets the framework centre every window on the
singularity.  It is model data, in the same sense as the atlas: no analytic
content, and no claim that the field solves anything.
-/
structure SingularityProfile (M : LocalModel.{u}) (T : Core.Target M.problem)
    (Place : Type v) [NormedAddCommGroup Place] [NormedSpace ℝ Place]
    (Value : Type w) [NormedAddCommGroup Value] [NormedSpace ℝ Value] where
  /-- The field whose smoothness the target asserts. -/
  field : M.problem.Ambient → Place → Value
  /-- The region on which it is asserted. -/
  region : M.problem.Ambient → Set Place
  /-- How a point of that region names a point of the atlas. -/
  place : Place → M.atlas.Point
  /-- Smoothness of the field on the region gives the registered target.  Only
  this direction is used: it is what turns target avoidance into a singular
  point.

  The baseline is available because a target usually asserts more than
  smoothness of the one field --- a regularity target for a balanced system
  also asserts a smooth pressure gradient, and the equation is what names it
  (`PDE.Distribution.exists_contDiffOn_representative_of_balance`).  Passing
  the baseline is what lets that be discharged framework-side instead of by
  every application. -/
  regularity_of_smooth : ∀ (object : M.problem.Ambient),
    M.problem.Baseline object →
    ContDiffOn ℝ ∞ (field object) (region object) → T.Predicate object

namespace SingularityProfile

variable {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  (profile : SingularityProfile M T Place Value)

/-- An object that satisfies the baseline and avoids the target has a singular
point. -/
theorem exists_singular {object : M.problem.Ambient}
    (baseline : M.problem.Baseline object) (avoids : ¬ T.Predicate object) :
    ∃ point ∈ profile.region object,
      ¬ ContDiffWithinAt ℝ ∞ (profile.field object) (profile.region object) point :=
  exists_singular_point_of_not_contDiffOn fun smooth =>
    avoids (profile.regularity_of_smooth object baseline smooth)

/--
**The singularity of an object.**

Total, so it can be a field of `PointLocalization`; its defining property is
available exactly when the object avoids the target, which is what an
`ActiveResidual` carries.
-/
noncomputable def singularPoint (object : M.problem.Ambient) : Place :=
  Classical.epsilon fun point =>
    point ∈ profile.region object ∧
      ¬ ContDiffWithinAt ℝ ∞ (profile.field object) (profile.region object) point

theorem singularPoint_spec {object : M.problem.Ambient}
    (baseline : M.problem.Baseline object) (avoids : ¬ T.Predicate object) :
    profile.singularPoint object ∈ profile.region object ∧
      ¬ ContDiffWithinAt ℝ ∞ (profile.field object) (profile.region object)
        (profile.singularPoint object) := by
  obtain ⟨point, mem, rough⟩ := profile.exists_singular baseline avoids
  exact Classical.epsilon_spec (p := fun place =>
    place ∈ profile.region object ∧
      ¬ ContDiffWithinAt ℝ ∞ (profile.field object) (profile.region object) place)
    ⟨point, mem, rough⟩

theorem singularPoint_mem {object : M.problem.Ambient}
    (baseline : M.problem.Baseline object) (avoids : ¬ T.Predicate object) :
    profile.singularPoint object ∈ profile.region object :=
  (profile.singularPoint_spec baseline avoids).1

theorem not_contDiffWithinAt_singularPoint {object : M.problem.Ambient}
    (baseline : M.problem.Baseline object) (avoids : ¬ T.Predicate object) :
    ¬ ContDiffWithinAt ℝ ∞ (profile.field object) (profile.region object)
      (profile.singularPoint object) :=
  (profile.singularPoint_spec baseline avoids).2

theorem singularPoint_mem_singularSet {object : M.problem.Ambient}
    (baseline : M.problem.Baseline object) (avoids : ¬ T.Predicate object) :
    profile.singularPoint object ∈
      singularSet (profile.field object) (profile.region object) :=
  profile.singularPoint_spec baseline avoids

/-! ### The site of an active residual

`ActiveResidual.avoids` is stated against the residual's own `Target` field.
For the residuals Core's selection produces that field *is* `T.Predicate`
(`CounterexampleLocalization.activeResidual`), so `reads` below is `Iff.rfl`
at every call site the framework generates.
-/

/-- **The singularity of an active residual**, as a point of the atlas.  This
is the value a `PointLocalization.site` built from this profile returns. -/
noncomputable def site (residual : ActiveResidual M) : M.atlas.Point :=
  profile.place (profile.singularPoint residual.object)

/-- The site really is a point at which the field fails to be smooth, whenever
the residual avoids the registered target. -/
theorem site_singular (residual : ActiveResidual M)
    (reads : ∀ object, residual.Target object ↔ T.Predicate object) :
    profile.singularPoint residual.object ∈
      singularSet (profile.field residual.object) (profile.region residual.object) :=
  profile.singularPoint_mem_singularSet residual.baseline fun holds =>
    residual.avoids ((reads residual.object).mpr holds)

/-- The site lies in the region the target speaks about. -/
theorem site_mem_region (residual : ActiveResidual M)
    (reads : ∀ object, residual.Target object ↔ T.Predicate object) :
    profile.singularPoint residual.object ∈ profile.region residual.object :=
  (profile.site_singular residual reads).1

end SingularityProfile

end Hypostructure.PDE
