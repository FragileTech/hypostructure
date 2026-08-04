import Hypostructure.PDE.Object
import Hypostructure.PDE.Singularity

/-!
# The no-singularity target

The mirror of `Hypostructure/Graph/MinimumDegreeCycleTarget.lean`.  Graph gives
an application `Graph.minimumDegreeCycleTarget`, whose `Predicate` is the packed
executable cycle target and whose `Statement` is the pinned public proposition,
with **both transport directions framework-owned**.  An application registers
the target by calling it; it does not write a target bridge.

This module does the same for a local regularity problem.  The predicate is

> the field of the object has **no singularity** in its domain,

which by `PDE.singularSet_eq_empty_iff` is interior regularity, and the
statement is the same read over every object satisfying the baseline.  Both
directions are `fun statement object baseline => statement object baseline`:
there is nothing to prove, exactly as there is nothing to prove that a graph
has vertices.

No estimate appears anywhere in this file, and none can: the target is the
emptiness of a set that is *defined* by pointwise non-smoothness.  A strategy
closes it by exhibiting the singular set as empty, never by bounding anything.
-/

namespace Hypostructure.PDE

open MeasureTheory TopologicalSpace
open scoped ContDiff

universe v w

/-! ## The predicate -/

/--
**No singularity forms.**

The field carries no point of its domain at which it fails to be smooth.  This
is the packed executable target: `PDE.singularSet` is a set, and the predicate
is its emptiness, so deciding it is deciding a set is empty rather than
producing a bound.
-/
def NoSingularity {dimension : ℕ} {Value : Type w} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (μ : Measure (Place dimension))
    (object : FieldObject dimension Value) : Prop :=
  ∃ representative : Place dimension → Value,
    ContDiffOn ℝ ∞ representative (object.domain : Set (Place dimension)) ∧
    ∀ᵐ place ∂μ, place ∈ (object.domain : Set (Place dimension)) →
      object.field place = representative place

/--
**Why a representative and not the chosen function.**

`FieldObject.field` is a free field of the structure, and every hypothesis a
baseline can put on it --- representing a distribution, `AEStronglyMeasurable`,
`MemLp`, a normalization stated as an integral --- is invariant under changing
it on a null set, while `ContDiffOn ℝ ∞ object.field` is not.  Asking for the
chosen function to be smooth is therefore refutable: modify a smooth solution at
one point and every hypothesis survives while the conclusion fails.

The theorem an interior-regularity argument actually proves is that the
solution *has* a smooth representative --- which is what
`stokes:thm:global-normalized-representative` says, and what this predicate
asks.  Nothing downstream is weakened: a closure that produces a smooth chosen
function still closes, through `noSingularity_of_contDiffOn`.
-/
theorem noSingularity_of_contDiffOn {dimension : ℕ} {Value : Type w}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {μ : Measure (Place dimension)} {object : FieldObject dimension Value}
    (smooth : ContDiffOn ℝ ∞ object.field
      (object.domain : Set (Place dimension))) :
    NoSingularity μ object :=
  ⟨object.field, smooth, Filter.Eventually.of_forall fun _ _ => rfl⟩

/-- The chosen function's own smoothness, read as the target.  This is the
direction `singularSet_eq_empty_iff` still supplies. -/
theorem noSingularity_of_singularSet_eq_empty {dimension : ℕ} {Value : Type w}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {μ : Measure (Place dimension)} {object : FieldObject dimension Value}
    (empty : singularSet object.field
      (object.domain : Set (Place dimension)) = ∅) :
    NoSingularity μ object :=
  noSingularity_of_contDiffOn (singularSet_eq_empty_iff.mp empty)

/-- A singularity of an object that misses the target, produced by the
framework.  This is what makes the minimal counterexample of a regularity
problem a *singularity profile*.

Missing the target means *no* representative is smooth, so in particular the
object's own field function is not, and it has a genuine point of
non-smoothness. -/
theorem exists_singularity_of_not_target {dimension : ℕ} {Value : Type w}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {μ : Measure (Place dimension)} {object : FieldObject dimension Value}
    (avoids : ¬ NoSingularity μ object) :
    ∃ place ∈ (object.domain : Set (Place dimension)),
      ¬ ContDiffWithinAt ℝ ∞ object.field
        (object.domain : Set (Place dimension)) place :=
  exists_singular_point_of_not_contDiffOn
    fun smooth => avoids (noSingularity_of_contDiffOn smooth)

/-! ## The registered target

Mirrors `Graph.minimumDegreeCycleTarget`: the `Statement` is the public
proposition an application pins, the `Predicate` is the packed target, and both
bridges are owned here.
-/

/-- The public proposition of a local regularity problem: every object meeting
the baseline is free of singularities. -/
def NoSingularityStatement (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure (Place dimension))
    (Baseline : FieldObject dimension Value → Prop) : Prop :=
  ∀ object : FieldObject dimension Value, Baseline object → NoSingularity μ object

/--
**The Core target of a local regularity problem.**

Both transport directions are framework-owned, so an application registers its
target by calling this and writes no bridge of its own.  Mirrors
`Graph.minimumDegreeCycleTarget`.
-/
def noSingularityTarget (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure (Place dimension))
    (Baseline : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) :
    Core.Target
      (problemWithPresentation dimension Value Baseline BranchState
        Presentation presentation) where
  Predicate := NoSingularity μ
  Statement := NoSingularityStatement dimension Value μ Baseline
  statement_to_target := fun statement object baseline =>
    statement object baseline
  target_to_statement := fun closure object baseline =>
    closure object baseline

@[simp] theorem noSingularityTarget_predicate (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure (Place dimension))
    (Baseline : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation)
    (object : FieldObject dimension Value) :
    (noSingularityTarget dimension Value μ Baseline BranchState Presentation
      presentation).Predicate object = NoSingularity μ object := rfl

end Hypostructure.PDE
