import Hypostructure.PDE.NoSingularityTarget

/-!
# Local smooth representatives patch to one global representative

The window machinery delivers, for each ball compactly contained in the domain,
a genuine `ContDiff` function representing the field there.  The registered
target asks for **one** function, smooth on the whole domain, agreeing with the
field almost everywhere.  This module is the passage between the two, and it
contains no analysis: only the observation that two continuous functions which
agree almost everywhere on an open set agree on it (`Measure.eqOn_of_ae_eq`,
available because an open set has positive measure), plus a countable subcover.

Nothing here is specific to a PDE.  It is the reason a local closure argument
can be stated purely on balls and still discharge a domain-wide target.
-/

namespace Hypostructure.PDE.Solution.RepresentativeGluing

open MeasureTheory Metric Set

universe uPoint uValue

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/--
**Almost-everywhere agreement on an open set is agreement on it**, for
continuous functions.  An open set is not null, so the set where two continuous
functions differ — open in the subspace — cannot be null unless it is empty.
-/
theorem eqOn_of_ae_eq_of_isOpen (μ : Measure Point) [μ.IsOpenPosMeasure]
    {region : Set Point} (open_ : IsOpen region)
    {first second : Point → Value}
    (agrees : ∀ᵐ place ∂μ, place ∈ region → first place = second place)
    (firstCont : ContinuousOn first region)
    (secondCont : ContinuousOn second region) :
    EqOn first second region := by
  have restricted : first =ᵐ[μ.restrict region] second := by
    rw [Filter.EventuallyEq, ae_restrict_iff' open_.measurableSet]
    exact agrees
  refine Measure.eqOn_of_ae_eq restricted firstCont secondCont ?_
  rw [open_.interior_eq]
  exact subset_closure

/--
**Two local representatives of the same field agree on the overlap of their
windows.**  Both are continuous there and both agree with the field almost
everywhere there, so the previous theorem applies to the intersection.
-/
theorem eqOn_inter_of_representatives (μ : Measure Point) [μ.IsOpenPosMeasure]
    {field first second : Point → Value}
    {left right : Set Point} (leftOpen : IsOpen left) (rightOpen : IsOpen right)
    (firstCont : ContinuousOn first left) (secondCont : ContinuousOn second right)
    (firstAgrees : ∀ᵐ place ∂μ, place ∈ left → field place = first place)
    (secondAgrees : ∀ᵐ place ∂μ, place ∈ right → field place = second place) :
    EqOn first second (left ∩ right) := by
  refine eqOn_of_ae_eq_of_isOpen μ (leftOpen.inter rightOpen) ?_
    (firstCont.mono inter_subset_left) (secondCont.mono inter_subset_right)
  filter_upwards [firstAgrees, secondAgrees] with place fromLeft fromRight member
  rw [← fromLeft member.1, fromRight member.2]

/--
**The local data a window family delivers**: a ball around every point of the
region, and a representative of the field on it.

This is a record of what the window machinery already produces, not a new
hypothesis: `radius` is the window it chose, `represent` is the `ContDiff`
function `LocalEmbedding.exists_contDiff_representative_of_smoothOn_ball`
returned, and `agrees` is the representation statement that came with it.
-/
structure LocalRepresentatives (μ : Measure Point) (region : Set Point)
    (field : Point → Value) where
  /-- The radius of the window chosen at each point. -/
  radius : Point → ℝ
  /-- Each window is a genuine ball. -/
  radius_pos : ∀ place ∈ region, 0 < radius place
  /-- Each window sits inside the region. -/
  ball_subset : ∀ place ∈ region, ball place (radius place) ⊆ region
  /-- The representative attached to each window. -/
  represent : Point → Point → Value
  /-- It is smooth on its window. -/
  smooth : ∀ place ∈ region,
    ContDiffOn ℝ ⊤ (represent place) (ball place (radius place))
  /-- …and represents the field there. -/
  agrees : ∀ place ∈ region, ∀ᵐ spot ∂μ,
    spot ∈ ball place (radius place) → field spot = represent place spot

namespace LocalRepresentatives

variable {μ : Measure Point} [μ.IsOpenPosMeasure]
  {region : Set Point} {field : Point → Value}
  (data : LocalRepresentatives μ region field)

/-- The windows cover the region. -/
theorem mem_own_ball {place : Point} (member : place ∈ region) :
    place ∈ ball place (data.radius place) :=
  mem_ball_self (data.radius_pos place member)

/-- **Any two windows' representatives agree on their overlap.** -/
theorem eqOn_overlap {left right : Point} (leftMember : left ∈ region)
    (rightMember : right ∈ region) :
    EqOn (data.represent left) (data.represent right)
      (ball left (data.radius left) ∩ ball right (data.radius right)) :=
  eqOn_inter_of_representatives μ isOpen_ball isOpen_ball
    (data.smooth left leftMember).continuousOn
    (data.smooth right rightMember).continuousOn
    (data.agrees left leftMember) (data.agrees right rightMember)

open Classical in
/-- The patched function: at each point, the representative of some window
containing it.  `eqOn_overlap` is what makes the choice immaterial. -/
noncomputable def glued (spot : Point) : Value :=
  if witness : ∃ place, place ∈ region ∧ spot ∈ ball place (data.radius place) then
    data.represent witness.choose spot
  else 0

/-- **The patched function is the representative of every window containing the
point** — the well-definedness statement. -/
theorem glued_eq {place spot : Point} (member : place ∈ region)
    (inside : spot ∈ ball place (data.radius place)) :
    data.glued spot = data.represent place spot := by
  classical
  have witness : ∃ chosen, chosen ∈ region ∧
      spot ∈ ball chosen (data.radius chosen) := ⟨place, member, inside⟩
  rw [glued, dif_pos witness]
  exact data.eqOn_overlap witness.choose_spec.1 member
    ⟨witness.choose_spec.2, inside⟩

/-- **The patched function is smooth on the whole region.**  Smoothness on an
open set is a local property, and on each window the patched function *is* that
window's representative. -/
theorem contDiffOn_glued : ContDiffOn ℝ ⊤ data.glued region := by
  intro spot member
  have onBall : ContDiffOn ℝ ⊤ data.glued (ball spot (data.radius spot)) :=
    (data.smooth spot member).congr fun _other inside => data.glued_eq member inside
  exact (onBall.contDiffAt
    (isOpen_ball.mem_nhds (data.mem_own_ball member))).contDiffWithinAt

/-- **The patched function represents the field almost everywhere on the
region.**  The windows cover it, second countability gives a countable
subcover, and a countable union of null sets is null. -/
theorem ae_eq_glued :
    ∀ᵐ spot ∂μ, spot ∈ region → field spot = data.glued spot := by
  classical
  obtain ⟨chosen, countable, cover⟩ :=
    TopologicalSpace.isOpen_iUnion_countable
      (fun place : region => ball (place : Point) (data.radius place))
      (fun _ => isOpen_ball)
  haveI : Countable chosen := countable.to_subtype
  have pieces : ∀ place : chosen, ∀ᵐ spot ∂μ,
      spot ∈ ball ((place : region) : Point) (data.radius (place : region)) →
        field spot = data.glued spot := by
    intro place
    filter_upwards [data.agrees (place : region) (place : region).2] with spot same inside
    rw [same inside, data.glued_eq (place : region).2 inside]
  filter_upwards [ae_all_iff.mpr pieces] with spot every member
  have covered : spot ∈ ⋃ place : region, ball (place : Point) (data.radius place) :=
    mem_iUnion.mpr ⟨⟨spot, member⟩, data.mem_own_ball member⟩
  rw [← cover, mem_iUnion₂] at covered
  obtain ⟨place, inChosen, inside⟩ := covered
  exact every ⟨place, inChosen⟩ inside

/--
**The payoff.**  A field with a local smooth representative around every point
of an open region has one smooth representative on the whole region, agreeing
with it almost everywhere — which is exactly the shape
`PDE.NoSingularity` asks for.
-/
theorem exists_contDiffOn_representative
    (family : LocalRepresentatives μ region field) :
    ∃ representative : Point → Value,
      ContDiffOn ℝ ⊤ representative region ∧
      ∀ᵐ spot ∂μ, spot ∈ region → field spot = representative spot :=
  ⟨family.glued, family.contDiffOn_glued, family.ae_eq_glued⟩

end LocalRepresentatives

end Hypostructure.PDE.Solution.RepresentativeGluing
