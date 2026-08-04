import Hypostructure.PDE.ParabolicAtlas
import Hypostructure.PDE.SpacetimeCoordinates

/-!
# The framework's standard parabolic atlas, in Euclidean coordinates

`Hypostructure.PDE.ParabolicAtlas` builds every parabolic space-time as a
binary product `ℝ × Space`.  That is the shape the geometry is written in, but
a binary product carries the supremum norm and therefore has no
`InnerProductSpace ℝ` instance --- while the whole regularity theory
(`Solution.ParabolicRegularity`, `Solution.InteriorRegularity`) is stated over
a point space with an inner product.

This module is the same atlas over `EuclideanSpace ℝ (Fin (dimension + 1))`,
which does have one, so that the atlas lives where the analysis lives.  Every
declaration here mirrors one of `ParabolicAtlas`, with a `Euclidean` prefix.

No geometry is reproved: the five facts about `euclideanParabolicRegion`
supplied by `Hypostructure.PDE.SpacetimeCoordinates` are the only geometric
input, and each of them is already the image of a product-space fact under the
linear homeomorphism `spacetimeCoordsL`.

There is no equation, residual, ledger, route or target anywhere in this file.
-/

namespace Hypostructure.PDE

open TopologicalSpace

/-! ## Euclidean parabolic cylinders -/

/-- A backward parabolic cylinder over `EuclideanSpace ℝ (Fin (dimension + 1))`:
the framework's standard local window, in the coordinates the regularity theory
uses.

Unlike `ParabolicCylinder`, whose `center` field is the *top* of the time
interval, `center` here is the point the window is taken around --- the
Euclidean window `euclideanParabolicRegion` is already the point-containing
one, and shifting the time coordinate back would mean re-deriving geometry in
coordinates rather than importing it. -/
structure EuclideanParabolicCylinder (dimension : ℕ) where
  center : EuclideanSpace ℝ (Fin (dimension + 1))
  radius : ℝ
  radius_pos : 0 < radius

namespace EuclideanParabolicCylinder

variable {dimension : ℕ}

/-- The open space-time region a cylinder represents. -/
def region (cylinder : EuclideanParabolicCylinder dimension) :
    Opens (EuclideanSpace ℝ (Fin (dimension + 1))) where
  carrier := euclideanParabolicRegion cylinder.center cylinder.radius
  is_open' := isOpen_euclideanParabolicRegion cylinder.center cylinder.radius

/-- The cylinder of radius `radius` around `point`. -/
def around (point : EuclideanSpace ℝ (Fin (dimension + 1))) {radius : ℝ}
    (positive : 0 < radius) : EuclideanParabolicCylinder dimension where
  center := point
  radius := radius
  radius_pos := positive

theorem around_region (point : EuclideanSpace ℝ (Fin (dimension + 1)))
    {radius : ℝ} (positive : 0 < radius) :
    ((around point positive).region :
        Set (EuclideanSpace ℝ (Fin (dimension + 1)))) =
      euclideanParabolicRegion point radius :=
  rfl

theorem mem_around (point : EuclideanSpace ℝ (Fin (dimension + 1)))
    {radius : ℝ} (positive : 0 < radius) :
    point ∈ (around point positive).region :=
  mem_euclideanParabolicRegion point positive

theorem convex_around (point : EuclideanSpace ℝ (Fin (dimension + 1)))
    {radius : ℝ} (positive : 0 < radius) :
    Convex ℝ ((around point positive).region :
      Set (EuclideanSpace ℝ (Fin (dimension + 1)))) :=
  convex_euclideanParabolicRegion point radius

end EuclideanParabolicCylinder

/-! ## The atlas and the model -/

/--
**The framework's standard parabolic atlas, in Euclidean coordinates.**

Windows are Euclidean parabolic cylinders and nesting is literal inclusion of
regions.  Local objects are the ambient objects themselves and restriction is
the identity, exactly as in `parabolicAtlas`: a represented equation remembers
its own presentation, so nothing is thrown away by restricting.

The point space is `EuclideanSpace ℝ (Fin (dimension + 1))`, which lives in
`Type 0`; the problem is therefore fixed at `Core.Problem.{0, 0}` rather than
being universe-polymorphic.
-/
abbrev euclideanParabolicAtlas (P : Core.Problem.{0, 0}) (dimension : ℕ) :
    LocalAtlas P where
  Point := EuclideanSpace ℝ (Fin (dimension + 1))
  Window := EuclideanParabolicCylinder dimension
  contains := fun point window => point ∈ window.region
  nested := fun small large => small.region ≤ large.region
  nested_refl := fun _ => le_rfl
  nested_trans := fun smallLarge largeAmbient => smallLarge.trans largeAmbient
  core := id
  core_nested := fun _ => le_rfl
  LocalObject := fun _ => P.Ambient
  restrict := fun object _ => object
  restrictLocal := fun _ object => object
  restrict_refl := fun _ _ => rfl
  restrict_trans := by intros; rfl
  restrict_global := by intros; rfl

/-- **The windows are open.**  This is the only hypothesis of the framework's
germ discharges (`LocalClosureAlgebra.Presentation.congruent_of_germ` and
`ofGerm_congruentAdmissible`) that mentions the atlas, and for the Euclidean
parabolic atlas it is the openness of a cylinder's own region. -/
theorem isOpen_euclideanParabolicContains (P : Core.Problem.{0, 0})
    (dimension : ℕ) (window : EuclideanParabolicCylinder dimension) :
    IsOpen {place | (euclideanParabolicAtlas P dimension).contains place window} :=
  window.region.isOpen

/-- The framework's Euclidean parabolic local model: a problem, the Euclidean
parabolic atlas over its space-time, and a represented equation. -/
abbrev euclideanParabolicModel {P : Core.Problem.{0, 0}} (dimension : ℕ)
    (equation : RepresentedEquation P (euclideanParabolicAtlas P dimension)) :
    LocalModel.{0} where
  problem := P
  atlas := euclideanParabolicAtlas P dimension
  equation := equation

/-! ## Localization, derived from the domain alone -/

section Localization

variable {P : Core.Problem.{0, 0}} {dimension : ℕ}
  (domain : P.Ambient → Opens (EuclideanSpace ℝ (Fin (dimension + 1))))

/-- The part of a window where the object is defined. -/
abbrev euclideanParabolicLocalDomain (object : P.Ambient)
    (window : EuclideanParabolicCylinder dimension) :
    Opens (EuclideanSpace ℝ (Fin (dimension + 1))) :=
  domain object ⊓ window.region

/-- **Admissibility**: the local carrier domain is convex.  This is what makes
local solvability unconditional on the window --- Malgrange applies with no
P-convexity side condition --- and it is the only thing a localization step
has to establish about the window it selects. -/
abbrev EuclideanParabolicAdmissible (object : P.Ambient)
    (window : EuclideanParabolicCylinder dimension) : Prop :=
  Convex ℝ
    ((euclideanParabolicLocalDomain domain object window :
        Opens (EuclideanSpace ℝ (Fin (dimension + 1)))) :
      Set (EuclideanSpace ℝ (Fin (dimension + 1))))

/-- Whether some cylinder around a point fits inside the object's domain. -/
def EuclideanCylinderFitsAt (object : P.Ambient)
    (point : EuclideanSpace ℝ (Fin (dimension + 1))) : Prop :=
  ∃ radius : ℝ, ∃ positive : 0 < radius,
    ((EuclideanParabolicCylinder.around point positive).region :
      Set (EuclideanSpace ℝ (Fin (dimension + 1)))) ⊆ domain object

/-- A cylinder fits around every point of the object's own (open) domain. -/
theorem euclideanCylinderFitsAt_of_mem {object : P.Ambient}
    {point : EuclideanSpace ℝ (Fin (dimension + 1))}
    (mem : point ∈ domain object) :
    EuclideanCylinderFitsAt domain object point := by
  obtain ⟨radius, positive, subset⟩ :=
    exists_euclideanParabolicRegion_subset (domain object).isOpen mem
  exact ⟨radius, positive, subset⟩

open scoped Classical in
/-- The window assigned to a point: one that fits inside the object's domain
whenever one does, and the unit cylinder otherwise (in which case the
intersection with the domain is empty and admissibility is vacuous). -/
noncomputable def euclideanCoverCylinder (object : P.Ambient)
    (point : EuclideanSpace ℝ (Fin (dimension + 1))) :
    EuclideanParabolicCylinder dimension :=
  if fits : EuclideanCylinderFitsAt domain object point then
    EuclideanParabolicCylinder.around point fits.choose_spec.choose
  else
    EuclideanParabolicCylinder.around point one_pos

theorem mem_euclideanCoverCylinder (object : P.Ambient)
    (point : EuclideanSpace ℝ (Fin (dimension + 1))) :
    point ∈ (euclideanCoverCylinder domain object point).region := by
  classical
  unfold euclideanCoverCylinder
  by_cases fits : EuclideanCylinderFitsAt domain object point
  · rw [dif_pos fits]
    exact EuclideanParabolicCylinder.mem_around _ _
  · rw [dif_neg fits]
    exact EuclideanParabolicCylinder.mem_around _ _

theorem euclideanCoverCylinder_admissible {object : P.Ambient}
    {point : EuclideanSpace ℝ (Fin (dimension + 1))}
    (mem : point ∈ domain object) :
    EuclideanParabolicAdmissible domain object
      (euclideanCoverCylinder domain object point) := by
  classical
  have fits : EuclideanCylinderFitsAt domain object point :=
    euclideanCylinderFitsAt_of_mem domain mem
  have cylinder_eq :
      euclideanCoverCylinder domain object point =
        EuclideanParabolicCylinder.around point fits.choose_spec.choose := by
    unfold euclideanCoverCylinder
    rw [dif_pos fits]
  have subset := fits.choose_spec.choose_spec
  have inf_eq :
      (euclideanParabolicLocalDomain domain object
          (euclideanCoverCylinder domain object point) :
          Opens (EuclideanSpace ℝ (Fin (dimension + 1)))) =
        (euclideanCoverCylinder domain object point).region := by
    rw [euclideanParabolicLocalDomain, inf_eq_right, cylinder_eq]
    exact subset
  show Convex ℝ _
  rw [inf_eq, cylinder_eq]
  exact EuclideanParabolicCylinder.convex_around _ _

/-! ### The base window of an active residual -/

variable (equation :
  RepresentedEquation P (euclideanParabolicAtlas P dimension))

/-- The site the localization works at: a point of the selected object's
domain.  It reads the active residual and nothing else. -/
noncomputable def euclideanParabolicSite
    (residual : ActiveResidual (euclideanParabolicModel dimension equation)) :
    EuclideanSpace ℝ (Fin (dimension + 1)) :=
  Classical.epsilon fun point => point ∈ domain residual.object

/-- The base window of the active residual, chosen after selection. -/
noncomputable def euclideanParabolicBase
    (residual : ActiveResidual (euclideanParabolicModel dimension equation)) :
    EuclideanParabolicCylinder dimension :=
  euclideanCoverCylinder domain residual.object
    (euclideanParabolicSite domain equation residual)

theorem mem_euclideanParabolicBase
    (residual : ActiveResidual (euclideanParabolicModel dimension equation)) :
    euclideanParabolicSite domain equation residual ∈
      (euclideanParabolicBase domain equation residual).region :=
  mem_euclideanCoverCylinder domain _ _

theorem euclideanParabolicBase_admissible
    (residual : ActiveResidual (euclideanParabolicModel dimension equation)) :
    EuclideanParabolicAdmissible domain residual.object
      (euclideanParabolicBase domain equation residual) := by
  classical
  rcases Set.eq_empty_or_nonempty
      ((domain residual.object :
          Opens (EuclideanSpace ℝ (Fin (dimension + 1)))) :
        Set (EuclideanSpace ℝ (Fin (dimension + 1)))) with
    empty | nonempty
  · have coe_empty :
        ((euclideanParabolicLocalDomain domain residual.object
            (euclideanParabolicBase domain equation residual) :
          Opens (EuclideanSpace ℝ (Fin (dimension + 1)))) :
            Set (EuclideanSpace ℝ (Fin (dimension + 1)))) = ∅ := by
      simp [euclideanParabolicLocalDomain, Opens.coe_inf, empty]
    show Convex ℝ _
    rw [coe_empty]
    exact convex_empty
  · have mem :
        euclideanParabolicSite domain equation residual ∈
          domain residual.object :=
      Classical.epsilon_spec
        (p := fun point => point ∈ domain residual.object) nonempty
    exact euclideanCoverCylinder_admissible domain mem

/--
**The whole point localization, derived.**

`PublicPresentation` consumes this, and every nested focus, tower and nesting
proof downstream of it is `NestedFocus.ofCoreTower`'s.  A domain supplies no
window, no admissibility proof and no localization theorem.
-/
noncomputable def euclideanParabolicPointLocalization :
    PointLocalization (euclideanParabolicModel dimension equation) where
  Admissible := EuclideanParabolicAdmissible domain
  site := euclideanParabolicSite domain equation
  base := euclideanParabolicBase domain equation
  point_mem_core_core := mem_euclideanParabolicBase domain equation
  base_admissible := euclideanParabolicBase_admissible domain equation

/-! ### Localizing at a preferred site

The site above is `Classical.epsilon`: *some* point of the domain.  A regularity
argument wants a *particular* one --- the singularity of the selected residual,
which `PDE/Singularity.lean` produces.

The obstruction to just using it is that `PointLocalization.base_admissible` is
quantified over **every** active residual, while a singular point is only known
to lie in the domain when the residual actually avoids the target.  So the site
below falls back: it uses the preferred point where that point is in the domain,
and the canonical one otherwise.  For a target-avoiding residual with a
singularity the fallback never fires, and for any other residual nothing was
claimed anyway.
-/

/-- The preferred site, guarded: the caller's point when it lies in the
object's domain, the canonical site otherwise. -/
noncomputable def euclideanParabolicPreferredSite
    (preferred : ActiveResidual (euclideanParabolicModel dimension equation) →
      EuclideanSpace ℝ (Fin (dimension + 1)))
    (residual : ActiveResidual (euclideanParabolicModel dimension equation)) :
    EuclideanSpace ℝ (Fin (dimension + 1)) :=
  open Classical in
  if preferred residual ∈ domain residual.object then preferred residual
  else euclideanParabolicSite domain equation residual

/-- Where the preferred point is admissible, the guarded site *is* it. -/
theorem euclideanParabolicPreferredSite_eq
    (preferred : ActiveResidual (euclideanParabolicModel dimension equation) →
      EuclideanSpace ℝ (Fin (dimension + 1)))
    {residual : ActiveResidual (euclideanParabolicModel dimension equation)}
    (mem : preferred residual ∈ domain residual.object) :
    euclideanParabolicPreferredSite domain equation preferred residual =
      preferred residual := by
  classical
  simp [euclideanParabolicPreferredSite, mem]

/--
**The point localization at a preferred site.**

Identical to `euclideanParabolicPointLocalization` except that the site is the
caller's where that is legitimate.  Feeding it
`PDE.Strategy.BalancedRegularity.site` centres every derived window on the
singularity of the selected residual.
-/
noncomputable def euclideanParabolicPointLocalizationAt
    (preferred : ActiveResidual (euclideanParabolicModel dimension equation) →
      EuclideanSpace ℝ (Fin (dimension + 1))) :
    PointLocalization (euclideanParabolicModel dimension equation) where
  Admissible := EuclideanParabolicAdmissible domain
  site := euclideanParabolicPreferredSite domain equation preferred
  base := fun residual =>
    euclideanCoverCylinder domain residual.object
      (euclideanParabolicPreferredSite domain equation preferred residual)
  point_mem_core_core := fun residual =>
    mem_euclideanCoverCylinder domain residual.object _
  base_admissible := fun residual => by
    classical
    by_cases mem : preferred residual ∈ domain residual.object
    · have site_eq :
          euclideanParabolicPreferredSite domain equation preferred residual =
            preferred residual :=
        euclideanParabolicPreferredSite_eq domain equation preferred mem
      rw [site_eq]
      exact euclideanCoverCylinder_admissible domain mem
    · have site_eq :
          euclideanParabolicPreferredSite domain equation preferred residual =
            euclideanParabolicSite domain equation residual := by
        simp [euclideanParabolicPreferredSite, mem]
      rw [site_eq]
      exact euclideanParabolicBase_admissible domain equation residual

/--
**The pointwise admissible-window selector, derived.**

This is the cover hypothesis of `LocalClosureAlgebra.target_of_exhaustion`,
discharged from the openness of the object's domain alone.
-/
noncomputable def euclideanParabolicCover :
    AdmissibleWindowCover (euclideanParabolicModel dimension equation)
      (EuclideanParabolicAdmissible domain)
      (fun object point => point ∈ domain object) where
  window := euclideanCoverCylinder domain
  admissible := fun _object _point mem =>
    euclideanCoverCylinder_admissible domain mem
  contains := fun object point _mem =>
    mem_euclideanCoverCylinder domain object point

end Localization

end Hypostructure.PDE
