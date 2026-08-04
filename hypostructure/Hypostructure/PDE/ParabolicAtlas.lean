import Hypostructure.PDE.Focus
import Hypostructure.PDE.EllipticLocalTail
import Hypostructure.PDE.Distribution.Local

/-!
# The framework's standard parabolic atlas

Every parabolic PDE localizes the same way: the windows are backward parabolic
cylinders over a space-time `ℝ × Space`, a window is admissible when the part
of it where the object lives is convex, and every point of an object's open
domain sits inside such a window.

All of that is geometry, not equation data, so the framework owns it.  A
domain supplies exactly one function --- *where each ambient object lives* ---
and receives the atlas, the model, the point localization consumed by
`PublicPresentation`, and the `AdmissibleWindowCover` that discharges the
cover hypothesis of the exhaustive local closure.  It proves nothing.

There is no equation, residual, ledger, route or target anywhere in this file.
-/

namespace Hypostructure.PDE

open TopologicalSpace

universe u

/-! ## Parabolic cylinders -/

/-- A backward parabolic cylinder over `ℝ × Space`: the framework's standard
local window. -/
structure ParabolicCylinder (Space : Type u) [NormedAddCommGroup Space]
    [NormedSpace Real Space] where
  center : Real × Space
  radius : Real
  radius_pos : 0 < radius

namespace ParabolicCylinder

variable {Space : Type u} [NormedAddCommGroup Space] [NormedSpace Real Space]

/-- The open space-time region a cylinder represents. -/
def region (cylinder : ParabolicCylinder Space) : Opens (Real × Space) where
  carrier :=
    Set.Ioo (cylinder.center.1 - cylinder.radius ^ 2) cylinder.center.1 ×ˢ
      Metric.ball cylinder.center.2 cylinder.radius
  is_open' := isOpen_Ioo.prod Metric.isOpen_ball

/-- The cylinder of radius `radius` around `point`.  Its time interval ends
half a parabolic unit after `point`, so a backward window contains the point
it is taken around. -/
noncomputable def around (point : Real × Space) {radius : Real} (positive : 0 < radius) :
    ParabolicCylinder Space where
  center := (point.1 + radius ^ 2 / 2, point.2)
  radius := radius
  radius_pos := positive

theorem around_region (point : Real × Space) {radius : Real}
    (positive : 0 < radius) :
    ((around point positive).region : Set (Real × Space)) =
      Distribution.parabolicRegion point radius :=
  rfl

theorem mem_around (point : Real × Space) {radius : Real}
    (positive : 0 < radius) : point ∈ (around point positive).region :=
  Distribution.mem_parabolicRegion point positive

theorem convex_around (point : Real × Space) {radius : Real}
    (positive : 0 < radius) :
    Convex Real ((around point positive).region : Set (Real × Space)) :=
  Distribution.convex_parabolicRegion point radius

end ParabolicCylinder

/-! ## The atlas and the model -/

/--
**The framework's standard parabolic atlas.**

Windows are parabolic cylinders and nesting is literal inclusion of regions.
Local objects are the ambient objects themselves and restriction is the
identity: a represented equation remembers its own presentation, so nothing is
thrown away by restricting, and the analytic content lives in the window a
predicate is stated on rather than in a truncation of the object.
-/
abbrev parabolicAtlas (P : Core.Problem.{u, u}) (Space : Type u)
    [NormedAddCommGroup Space] [NormedSpace Real Space] : LocalAtlas P where
  Point := Real × Space
  Window := ParabolicCylinder Space
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
`ofGerm_congruentAdmissible`) that mentions the atlas, and for the standard
parabolic atlas it is the openness of a cylinder's own region. -/
theorem isOpen_parabolicContains (P : Core.Problem.{u, u}) (Space : Type u)
    [NormedAddCommGroup Space] [NormedSpace Real Space]
    (window : ParabolicCylinder Space) :
    IsOpen {place | (parabolicAtlas P Space).contains place window} :=
  window.region.isOpen

/-- The framework's parabolic local model: a problem, the standard parabolic
atlas over its space-time, and a represented equation. -/
abbrev parabolicModel {P : Core.Problem.{u, u}} (Space : Type u)
    [NormedAddCommGroup Space] [NormedSpace Real Space]
    (equation : RepresentedEquation P (parabolicAtlas P Space)) :
    LocalModel.{u} where
  problem := P
  atlas := parabolicAtlas P Space
  equation := equation

/-! ## Localization, derived from the domain alone -/

section Localization

variable {P : Core.Problem.{u, u}} {Space : Type u}
  [NormedAddCommGroup Space] [NormedSpace Real Space]
  (domain : P.Ambient → Opens (Real × Space))

/-- The part of a window where the object is defined. -/
abbrev parabolicLocalDomain (object : P.Ambient)
    (window : ParabolicCylinder Space) : Opens (Real × Space) :=
  domain object ⊓ window.region

/-- **Admissibility**: the local carrier domain is convex.  This is what makes
local solvability unconditional on the window --- Malgrange applies with no
P-convexity side condition --- and it is the only thing a localization step
has to establish about the window it selects. -/
abbrev ParabolicAdmissible (object : P.Ambient)
    (window : ParabolicCylinder Space) : Prop :=
  Convex Real
    ((parabolicLocalDomain domain object window : Opens (Real × Space)) :
      Set (Real × Space))

/-- Whether some cylinder around a point fits inside the object's domain. -/
def CylinderFitsAt (object : P.Ambient) (point : Real × Space) : Prop :=
  ∃ radius : Real, ∃ positive : 0 < radius,
    ((ParabolicCylinder.around point positive).region : Set (Real × Space)) ⊆
      domain object

/-- A cylinder fits around every point of the object's own (open) domain. -/
theorem cylinderFitsAt_of_mem {object : P.Ambient} {point : Real × Space}
    (mem : point ∈ domain object) : CylinderFitsAt domain object point := by
  obtain ⟨radius, positive, subset⟩ :=
    Distribution.exists_parabolicRegion_subset (domain object).isOpen mem
  exact ⟨radius, positive, subset⟩

open scoped Classical in
/-- The window assigned to a point: one that fits inside the object's domain
whenever one does, and the unit cylinder otherwise (in which case the
intersection with the domain is empty and admissibility is vacuous). -/
noncomputable def coverCylinder (object : P.Ambient)
    (point : Real × Space) : ParabolicCylinder Space :=
  if fits : CylinderFitsAt domain object point then
    ParabolicCylinder.around point fits.choose_spec.choose
  else
    ParabolicCylinder.around point one_pos

theorem mem_coverCylinder (object : P.Ambient) (point : Real × Space) :
    point ∈ (coverCylinder domain object point).region := by
  classical
  unfold coverCylinder
  by_cases fits : CylinderFitsAt domain object point
  · rw [dif_pos fits]
    exact ParabolicCylinder.mem_around _ _
  · rw [dif_neg fits]
    exact ParabolicCylinder.mem_around _ _

theorem coverCylinder_admissible {object : P.Ambient} {point : Real × Space}
    (mem : point ∈ domain object) :
    ParabolicAdmissible domain object (coverCylinder domain object point) := by
  classical
  have fits : CylinderFitsAt domain object point :=
    cylinderFitsAt_of_mem domain mem
  have cylinder_eq :
      coverCylinder domain object point =
        ParabolicCylinder.around point fits.choose_spec.choose := by
    unfold coverCylinder
    rw [dif_pos fits]
  have subset := fits.choose_spec.choose_spec
  have inf_eq :
      (parabolicLocalDomain domain object (coverCylinder domain object point) :
          Opens (Real × Space)) =
        (coverCylinder domain object point).region := by
    rw [parabolicLocalDomain, inf_eq_right, cylinder_eq]
    exact subset
  show Convex Real _
  rw [inf_eq, cylinder_eq]
  exact ParabolicCylinder.convex_around _ _

/-! ### The base window of an active residual -/

variable (equation : RepresentedEquation P (parabolicAtlas P Space))

/-- The site the localization works at: a point of the selected object's
domain.  It reads the active residual and nothing else. -/
noncomputable def parabolicSite
    (residual : ActiveResidual (parabolicModel Space equation)) :
    Real × Space :=
  Classical.epsilon fun point => point ∈ domain residual.object

/-- The base window of the active residual, chosen after selection. -/
noncomputable def parabolicBase
    (residual : ActiveResidual (parabolicModel Space equation)) :
    ParabolicCylinder Space :=
  coverCylinder domain residual.object (parabolicSite domain equation residual)

theorem mem_parabolicBase
    (residual : ActiveResidual (parabolicModel Space equation)) :
    parabolicSite domain equation residual ∈
      (parabolicBase domain equation residual).region :=
  mem_coverCylinder domain _ _

theorem parabolicBase_admissible
    (residual : ActiveResidual (parabolicModel Space equation)) :
    ParabolicAdmissible domain residual.object
      (parabolicBase domain equation residual) := by
  classical
  rcases Set.eq_empty_or_nonempty
      ((domain residual.object : Opens (Real × Space)) :
        Set (Real × Space)) with
    empty | nonempty
  · have coe_empty :
        ((parabolicLocalDomain domain residual.object
            (parabolicBase domain equation residual) :
          Opens (Real × Space)) : Set (Real × Space)) = ∅ := by
      simp [parabolicLocalDomain, Opens.coe_inf, empty]
    show Convex Real _
    rw [coe_empty]
    exact convex_empty
  · have mem : parabolicSite domain equation residual ∈ domain residual.object :=
      Classical.epsilon_spec
        (p := fun point => point ∈ domain residual.object) nonempty
    exact coverCylinder_admissible domain mem

/--
**The whole point localization, derived.**

`PublicPresentation` consumes this, and every nested focus, tower and nesting
proof downstream of it is `NestedFocus.ofCoreTower`'s.  A domain supplies no
window, no admissibility proof and no localization theorem.
-/
noncomputable def parabolicPointLocalization :
    PointLocalization (parabolicModel Space equation) where
  Admissible := ParabolicAdmissible domain
  site := parabolicSite domain equation
  base := parabolicBase domain equation
  point_mem_core_core := mem_parabolicBase domain equation
  base_admissible := parabolicBase_admissible domain equation

/--
**The pointwise admissible-window selector, derived.**

This is the cover hypothesis of `LocalClosureAlgebra.target_of_exhaustion`,
discharged from the openness of the object's domain alone.
-/
noncomputable def parabolicCover :
    AdmissibleWindowCover (parabolicModel Space equation)
      (ParabolicAdmissible domain)
      (fun object point => point ∈ domain object) where
  window := coverCylinder domain
  admissible := fun _object _point mem => coverCylinder_admissible domain mem
  contains := fun object point _mem => mem_coverCylinder domain object point

end Localization

end Hypostructure.PDE
