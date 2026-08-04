import Mathlib
import Hypostructure.PDE.Distribution.Local

/-!
# Space-time in Euclidean coordinates

A parabolic space-time is naturally written as a product `ℝ × Space`: time is
one factor and the spatial slice is the other, and that is the shape the atlas,
the cylinders and the equation all use.  The regularity theory, on the other
hand, needs an inner product --- `heatOperator`, `SobolevOn` and
`OrthonormalBasis` all do --- and a binary product carries the supremum norm,
which has none.

The two are the same vector space in different coordinates, and this module is
that change of coordinates.  In finite dimensions a linear equivalence is
automatically a homeomorphism, so nothing analytic is involved: the map is
written down once and smoothness travels along it in both directions.

This is what lets a certificate proved on `EuclideanSpace ℝ (Fin (n+1))` be
read as a statement about the registered product space-time.  No norm is
claimed to be preserved --- none needs to be, because the properties that
travel (smoothness, openness, membership) do not see the norm.
-/

namespace Hypostructure.PDE

open scoped ContDiff

/-- **Space-time in Euclidean coordinates.**  Time becomes the zeroth
coordinate and the spatial slice fills the rest. -/
noncomputable def spacetimeCoords (dimension : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin dimension)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (dimension + 1)) where
  toFun place := WithLp.toLp 2 (Fin.cons place.1 fun axis => place.2 axis)
  invFun point :=
    ((WithLp.ofLp point) 0, WithLp.toLp 2 fun axis => (WithLp.ofLp point) axis.succ)
  map_add' _first _second := by ext index; refine Fin.cases ?_ ?_ index <;> intros <;> simp
  map_smul' _scalar _place := by ext index; refine Fin.cases ?_ ?_ index <;> intros <;> simp
  left_inv _place := by ext <;> simp
  right_inv _point := by ext index; refine Fin.cases ?_ ?_ index <;> intros <;> simp

/-- The same change of coordinates as a homeomorphism.  Finite dimensionality
is the whole proof. -/
noncomputable def spacetimeCoordsL (dimension : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin dimension)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (dimension + 1)) :=
  (spacetimeCoords dimension).toContinuousLinearEquiv

/--
**Smoothness pulls back along the change of coordinates.**

A field that is smooth at the Euclidean image of a point, within the image of a
region, is smooth at the point within the region.  This is the direction a
local-closure certificate is consumed in: the regularity theory proves the
Euclidean statement and the registered problem asks for the product one.
-/
theorem contDiffWithinAt_of_euclidean {dimension : ℕ} {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : (ℝ × EuclideanSpace ℝ (Fin dimension)) → Value)
    (region : Set (ℝ × EuclideanSpace ℝ (Fin dimension)))
    (place : ℝ × EuclideanSpace ℝ (Fin dimension))
    (smooth : ContDiffWithinAt ℝ ∞ (field ∘ (spacetimeCoordsL dimension).symm)
      (spacetimeCoordsL dimension '' region) (spacetimeCoordsL dimension place)) :
    ContDiffWithinAt ℝ ∞ field region place := by
  have composed :
      ContDiffWithinAt ℝ ∞
        ((field ∘ (spacetimeCoordsL dimension).symm) ∘ spacetimeCoordsL dimension)
        region place :=
    smooth.comp place (spacetimeCoordsL dimension).contDiff.contDiffWithinAt
      (Set.mapsTo_image _ _)
  simpa [Function.comp_def] using composed

/-- Smoothness pushes forward along the change of coordinates, for the same
reason. -/
theorem contDiffWithinAt_euclidean_of {dimension : ℕ} {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : (ℝ × EuclideanSpace ℝ (Fin dimension)) → Value)
    (region : Set (ℝ × EuclideanSpace ℝ (Fin dimension)))
    (place : ℝ × EuclideanSpace ℝ (Fin dimension))
    (smooth : ContDiffWithinAt ℝ ∞ field region place) :
    ContDiffWithinAt ℝ ∞ (field ∘ (spacetimeCoordsL dimension).symm)
      (spacetimeCoordsL dimension '' region) (spacetimeCoordsL dimension place) := by
  refine smooth.comp _ (spacetimeCoordsL dimension).symm.contDiff.contDiffWithinAt ?_
  rintro _ ⟨origin, mem, rfl⟩
  simpa using mem

/-! ## The parabolic geometry of a Euclidean space-time

The atlas has to live where the regularity theory lives, and the regularity
theory needs an inner product.  So the parabolic window of a Euclidean
space-time is *defined* as the coordinate image of the product one: every
geometric fact it needs is then the image of an already-proved fact under a
linear homeomorphism, and no window is ever transported at use time.
-/

open Distribution in
/-- The parabolic window of a Euclidean space-time. -/
def euclideanParabolicRegion {dimension : ℕ}
    (centre : EuclideanSpace ℝ (Fin (dimension + 1))) (radius : ℝ) :
    Set (EuclideanSpace ℝ (Fin (dimension + 1))) :=
  spacetimeCoordsL dimension ''
    parabolicRegion ((spacetimeCoordsL dimension).symm centre) radius

open Distribution in
theorem isOpen_euclideanParabolicRegion {dimension : ℕ}
    (centre : EuclideanSpace ℝ (Fin (dimension + 1))) (radius : ℝ) :
    IsOpen (euclideanParabolicRegion centre radius) :=
  (spacetimeCoordsL dimension).toHomeomorph.isOpenMap _
    (isOpen_parabolicRegion _ radius)

open Distribution in
/-- Euclidean parabolic windows are convex: the image of a convex set under a
linear map. -/
theorem convex_euclideanParabolicRegion {dimension : ℕ}
    (centre : EuclideanSpace ℝ (Fin (dimension + 1))) (radius : ℝ) :
    Convex ℝ (euclideanParabolicRegion centre radius) :=
  (convex_parabolicRegion _ radius).linear_image
    (spacetimeCoordsL dimension).toLinearMap

open Distribution in
/-- A point lies in its own Euclidean parabolic window. -/
theorem mem_euclideanParabolicRegion {dimension : ℕ}
    (centre : EuclideanSpace ℝ (Fin (dimension + 1))) {radius : ℝ}
    (positive : 0 < radius) : centre ∈ euclideanParabolicRegion centre radius :=
  ⟨(spacetimeCoordsL dimension).symm centre,
    mem_parabolicRegion _ positive, by simp⟩

open Distribution in
/-- Every open set containing a point contains a Euclidean parabolic window
around it.  This is the geometric input a localization step needs. -/
theorem exists_euclideanParabolicRegion_subset {dimension : ℕ}
    {domain : Set (EuclideanSpace ℝ (Fin (dimension + 1)))}
    (open_domain : IsOpen domain)
    {centre : EuclideanSpace ℝ (Fin (dimension + 1))} (mem : centre ∈ domain) :
    ∃ radius : ℝ, 0 < radius ∧
      euclideanParabolicRegion centre radius ⊆ domain := by
  obtain ⟨radius, positive, subset⟩ :=
    exists_parabolicRegion_subset
      (open_domain.preimage (spacetimeCoordsL dimension).continuous)
      (show (spacetimeCoordsL dimension).symm centre ∈
        spacetimeCoordsL dimension ⁻¹' domain by simpa using mem)
  refine ⟨radius, positive, ?_⟩
  rintro _ ⟨place, place_mem, rfl⟩
  exact subset place_mem

end Hypostructure.PDE
