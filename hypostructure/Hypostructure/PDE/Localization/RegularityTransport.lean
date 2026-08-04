import Mathlib
import Hypostructure.PDE.Singularity

/-!
# Regularity travels with the coordinate change

A local argument is allowed to move its window: translate it so the singularity
sits at the origin, or rescale it parabolically.  For that to be free of
mathematical content, the framework must own the statement that regularity is
*not changed* by the move --- otherwise every recentering would be an analytic
step and the localization would not be local at all.

That is this module.  Every change of coordinates used by a parabolic
localization is either a translation or a linear homeomorphism, and smoothness
is preserved by both in both directions, for the same reason: the map and its
inverse are smooth, and `ContDiffWithinAt` composes.

The theorem that matters most is `singularSet_comp_add_const` and its linear
counterpart: **the singular set moves with the coordinate change**.  So a
window recentred on the singularity really is a window around the origin of the
moved field, and "profile the singularity locally" is a statement about the
recentred picture without any further argument.

Nothing here is an estimate.  No norm is claimed to be preserved --- none needs
to be, because smoothness does not see the norm.
-/

namespace Hypostructure.PDE.Localization.RegularityTransport

open scoped ContDiff

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Translation -/

/-- Translation is smooth, which is the only fact the transport needs. -/
theorem contDiff_addRight (shift : E) :
    ContDiff ℝ ∞ (fun place : E => place + shift) :=
  contDiff_id.add contDiff_const

/-- Smoothness at a point transports along a translation. -/
theorem contDiffWithinAt_comp_add_const {field : E → F} {region : Set E}
    (shift place : E)
    (smooth : ContDiffWithinAt ℝ ∞ field region (place + shift)) :
    ContDiffWithinAt ℝ ∞ (fun position => field (position + shift))
      ((fun position => position + shift) ⁻¹' region) place :=
  smooth.comp place (contDiff_addRight shift).contDiffWithinAt
    (Set.mapsTo_preimage _ _)

/-- …and back, by translating by the opposite shift. -/
theorem contDiffWithinAt_of_comp_add_const {field : E → F} {region : Set E}
    (shift place : E)
    (smooth : ContDiffWithinAt ℝ ∞ (fun position => field (position + shift))
      ((fun position => position + shift) ⁻¹' region) place) :
    ContDiffWithinAt ℝ ∞ field region (place + shift) := by
  have moved := contDiffWithinAt_comp_add_const (field := fun position =>
    field (position + shift))
    (region := (fun position => position + shift) ⁻¹' region) (-shift)
    (place + shift) (by simpa using smooth)
  have rewritten :
      (fun position : E => field (position + -shift + shift)) = field := by
    funext position; simp
  have setRewritten :
      (fun position : E => position + -shift) ⁻¹'
          ((fun position : E => position + shift) ⁻¹' region) = region := by
    ext position; simp
  rw [rewritten, setRewritten] at moved
  simpa using moved

/-- **Smoothness at a point is unchanged by translation.** -/
theorem contDiffWithinAt_add_const_iff {field : E → F} {region : Set E}
    (shift place : E) :
    ContDiffWithinAt ℝ ∞ (fun position => field (position + shift))
        ((fun position => position + shift) ⁻¹' region) place ↔
      ContDiffWithinAt ℝ ∞ field region (place + shift) :=
  ⟨contDiffWithinAt_of_comp_add_const shift place,
    contDiffWithinAt_comp_add_const shift place⟩

/-- **Interior regularity is unchanged by translation.** -/
theorem contDiffOn_add_const_iff {field : E → F} {region : Set E} (shift : E) :
    ContDiffOn ℝ ∞ (fun position => field (position + shift))
        ((fun position => position + shift) ⁻¹' region) ↔
      ContDiffOn ℝ ∞ field region := by
  constructor
  · intro smooth point mem
    have := (contDiffWithinAt_add_const_iff (field := field) (region := region)
      shift (point + -shift)).mp (by simpa using smooth (point + -shift) (by simpa using mem))
    simpa using this
  · intro smooth point mem
    exact (contDiffWithinAt_add_const_iff (field := field) (region := region)
      shift point).mpr (smooth _ mem)

/--
**The singular set moves with the translation.**

This is what makes a recentred window a window around the *same* singularity:
the points of non-smoothness of the translated field are exactly the
translates of the points of non-smoothness of the original.
-/
theorem singularSet_comp_add_const (field : E → F) (region : Set E) (shift : E) :
    PDE.singularSet (fun position => field (position + shift))
        ((fun position => position + shift) ⁻¹' region) =
      (fun position => position + shift) ⁻¹' PDE.singularSet field region := by
  ext place
  simp only [PDE.mem_singularSet, Set.mem_preimage]
  exact and_congr Iff.rfl
    (not_congr (contDiffWithinAt_add_const_iff (field := field) (region := region)
      shift place))

/-! ## A linear homeomorphism

Parabolic rescaling `(t, x) ↦ (λ²t, λx)` is linear and invertible, so it is a
`ContinuousLinearEquiv`, and the same argument applies verbatim.
-/

/-- Smoothness at a point transports along a linear homeomorphism. -/
theorem contDiffWithinAt_comp_equiv {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) (place : E)
    (smooth : ContDiffWithinAt ℝ ∞ field region (change place)) :
    ContDiffWithinAt ℝ ∞ (fun position => field (change position))
      (change ⁻¹' region) place :=
  smooth.comp place change.contDiff.contDiffWithinAt (Set.mapsTo_preimage _ _)

/-- …and back, along the inverse. -/
theorem contDiffWithinAt_of_comp_equiv {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) (place : E)
    (smooth : ContDiffWithinAt ℝ ∞ (fun position => field (change position))
      (change ⁻¹' region) place) :
    ContDiffWithinAt ℝ ∞ field region (change place) := by
  have moved := contDiffWithinAt_comp_equiv
    (field := fun position => field (change position))
    (region := change ⁻¹' region) change.symm (change place)
    (by simpa using smooth)
  have rewritten :
      (fun position : E => field (change (change.symm position))) = field := by
    funext position; simp
  have setRewritten :
      (change.symm : E → E) ⁻¹' ((change : E → E) ⁻¹' region) = region := by
    ext position; simp
  rw [rewritten, setRewritten] at moved
  simpa using moved

/-- **Smoothness at a point is unchanged by a linear change of coordinates.** -/
theorem contDiffWithinAt_equiv_iff {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) (place : E) :
    ContDiffWithinAt ℝ ∞ (fun position => field (change position))
        (change ⁻¹' region) place ↔
      ContDiffWithinAt ℝ ∞ field region (change place) :=
  ⟨contDiffWithinAt_of_comp_equiv change place,
    contDiffWithinAt_comp_equiv change place⟩

/-- **Interior regularity is unchanged by a linear change of coordinates.** -/
theorem contDiffOn_equiv_iff {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun position => field (change position)) (change ⁻¹' region) ↔
      ContDiffOn ℝ ∞ field region := by
  constructor
  · intro smooth point mem
    have := (contDiffWithinAt_equiv_iff (field := field) (region := region)
      change (change.symm point)).mp
        (by simpa using smooth (change.symm point) (by simpa using mem))
    simpa using this
  · intro smooth point mem
    exact (contDiffWithinAt_equiv_iff (field := field) (region := region)
      change point).mpr (smooth _ mem)

/-- **The singular set moves with the linear change of coordinates.** -/
theorem singularSet_comp_equiv (field : E → F) (region : Set E)
    (change : E ≃L[ℝ] E) :
    PDE.singularSet (fun position => field (change position)) (change ⁻¹' region) =
      (change : E → E) ⁻¹' PDE.singularSet field region := by
  ext place
  simp only [PDE.mem_singularSet, Set.mem_preimage]
  exact and_congr Iff.rfl
    (not_congr (contDiffWithinAt_equiv_iff (field := field) (region := region)
      change place))

/-! ## The change of frame a localization actually performs

Recentring *and* rescaling at once: `place ↦ change place + shift`.  That is the
map a parabolic localization applies when it moves a window onto the
singularity and zooms in, and it is the composition of the two cases above, so
nothing new is proved --- the two halves are simply run in order.
-/

/-- **Regularity at a point is unchanged by an affine change of frame.** -/
theorem contDiffWithinAt_affine_iff {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) (shift place : E) :
    ContDiffWithinAt ℝ ∞ (fun position => field (change position + shift))
        ((fun position => change position + shift) ⁻¹' region) place ↔
      ContDiffWithinAt ℝ ∞ field region (change place + shift) := by
  have translated :=
    contDiffWithinAt_add_const_iff (field := field) (region := region) shift
  have composed :=
    contDiffWithinAt_equiv_iff
      (field := fun position => field (position + shift))
      (region := (fun position => position + shift) ⁻¹' region) change place
  refine composed.trans (translated (change place))

/-- **The singular set moves with the change of frame.**

This is what lets a localization follow the singularity across frames: the
points of non-smoothness in the moved picture are exactly the moved points of
non-smoothness, so "the window is centred on the blowup" survives recentring
and rescaling without any further argument. -/
theorem singularSet_comp_affine (field : E → F) (region : Set E)
    (change : E ≃L[ℝ] E) (shift : E) :
    PDE.singularSet (fun position => field (change position + shift))
        ((fun position => change position + shift) ⁻¹' region) =
      (fun position => change position + shift) ⁻¹' PDE.singularSet field region := by
  ext place
  simp only [PDE.mem_singularSet, Set.mem_preimage]
  exact and_congr Iff.rfl
    (not_congr (contDiffWithinAt_affine_iff (field := field) (region := region)
      change shift place))

/-- **Interior regularity is unchanged by the change of frame.** -/
theorem contDiffOn_affine_iff {field : E → F} {region : Set E}
    (change : E ≃L[ℝ] E) (shift : E) :
    ContDiffOn ℝ ∞ (fun position => field (change position + shift))
        ((fun position => change position + shift) ⁻¹' region) ↔
      ContDiffOn ℝ ∞ field region := by
  constructor
  · intro smooth point mem
    have moved :=
      (contDiffWithinAt_affine_iff (field := field) (region := region) change shift
        (change.symm (point + -shift))).mp
        (by simpa using smooth (change.symm (point + -shift)) (by simpa using mem))
    simpa using moved
  · intro smooth point mem
    exact (contDiffWithinAt_affine_iff (field := field) (region := region)
      change shift point).mpr (smooth _ mem)

/-! ## Assembling a Euclidean-valued field from its coordinates

A balance names its gradient one coordinate at a time, but a target asks for a
single vector-valued field.  Smoothness passes between the two readings because
`WithLp.toLp` is a linear homeomorphism onto a finite-dimensional space, so it
is smooth and so is each coordinate projection.
-/

/-- **A Euclidean-valued field is smooth when each of its coordinates is.** -/
theorem contDiffOn_euclidean_of_coordinates {n : ℕ} {region : Set E}
    {coordinates : E → Fin n → ℝ}
    (smooth : ∀ index, ContDiffOn ℝ ∞ (fun place => coordinates place index) region) :
    ContDiffOn ℝ ∞ (fun place => (WithLp.toLp 2 (coordinates place) :
      EuclideanSpace ℝ (Fin n))) region := by
  rw [contDiffOn_euclidean]
  intro index
  exact (smooth index).congr fun place _ => rfl

/-- …and conversely, each coordinate of a smooth Euclidean-valued field is
smooth. -/
theorem contDiffOn_coordinate_of_euclidean {n : ℕ} {region : Set E}
    {field : E → EuclideanSpace ℝ (Fin n)}
    (smooth : ContDiffOn ℝ ∞ field region) (index : Fin n) :
    ContDiffOn ℝ ∞ (fun place => field place index) region :=
  (contDiffOn_euclidean.mp smooth) index

end Hypostructure.PDE.Localization.RegularityTransport
