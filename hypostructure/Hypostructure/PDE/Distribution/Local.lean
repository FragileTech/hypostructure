import Mathlib

/-!
# Local distribution and window geometry

Framework-owned helpers for PDEs whose local objects are distributions.
Nothing here mentions a particular equation: everything is generic over the
ambient normed space.

* `restrict` is the honest restriction of a distribution to a smaller open
  set, obtained by precomposing with extension-by-zero of test functions.
* `parabolicRegion` is the standard backward parabolic window around a point,
  together with the two facts a localization step needs: the point lies in
  its own window, and a small enough window fits inside any open set
  containing the point.
* `convex_parabolicRegion` is what makes local solvability unconditional:
  parabolic windows are convex, so Malgrange applies on them with no
  P-convexity side condition.
-/

namespace Hypostructure.PDE.Distribution

open TopologicalSpace
open scoped Distributions

universe uPoint uIndex

/-- Restriction of a distribution to a smaller open set.

`TestFunction.monoCLM` is extension-by-zero of test functions, which is the
inclusion exactly when the domains are nested; the nesting proof is therefore
the honesty condition of this definition. -/
noncomputable def restrict
    {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace Real Point]
    {small large : Opens Point} (_nested : small ≤ large)
    (value : Distribution large Real ⊤) : Distribution small Real ⊤ :=
  value.comp (TestFunction.monoCLM Real)

/--
The constant-coefficient operator of Laplace type determined by a finite
family of directions: the sum, over the family, of the second derivative
along each direction.

The ordinary Laplacian is the case where the directions are an orthonormal
basis; degenerate families are allowed.
-/
noncomputable def laplaceTypeCLM
    {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace Real Point]
    {Index : Type uIndex} [Fintype Index]
    (domain : Opens Point) (directions : Index → Point) :
    Distribution domain Real ⊤ →L[Real] Distribution domain Real ⊤ :=
  Finset.univ.sum fun index =>
    (Distribution.lineDerivCLM (directions index) :
        Distribution domain Real ⊤ →L[Real] Distribution domain Real ⊤).comp
      (Distribution.lineDerivCLM (directions index) :
        Distribution domain Real ⊤ →L[Real] Distribution domain Real ⊤)

section Parabolic

variable {Space : Type uPoint} [NormedAddCommGroup Space]
  [NormedSpace Real Space]

/--
The backward parabolic window of radius `r` around `point`.

The time interval ends half a parabolic unit *after* the point, so that a
backward window contains the point it is centred on.
-/
def parabolicRegion (point : Real × Space) (radius : Real) :
    Set (Real × Space) :=
  Set.Ioo (point.1 + radius ^ 2 / 2 - radius ^ 2)
      (point.1 + radius ^ 2 / 2) ×ˢ
    Metric.ball point.2 radius

theorem isOpen_parabolicRegion (point : Real × Space) (radius : Real) :
    IsOpen (parabolicRegion point radius) :=
  isOpen_Ioo.prod Metric.isOpen_ball

/-- Parabolic windows are convex.  This is the geometric fact that makes
local solvability unconditional on them. -/
theorem convex_parabolicRegion (point : Real × Space) (radius : Real) :
    Convex Real (parabolicRegion point radius) :=
  (convex_Ioo _ _).prod (convex_ball _ _)

/-- A point lies in its own parabolic window. -/
theorem mem_parabolicRegion (point : Real × Space) {radius : Real}
    (positive : 0 < radius) : point ∈ parabolicRegion point radius := by
  have square : 0 < radius ^ 2 := by positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show point.1 + radius ^ 2 / 2 - radius ^ 2 < point.1
    linarith
  · show point.1 < point.1 + radius ^ 2 / 2
    linarith
  · simpa using positive

/--
Every open set containing a point contains a parabolic window around it.

This is the only geometric input a localization step needs in order to choose
a window that sits where the selected object actually lives.
-/
theorem exists_parabolicRegion_subset
    {domain : Set (Real × Space)} (open_domain : IsOpen domain)
    {point : Real × Space} (mem : point ∈ domain) :
    ∃ radius : Real, 0 < radius ∧
      parabolicRegion point radius ⊆ domain := by
  obtain ⟨epsilon, positive, ball_subset⟩ :=
    Metric.isOpen_iff.mp open_domain point mem
  refine ⟨min epsilon 1, lt_min positive one_pos, ?_⟩
  set radius := min epsilon 1 with radius_def
  have radius_pos : 0 < radius := lt_min positive one_pos
  have radius_le : radius ≤ epsilon := min_le_left _ _
  have radius_le_one : radius ≤ 1 := min_le_right _ _
  have square_le : radius ^ 2 ≤ radius := by nlinarith
  intro candidate mem_window
  apply ball_subset
  rw [← ball_prod_same]
  obtain ⟨time_mem, space_mem⟩ := mem_window
  refine ⟨?_, ?_⟩
  · have lower : point.1 + radius ^ 2 / 2 - radius ^ 2 < candidate.1 :=
      time_mem.1
    have upper : candidate.1 < point.1 + radius ^ 2 / 2 := time_mem.2
    have : |candidate.1 - point.1| < epsilon := by
      rw [abs_lt]
      constructor <;> nlinarith
    simpa [Metric.mem_ball, Real.dist_eq] using this
  · exact Metric.ball_subset_ball radius_le space_mem

end Parabolic

end Hypostructure.PDE.Distribution
