import Hypostructure.PDE.Coordinate

/-!
# Automatic recentering and rescaling

Recentering, rescaling and the coordinate bookkeeping around them are the
tedious part of local PDE work.  The framework already owns every piece ---
`RecenteringInterface`, `RescalingInterface`, `RealizedCoordinate`,
`Core.CoordinatePath`, `EquationState.transportPath` --- but a model still had
to wire them together by hand at every window.

This module does that wiring once.  A `Normalization` picks the shift and the
scale **from the window itself**, so nothing is chosen per problem, and it
exposes:

* `normalize` — carry an incoming local state to the model's normal window;
* `denormalize` — carry a result back;
* `denormalize_normalize` — the round trip is the identity.

The payoff is that a solution operator, a split, or an estimate may be stated
*only on the normal window*, and the framework moves it to and from whatever
window the localization step actually selected.  No model writes a coordinate
change again.

Everything is transport along an ordinary `Core.CoordinatePath`; there is no
second path type and no second executor.
-/

namespace Hypostructure.PDE

universe u

/--
A normalization scheme for a local model.

`shift` and `scale` are functions of the window, so the coordinate change is
determined by the incoming residual and never supplied per problem.
`inversePath` is the returning change of coordinates — a translation and a
dilation are invertible, and registering the inverse is structural data, not
an analytic hypothesis.
-/
structure Normalization (M : LocalModel.{u}) where
  recentering : RecenteringInterface M
  rescaling : RescalingInterface M
  shift : M.atlas.Window → recentering.Shift
  scale : M.atlas.Window → rescaling.Scale
  /-- The returning coordinate path. -/
  inversePath : (window : M.atlas.Window) →
    Core.CoordinatePath (coordinateSystem M)
      (rescaling.targetWindow (scale window)
        (recentering.targetWindow (shift window) window))
      window
  /-- Normalizing and returning is the identity on local states. -/
  round_trip : ∀ (window : M.atlas.Window)
    (state : EquationState M.equation window),
    ((state.transportCoordinate
        (recentering.coordinate (shift window) window)).transportCoordinate
      (rescaling.coordinate (scale window)
        (recentering.targetWindow (shift window) window))).transportPath
      (inversePath window) = state

namespace Normalization

variable {M : LocalModel.{u}} (normalization : Normalization M)

/-- The window after recentering. -/
def recenteredWindow (window : M.atlas.Window) : M.atlas.Window :=
  normalization.recentering.targetWindow (normalization.shift window) window

/-- The model's normal window: recentered, then rescaled. -/
def normalWindow (window : M.atlas.Window) : M.atlas.Window :=
  normalization.rescaling.targetWindow (normalization.scale window)
    (normalization.recenteredWindow window)

/-- The coordinate path carrying a window to its normal form.  It is an
ordinary two-primitive `Core.CoordinatePath`. -/
def path (window : M.atlas.Window) :
    Core.CoordinatePath (coordinateSystem M) window
      (normalization.normalWindow window) :=
  .cons (normalization.recentering.coordinate
      (normalization.shift window) window)
    (.cons (normalization.rescaling.coordinate (normalization.scale window)
      (normalization.recenteredWindow window)) .nil)

/-- Carry an incoming local state to the normal window. -/
def normalize (window : M.atlas.Window)
    (state : EquationState M.equation window) :
    EquationState M.equation (normalization.normalWindow window) :=
  state.transportPath (normalization.path window)

/-- Carry a result on the normal window back to the incoming window. -/
def denormalize (window : M.atlas.Window)
    (state : EquationState M.equation (normalization.normalWindow window)) :
    EquationState M.equation window :=
  state.transportPath (normalization.inversePath window)

/-- The round trip is the identity: a statement made on the normal window
returns to the window the localization step selected. -/
theorem denormalize_normalize (window : M.atlas.Window)
    (state : EquationState M.equation window) :
    normalization.denormalize window (normalization.normalize window state) =
      state :=
  normalization.round_trip window state

/-- Normalization keeps provenance: the normalized state is the restriction of
the transported ambient object, so no fact about where the state came from is
lost in the coordinate change. -/
theorem normalize_object (window : M.atlas.Window)
    (state : EquationState M.equation window) (ambient : M.problem.Ambient)
    (provenance : state.object = M.atlas.restrict ambient window) :
    (normalization.normalize window state).object =
      M.atlas.restrict ((normalization.path window).run ambient)
        (normalization.normalWindow window) :=
  EquationState.transportPath_object_eq_restrict_run
    (normalization.path window) state ambient provenance

/-- Equation validity survives normalization; it is carried by the state. -/
theorem normalize_valid (window : M.atlas.Window)
    (state : EquationState M.equation window) :
    M.equation.satisfies (normalization.normalize window state).data :=
  (normalization.normalize window state).valid

end Normalization

end Hypostructure.PDE
