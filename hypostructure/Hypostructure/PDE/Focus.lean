import Hypostructure.PDE.Coordinate

/-!
# Nested local PDE focuses

The focus is indexed by one supplied point and carries only three nested
windows.  It neither enumerates the ambient point space nor chooses a global
scale.  Restriction and optional recentering are exposed through the existing
represented-coordinate machinery.
-/

namespace Hypostructure.PDE

universe u

/-- Three nested windows around one supplied local point. -/
structure NestedFocus (M : LocalModel.{u}) (point : M.atlas.Point) where
  inner : M.atlas.Window
  middle : M.atlas.Window
  outer : M.atlas.Window
  point_mem_inner : M.atlas.contains point inner
  inner_middle : M.atlas.nested inner middle
  middle_outer : M.atlas.nested middle outer

namespace NestedFocus

variable {M : LocalModel.{u}} {point : M.atlas.Point}
    (focus : NestedFocus M point)

/-- Derived inclusion of the inner window in the outer window. -/
def inner_outer : M.atlas.nested focus.inner focus.outer :=
  M.atlas.nested_trans focus.inner_middle focus.middle_outer

/-- Canonical represented restriction from the outer to the middle window. -/
def outerToMiddle : RealizedCoordinate M focus.outer focus.middle :=
  restrictionCoordinate M focus.middle_outer

/-- Canonical represented restriction from the middle to the inner window. -/
def middleToInner : RealizedCoordinate M focus.middle focus.inner :=
  restrictionCoordinate M focus.inner_middle

/-- Canonical direct represented restriction from outer to inner. -/
def outerToInner : RealizedCoordinate M focus.outer focus.inner :=
  restrictionCoordinate M focus.inner_outer

/-- The outer-to-middle restriction as a one-step Core coordinate path. -/
def outerToMiddlePath :
    Core.CoordinatePath (coordinateSystem M) focus.outer focus.middle :=
  .cons focus.outerToMiddle .nil

/-- The middle-to-inner restriction as a one-step Core coordinate path. -/
def middleToInnerPath :
    Core.CoordinatePath (coordinateSystem M) focus.middle focus.inner :=
  .cons focus.middleToInner .nil

/--
The nested restriction path is composed by Core and contains no PDE-owned
path execution.
-/
def outerToInnerPath :
    Core.CoordinatePath (coordinateSystem M) focus.outer focus.inner :=
  focus.outerToMiddlePath.append focus.middleToInnerPath

/-- Restrict an outer represented equation state to the middle window. -/
def restrictToMiddle
    (state : EquationState M.equation focus.outer) :
    EquationState M.equation focus.middle :=
  state.restrict focus.middle_outer

/-- Restrict the same outer state directly to the inner window. -/
def restrictToInner
    (state : EquationState M.equation focus.outer) :
    EquationState M.equation focus.inner :=
  state.restrict focus.inner_outer

/-- The local objects obtained through the middle and directly agree. -/
theorem restrict_inner_object_eq
    (state : EquationState M.equation focus.outer) :
    ((focus.restrictToMiddle state).restrict focus.inner_middle).object =
      (focus.restrictToInner state).object :=
  M.atlas.restrict_trans focus.inner_middle focus.middle_outer state.object

end NestedFocus

/-! ## Framework-owned nested-window assembly -/

/--
The atlas's own nested tower around one supplied point.

`middle` and `inner` are the `core` iterates of the supplied base window, so
the nesting proofs are the atlas laws `core_nested`.  No problem supplies a
`NestedFocus`, and no window is chosen by a consumer.
-/
def NestedFocus.ofCoreTower (M : LocalModel.{u}) (point : M.atlas.Point)
    (base : M.atlas.Window)
    (contained :
      M.atlas.contains point (M.atlas.core (M.atlas.core base))) :
    NestedFocus M point where
  inner := M.atlas.core (M.atlas.core base)
  middle := M.atlas.core base
  outer := base
  point_mem_inner := contained
  inner_middle := M.atlas.core_nested (M.atlas.core base)
  middle_outer := M.atlas.core_nested base

/-! ## The active residual -/

/--
The framework's view of the *active residual*: the object Core's selection
path already chose, together with its baseline, its target avoidance, and the
minimality kernel that excluded every strictly smaller baseline object.

Only Core's minimal-counterexample selection produces this value.  A public
presentation therefore cannot manufacture one from an ambient input, which is
exactly what prevents a global focus from being computed before local
residualization.
-/
structure ActiveResidual (M : LocalModel.{u}) where
  /-- The external target that the selected object avoids. -/
  Target : M.problem.Ambient → Prop
  /-- The registered strict progress relation used by the selector. -/
  Smaller : M.problem.Ambient → M.problem.Ambient → Prop
  /-- The selected minimal counterexample. -/
  object : M.problem.Ambient
  baseline : M.problem.Baseline object
  avoids : ¬ Target object
  minimal : ∀ H : M.problem.Ambient,
    Smaller H object → M.problem.Baseline H → Target H

/-! ## Framework-owned localization of the active residual -/

/--
Where a model localizes, and which windows are legitimate sites.

`base` and `site` are indexed by the *active residual*, so the window may be
chosen small enough to sit where the selected object actually lives; that is
what `base_admissible` records.  `Admissible` is localization data, not atlas
data: an atlas whose objects are globally defined takes it to be `True`,
while a model whose objects carry their own domain uses it to keep every
later statement local.

There is still no ambient-indexed focus here: the nested tower is assembled
by `NestedFocus.ofCoreTower` from the single base window.
-/
structure PointLocalization (M : LocalModel.{u}) where
  Admissible : M.problem.Ambient → M.atlas.Window → Prop
  site : ActiveResidual M → M.atlas.Point
  base : ActiveResidual M → M.atlas.Window
  point_mem_core_core : ∀ residual : ActiveResidual M,
    M.atlas.contains (site residual)
      (M.atlas.core (M.atlas.core (base residual)))
  base_admissible : ∀ residual : ActiveResidual M,
    Admissible residual.object (base residual)

namespace PointLocalization

variable {M : LocalModel.{u}} (localization : PointLocalization M)

/-- The framework-derived nested focus of the active residual. -/
def focus (residual : ActiveResidual M) :
    NestedFocus M (localization.site residual) :=
  NestedFocus.ofCoreTower M _ (localization.base residual)
    (localization.point_mem_core_core residual)

@[simp] theorem focus_outer (residual : ActiveResidual M) :
    (localization.focus residual).outer = localization.base residual :=
  rfl

@[simp] theorem focus_middle (residual : ActiveResidual M) :
    (localization.focus residual).middle =
      M.atlas.core (localization.base residual) :=
  rfl

@[simp] theorem focus_inner (residual : ActiveResidual M) :
    (localization.focus residual).inner =
      M.atlas.core (M.atlas.core (localization.base residual)) :=
  rfl

/-- The selected outer window is admissible for the selected object. -/
theorem focus_outer_admissible (residual : ActiveResidual M) :
    localization.Admissible residual.object (localization.focus residual).outer :=
  localization.base_admissible residual

end PointLocalization

/-! ## Framework-owned public PDE presentation -/

/--
Everything a PDE application supplies.

It contains no nested focus and no ambient-indexed focus selection.  The only
localization datum is `localization`, which is pure atlas data, plus `siteOf`,
which reads the *active residual* produced by Core's selection path and
returns a single point.  The nested tower, the outer equation state, and the
local/tail split are all derived by the framework from those.
-/
structure PublicPresentation (M : LocalModel.{u}) where
  /-- Where the model localizes; see `PointLocalization`.  This is the only
  localization datum, and it is residual-indexed. -/
  localization : PointLocalization M
  /-- The represented equation on every window of an already-selected
  residual.  It is indexed by the active residual rather than by a bare
  ambient object, so the equation is only ever demanded where Core's
  selection has already supplied a baseline. -/
  state : (residual : ActiveResidual M) →
    (window : M.atlas.Window) → EquationState M.equation window
  state_object : ∀ residual window,
    (state residual window).object = M.atlas.restrict residual.object window
  restrict_state : ∀ residual {inner outer}
    (nested : M.atlas.nested inner outer),
    (state residual outer).restrict nested = state residual inner

namespace PublicPresentation

variable {M : LocalModel.{u}} (presentation : PublicPresentation M)

/-- The local site of the active residual. -/
def siteOf (residual : ActiveResidual M) : M.atlas.Point :=
  presentation.localization.site residual

/-- The local focus of the active residual.  It is derived from the exact
selected context and the atlas locality data; it is never supplied. -/
def focus (residual : ActiveResidual M) :
    NestedFocus M (presentation.siteOf residual) :=
  presentation.localization.focus residual

/-- The selected outer window is admissible for the selected object. -/
theorem focus_outer_admissible (residual : ActiveResidual M) :
    presentation.localization.Admissible residual.object
      (presentation.focus residual).outer :=
  presentation.localization.base_admissible residual

/-- The same derived focus packaged with its point. -/
def focusOf (residual : ActiveResidual M) :
    Sigma fun point => NestedFocus M point :=
  ⟨presentation.siteOf residual, presentation.focus residual⟩

@[simp] theorem focusOf_fst (residual : ActiveResidual M) :
    (presentation.focusOf residual).1 = presentation.siteOf residual :=
  rfl

@[simp] theorem focusOf_snd (residual : ActiveResidual M) :
    (presentation.focusOf residual).2 = presentation.focus residual :=
  rfl

/-- The outer equation state of the active residual, obtained by restricting
the selected object to the derived outer window. -/
def outerState (residual : ActiveResidual M) :
    EquationState M.equation (presentation.focus residual).outer :=
  presentation.state residual (presentation.focus residual).outer

theorem outerState_object (residual : ActiveResidual M) :
    (presentation.outerState residual).object =
      M.atlas.restrict residual.object (presentation.focus residual).outer :=
  presentation.state_object residual _

/-- The inner equation state, obtained from the outer one by the framework's
own restriction along the derived tower. -/
def innerState (residual : ActiveResidual M) :
    EquationState M.equation (presentation.focus residual).inner :=
  (presentation.focus residual).restrictToInner
    (presentation.outerState residual)

theorem innerState_eq (residual : ActiveResidual M) :
    presentation.innerState residual =
      presentation.state residual (presentation.focus residual).inner :=
  presentation.restrict_state residual (presentation.focus residual).inner_outer

end PublicPresentation

/--
Optional recentering data for one nested focus.  Each coordinate is obtained
from the registered `RecenteringInterface`; no PDE adapter constructs a
coordinate map or assumes translation invariance.
-/
structure RecenteredFocus
    (M : LocalModel.{u}) {point : M.atlas.Point}
    (focus : NestedFocus M point) where
  interface : RecenteringInterface M
  shift : interface.Shift

namespace RecenteredFocus

variable {M : LocalModel.{u}} {point : M.atlas.Point}
    {focus : NestedFocus M point}
    (recentered : RecenteredFocus M focus)

def outerCoordinate :
    RealizedCoordinate M focus.outer
      (recentered.interface.targetWindow recentered.shift focus.outer) :=
  recentered.interface.coordinate recentered.shift focus.outer

def middleCoordinate :
    RealizedCoordinate M focus.middle
      (recentered.interface.targetWindow recentered.shift focus.middle) :=
  recentered.interface.coordinate recentered.shift focus.middle

def innerCoordinate :
    RealizedCoordinate M focus.inner
      (recentered.interface.targetWindow recentered.shift focus.inner) :=
  recentered.interface.coordinate recentered.shift focus.inner

end RecenteredFocus

end Hypostructure.PDE
