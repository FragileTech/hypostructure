import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Coordinate
import Hypostructure.PDE.LocalTail

/-!
# Recentered local-tail continuations

This module turns the tail child of an exact additive decomposition into the
next represented local equation.  It uses Core's residual queries and
coordinate paths throughout.  There is no PDE ledger, path language,
executor, route, or exterior-domain operation.
-/

namespace Hypostructure.PDE

universe uModel uCarrier uPrevious uClosed uAdded

/--
The exact tail child interpreted as a valid represented equation on its
source window.

`ExactLocalTail` owns additive reconstruction.  `RepresentedTail` owns only
the local equation interpretation of that same `split.tailPart`.
-/
structure RepresentedTail
    (M : LocalModel.{uModel})
    {Carrier : Type uCarrier} [Add Carrier]
    (whole : Carrier) (split : ExactLocalTail Carrier whole) where
  sourceWindow : M.atlas.Window
  interpretTail : Carrier → M.atlas.LocalObject sourceWindow
  equationState : EquationState M.equation sourceWindow
  equationState_object :
    equationState.object = interpretTail split.tailPart

/-- Optional rescaling data after a tail has been restricted and recentered. -/
structure TailScaleChoice
    (M : LocalModel.{uModel}) (window : M.atlas.Window) where
  interface : RescalingInterface M
  scale : interface.Scale

/--
One rescaling coordinate already derived from a registered interface.  Unlike
`TailScaleChoice`, this stored result contains no type-valued registry field.
-/
structure TailScaleCoordinate
    (M : LocalModel.{uModel}) (window : M.atlas.Window) where
  targetWindow : M.atlas.Window
  coordinate : RealizedCoordinate M window targetWindow

/--
Mathematical coordinate data for the next tail focus.

The target window and complete path are derived below.  A caller supplies no
transported object, transformed equation, path, or route.
-/
structure TailFocus
    (M : LocalModel.{uModel}) (sourceWindow : M.atlas.Window) where
  private mk ::
  restrictedWindow : M.atlas.Window
  restricted_nested : M.atlas.nested restrictedWindow sourceWindow
  recenteredWindow : M.atlas.Window
  recenteringCoordinate :
    RealizedCoordinate M restrictedWindow recenteredWindow
  scaleCoordinate? : Option
    (TailScaleCoordinate M recenteredWindow)

namespace TailFocus

variable {M : LocalModel.{uModel}} {sourceWindow : M.atlas.Window}
    (focus : TailFocus M sourceWindow)

/--
Construct a focus only from registered recentering and optional rescaling
interfaces.  The lightweight stored coordinates are derived here; callers
cannot inject a path, target equation, or transported object.
-/
def ofInterfaces
    (restrictedWindow : M.atlas.Window)
    (restricted_nested : M.atlas.nested restrictedWindow sourceWindow)
    (recentering : RecenteringInterface M)
    (shift : recentering.Shift)
    (scale? : Option
      (TailScaleChoice M
        (recentering.targetWindow shift restrictedWindow)) := none) :
    TailFocus M sourceWindow :=
  let recenteredWindow :=
    recentering.targetWindow shift restrictedWindow
  let recenteringCoordinate :=
    recentering.coordinate shift restrictedWindow
  match scale? with
  | none =>
      ⟨restrictedWindow, restricted_nested, recenteredWindow,
        recenteringCoordinate, none⟩
  | some selected =>
      ⟨restrictedWindow, restricted_nested, recenteredWindow,
        recenteringCoordinate,
        some
          ⟨selected.interface.targetWindow selected.scale recenteredWindow,
            selected.interface.coordinate selected.scale recenteredWindow⟩⟩

/-- Final local window, with optional registered rescaling. -/
private def targetWindowFor
    (choice : Option
      (TailScaleCoordinate M focus.recenteredWindow)) :
    M.atlas.Window :=
  match choice with
  | none => focus.recenteredWindow
  | some selected => selected.targetWindow

/-- Final local window, with optional registered rescaling. -/
def targetWindow : M.atlas.Window :=
  focus.targetWindowFor focus.scaleCoordinate?

/-- Optional rescaling suffix, built from the registered primitive only. -/
private def scalePathFor
    (choice : Option
      (TailScaleCoordinate M focus.recenteredWindow)) :
    Core.CoordinatePath (coordinateSystem M)
      focus.recenteredWindow (focus.targetWindowFor choice) :=
  match choice with
  | none => .nil
  | some selected => .cons selected.coordinate .nil

/-- Optional rescaling suffix, built from the registered primitive only. -/
def scalePath :
    Core.CoordinatePath (coordinateSystem M)
      focus.recenteredWindow focus.targetWindow :=
  focus.scalePathFor focus.scaleCoordinate?

/--
The derived restriction → recentering → optional-rescaling Core path.
-/
def coordinatePath :
    Core.CoordinatePath (coordinateSystem M)
      sourceWindow focus.targetWindow :=
  .cons (restrictionCoordinate M focus.restricted_nested)
    (.cons
      focus.recenteringCoordinate
      focus.scalePath)

end TailFocus

/--
Constructor-sealed result of transporting one represented tail.

Both the path and the equation state are fixed by the original tail and
`TailFocus`; no precomputed recentered state can be injected.
-/
structure RecenteredTail
    {M : LocalModel.{uModel}}
    {Carrier : Type uCarrier} [Add Carrier]
    {whole : Carrier} {split : ExactLocalTail Carrier whole}
    (originalTail : RepresentedTail M whole split)
    (focus : TailFocus M originalTail.sourceWindow) where
  private mk ::
  path : Core.CoordinatePath (coordinateSystem M)
    originalTail.sourceWindow focus.targetWindow
  path_eq : path = focus.coordinatePath
  state : EquationState M.equation focus.targetWindow
  state_eq :
    state = originalTail.equationState.transportPath focus.coordinatePath

namespace RepresentedTail

variable {M : LocalModel.{uModel}}
    {Carrier : Type uCarrier} [Add Carrier]
    {whole : Carrier} {split : ExactLocalTail Carrier whole}

/-- Deterministically transport a represented tail to its next local focus. -/
def recenter
    (tail : RepresentedTail M whole split)
    (focus : TailFocus M tail.sourceWindow) :
    RecenteredTail tail focus :=
  ⟨focus.coordinatePath, rfl,
    tail.equationState.transportPath focus.coordinatePath, rfl⟩

end RepresentedTail

namespace RecenteredTail

variable {M : LocalModel.{uModel}}
    {Carrier : Type uCarrier} [Add Carrier]
    {whole : Carrier} {split : ExactLocalTail Carrier whole}
    {tail : RepresentedTail M whole split}
    {focus : TailFocus M tail.sourceWindow}

/-- The transported object is exactly Core-path equation transport. -/
theorem state_object
    (recentered : RecenteredTail tail focus) :
    recentered.state.object =
      (tail.equationState.transportPath focus.coordinatePath).object := by
  rw [recentered.state_eq]

/-- The transported equation remains valid. -/
theorem state_valid
    (recentered : RecenteredTail tail focus) :
    M.equation.satisfies recentered.state.data :=
  recentered.state.valid

/-- Original local/tail reconstruction stays available after recentering. -/
theorem original_reconstruction
    (_recentered : RecenteredTail tail focus) :
    split.localPart + split.tailPart = whole :=
  split.exact_reconstruction

/-- Recentring the tail does not replace or modify the local child. -/
@[simp]
theorem localPart_unchanged
    (_recentered : RecenteredTail tail focus) :
    split.localPart = split.localPart :=
  rfl

/--
When the source state is the restriction of an ambient object, the
recentered tail object agrees with restriction of Core's ambient path run.
-/
theorem state_object_eq_restrict_run
    (recentered : RecenteredTail tail focus)
    (ambient : M.problem.Ambient)
    (source_eq :
      tail.equationState.object =
        M.atlas.restrict ambient tail.sourceWindow) :
    recentered.state.object =
      M.atlas.restrict
        (focus.coordinatePath.run ambient) focus.targetWindow := by
  rw [recentered.state_eq]
  exact EquationState.transportPath_object_eq_restrict_run
    focus.coordinatePath tail.equationState ambient source_eq

end RecenteredTail

namespace TailContinuation

/--
Residual-query presentation of a tail handoff.

The local-closure query is mandatory and participates in the derived
activation query.  Consequently a represented tail and a focus alone do not
form an active continuation.
-/
structure Profile
    (Previous : Type uPrevious)
    (M : LocalModel.{uModel})
    (Carrier : Previous → Type uCarrier)
    [∀ previous, Add (Carrier previous)]
    (wholeQuery : Core.Residual.Query Previous Carrier) where
  LocalClosed :
    (previous : Previous) →
      ExactLocalTail (Carrier previous) (wholeQuery.read previous) →
        Type uClosed
  splitQuery :
    Core.Residual.Query Previous fun previous =>
      ExactLocalTail (Carrier previous) (wholeQuery.read previous)
  localClosedQuery :
    Core.Residual.Query Previous fun previous =>
      LocalClosed previous (splitQuery.read previous)
  representedTailQuery :
    Core.Residual.Query Previous fun previous =>
      RepresentedTail M (wholeQuery.read previous)
        (splitQuery.read previous)
  focusQuery :
    Core.Residual.Query Previous fun previous =>
      TailFocus M (representedTailQuery.read previous).sourceWindow

namespace Profile

variable {Previous : Type uPrevious}
    {M : LocalModel.{uModel}}
    {Carrier : Previous → Type uCarrier}
    [∀ previous, Add (Carrier previous)]
    {wholeQuery : Core.Residual.Query Previous Carrier}
    (profile : Profile Previous M Carrier wholeQuery)

/-- The local child queried from the exact incoming split. -/
def localQuery : Core.Residual.Query Previous Carrier :=
  ExactLocalTail.localQuery wholeQuery profile.splitQuery

/-- The simultaneous tail child queried from the same split. -/
def tailQuery : Core.Residual.Query Previous Carrier :=
  ExactLocalTail.tailQuery wholeQuery profile.splitQuery

/--
All four exact predecessors required to activate the tail.  This is composed
only with Core query conjunction.
-/
def activationInputs :
    Core.Residual.Query Previous fun previous =>
      PProd
        (PProd
          (PProd
            (ExactLocalTail (Carrier previous)
              (wholeQuery.read previous))
            (profile.LocalClosed previous
              (profile.splitQuery.read previous)))
          (RepresentedTail M (wholeQuery.read previous)
            (profile.splitQuery.read previous)))
        (TailFocus M
          (profile.representedTailQuery.read previous).sourceWindow) :=
  ((profile.splitQuery.and profile.localClosedQuery).and
    profile.representedTailQuery).and profile.focusQuery

private def activate
    (previous : Previous)
    (_split :
      ExactLocalTail (Carrier previous) (wholeQuery.read previous))
    (_localClosed :
      profile.LocalClosed previous (profile.splitQuery.read previous))
    (represented :
      RepresentedTail M (wholeQuery.read previous)
        (profile.splitQuery.read previous))
    (focus : TailFocus M represented.sourceWindow) :
    RecenteredTail represented focus :=
  represented.recenter focus

/--
The recentered tail derived by dependent mapping of the exact split, local
closure, represented equation, and focus queries.
-/
def recenteredTailQuery :
    Core.Residual.Query Previous fun previous =>
      RecenteredTail
        (profile.representedTailQuery.read previous)
        (profile.focusQuery.read previous) :=
  profile.activationInputs.dependentMap fun previous inputs =>
    profile.activate previous inputs.1.1.1 inputs.1.1.2
      (profile.representedTailQuery.read previous)
      (profile.focusQuery.read previous)

/-- The represented recentered equation consumed by later PDE adapters. -/
def recenteredEquationQuery :
    Core.Residual.Query Previous fun previous =>
      EquationState M.equation
        (profile.focusQuery.read previous).targetWindow :=
  profile.recenteredTailQuery.map fun _ recentered => recentered.state

/-- The original exact decomposition certificate remains queryable. -/
def originalReconstructionQuery :
    Core.Residual.Query Previous fun previous =>
      (profile.splitQuery.read previous).localPart +
          (profile.splitQuery.read previous).tailPart =
        wholeQuery.read previous :=
  profile.splitQuery.dependentMap fun _ split =>
    split.exact_reconstruction

/-- Tail activation visibly reads the immediately preceding local closure. -/
theorem recenteredTailQuery_read
    (previous : Previous) :
    profile.recenteredTailQuery.read previous =
      profile.activate previous
        (profile.splitQuery.read previous)
        (profile.localClosedQuery.read previous)
        (profile.representedTailQuery.read previous)
        (profile.focusQuery.read previous) :=
  rfl

/--
Lift the entire handoff through one surrounding ledger extension.  Every
inherited query is lifted only with `Query.preserve`.
-/
def preserve
    {Added : Previous → Type uAdded} :
    Profile
      (Core.Residual.Ledger.Extension Previous Added) M
      (fun stage => Carrier stage.previous)
      wholeQuery.preserve where
  LocalClosed := fun stage split =>
    profile.LocalClosed stage.previous split
  splitQuery := profile.splitQuery.preserve
  localClosedQuery := profile.localClosedQuery.preserve
  representedTailQuery := profile.representedTailQuery.preserve
  focusQuery := profile.focusQuery.preserve

end Profile

end TailContinuation

end Hypostructure.PDE
