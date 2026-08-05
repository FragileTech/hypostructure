import Hypostructure.Core.Strategy.Dag
import Hypostructure.PDE.Model
import Hypostructure.PDE.Focus
import Hypostructure.PDE.EllipticLocalTail

/-!
# Callback-free PDE minimal-counterexample localization

Core performs target stopping, minimal selection, and ledger extension.  This
thin PDE adapter supplies only the canonical zero-step local progress
presentation: no PDE problem can manufacture a smaller predecessor at this
opening localization step.  The strategy output is Core's exact selected
minimal-counterexample context.
-/

namespace Hypostructure.PDE.Strategy.CounterexampleLocalization

open Hypostructure

universe u uPrevious

/-- Canonical opening progress for an arbitrary represented PDE problem.
The empty strict relation makes the received obstruction itself the unique
minimal local counterexample; subsequent PDE strategies refine its windows
through the existing coordinate and residual APIs. -/
def progress (M : PDE.LocalModel.{u}) : Core.Progress.{u, u, 0} M.problem where
  Measure := Unit
  lt := fun _ _ => False
  wellFounded := ⟨fun _ =>
    @Acc.intro Unit (fun _ _ => False) ()
      (fun _ smaller => False.elim smaller)⟩
  measure := fun _ => ()

/-- Callback-free registration usable by every represented PDE model. -/
def registration (M : PDE.LocalModel.{u}) (T : Core.Target M.problem) :
    Core.CounterexampleLocalizationData.{u, u, 0} M.problem T where
  selection :=
    Core.MinimalCounterexampleSelectionData.ofProgress (progress M)

/-! ## Step 2: the selected context *is* the active residual

Exactly as on the Graph side, the adapter interprets Core's selected context
and adds nothing.  The interpretation is total: every field of
`PDE.ActiveResidual` is a field of the exact selected context. -/

/-- Expose Core's selected minimal-counterexample context as the framework's
active residual.  This is the only bridge between selection and
localization. -/
def activeResidual
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {progress : Core.Progress.{u, u, 0} M.problem}
    (context :
      Core.MinimalCounterexampleContext M.problem T.Predicate progress) :
    PDE.ActiveResidual M where
  Target := T.Predicate
  Smaller := progress.Smaller
  object := context.G
  baseline := context.baseline
  avoids := context.avoids
  minimal := context.minimal

@[simp] theorem activeResidual_object
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {progress : Core.Progress.{u, u, 0} M.problem}
    (context :
      Core.MinimalCounterexampleContext M.problem T.Predicate progress) :
    (activeResidual (T := T) context).object = context.G :=
  rfl

/-! ## Step 3: the local focus is derived from that active residual

`FocusedResidual` is produced by the framework alone.  Its point comes from
the public presentation's residual-indexed site, its nested windows from the
atlas `core` tower, and its outer state from the represented equation. -/

structure FocusedResidual (M : PDE.LocalModel.{u}) where
  ambient : M.problem.Ambient
  point : M.atlas.Point
  focus : PDE.NestedFocus M point
  outerState : PDE.EquationState M.equation focus.outer
  outerState_object :
    outerState.object = M.atlas.restrict ambient focus.outer

/-- The framework-derived focus of the active residual. -/
def focusOf
    {M : PDE.LocalModel.{u}}
    (presentation : PDE.PublicPresentation M)
    (residual : PDE.ActiveResidual M) :
    Sigma fun point => PDE.NestedFocus M point :=
  presentation.focusOf residual

/-- The framework-derived local residual of the active residual. -/
def focusedResidual
    {M : PDE.LocalModel.{u}}
    (presentation : PDE.PublicPresentation M)
    (residual : PDE.ActiveResidual M) : FocusedResidual M where
  ambient := residual.object
  point := presentation.siteOf residual
  focus := presentation.focus residual
  outerState := presentation.outerState residual
  outerState_object := presentation.outerState_object residual

def activeResidualQuery
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {Previous : Sort*}
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext M.problem T.Predicate
        (registration M T).selection.progress) :
    Core.Residual.Query Previous fun _ => PDE.ActiveResidual M :=
  context.map fun _ selected => activeResidual (T := T) selected

def focusQuery
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {Previous : Sort*}
    (presentation : PDE.PublicPresentation M)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext M.problem T.Predicate
        (registration M T).selection.progress) :
    Core.Residual.Query Previous fun _ =>
      Sigma fun point => PDE.NestedFocus M point :=
  (activeResidualQuery (T := T) context).map fun _ residual =>
    focusOf presentation residual

def equationStateQuery
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {Previous : Sort*}
    (presentation : PDE.PublicPresentation M)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext M.problem T.Predicate
        (registration M T).selection.progress) :
    Core.Residual.Query Previous fun previous =>
      let focused := (focusQuery presentation context) previous
      PDE.EquationState M.equation focused.2.outer :=
  (activeResidualQuery (T := T) context).dependentMap fun _ residual =>
    presentation.outerState residual

def focusedResidualQuery
    {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
    {Previous : Sort*}
    (presentation : PDE.PublicPresentation M)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext M.problem T.Predicate
        (registration M T).selection.progress) :
    Core.Residual.Query Previous fun _ => FocusedResidual M :=
  (activeResidualQuery (T := T) context).map fun _ residual =>
    focusedResidual presentation residual

/-- Thin consumer of the exact context query exported by Core. -/
structure Profile
    (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)
    (Previous : Type uPrevious) where
  context : Core.Residual.Query Previous fun _ =>
    Core.MinimalCounterexampleContext M.problem T.Predicate
      (registration M T).selection.progress

namespace Profile

variable {M : PDE.LocalModel.{u}} {T : Core.Target M.problem}
  {Previous : Type uPrevious}
  (profile : Profile M T Previous)

def objectQuery : Core.Residual.Query Previous fun _ => M.problem.Ambient :=
  profile.context.map fun _ context => context.G

/-- The active local residual is obtained from the Core-selected context;
there is no second ledger read or application-owned residual value. -/
def activeQuery : Core.Residual.Query Previous fun _ => PDE.ActiveResidual M :=
  activeResidualQuery (T := T) profile.context

def baselineQuery : Core.Residual.Query Previous fun previous =>
    M.problem.Baseline (profile.objectQuery previous) :=
  profile.context.dependentMap fun _ context => context.baseline

def avoidingQuery : Core.Residual.Query Previous fun previous =>
    Not (T.Predicate (profile.objectQuery previous)) :=
  profile.context.dependentMap fun _ context => context.avoids

/-! ### Steps 3 and 4, wired by the framework

Given only a `PublicPresentation`, the profile derives the focus, the local
residual, and — once a local elliptic constraint is registered — the
`CurrentLocalEllipticResidual` whose exact atom/tail split Core consumes.
An application supplies none of these. -/

def focusQuery (presentation : PDE.PublicPresentation M) :
    Core.Residual.Query Previous fun _ =>
      Sigma fun point => PDE.NestedFocus M point :=
  CounterexampleLocalization.focusQuery (T := T) presentation profile.context

def focusedResidualQuery (presentation : PDE.PublicPresentation M) :
    Core.Residual.Query Previous fun _ => FocusedResidual M :=
  CounterexampleLocalization.focusedResidualQuery (T := T) presentation
    profile.context

/-- The local elliptic residual of the active residual: step 4's input.

`Carrier` and `Source` are indexed by the elliptic constraint's component
interface, so a PDE whose components live in an object-dependent space — a
distribution over the selected object's own domain, say — needs no flattening
and no problem-specific carrier. -/
def currentLocalEllipticQuery
    {N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u} {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    (elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source)
    (presentation : PDE.PublicPresentation M)
    (admissible : ∀ residual : PDE.ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer) :
    Core.Residual.Query Previous fun _ =>
      PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
        elliptic :=
  PDE.CurrentLocalEllipticResidual.ofActiveResidualQuery
    (elliptic := elliptic) presentation profile.activeQuery admissible

end Profile

end Hypostructure.PDE.Strategy.CounterexampleLocalization
