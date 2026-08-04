import Hypostructure.Core.Minimality

/-!
# Minimal-subobject exclusion strategy

This domain-neutral Strategy composition runs Core's existing focused
minimality operation on the literal predecessor ledger.  On the active
branch, the operation appends the existing
`Minimality.NoSubobjectBaselineCertificate`; inactive siblings receive only
the framework-owned inactive marker.  The predecessor, its residual, and its
accumulated ledger are retained by `Residual.Focus.Stage`.

No new construction theorem or CT is introduced here.  Certificate
derivation, branch selection, ledger extension, work accounting, and
successor queries are delegated to the canonical Core APIs.
-/

namespace Hypostructure.Core.Strategy.MinimalSubobjectExclusion

universe uAmbient uBranch uMeasure uSubobject uResidual uPrevious

/-! ## Ordinary accumulated-ledger execution -/

/-- Exact non-branching successor when the incoming stage already carries a
minimal-counterexample context query. -/
abbrev DirectStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uPrevious}
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Core.Minimality.NoSubobjectBaselineCertificate profile
      (context.read previous)

/-- Append the generic minimality certificate to the literal predecessor. -/
def executeDirect
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uPrevious}
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    DirectStage profile context :=
  Core.Residual.Ledger.extend previous
    (Core.Minimality.deriveNoSubobjectBaseline profile
      (context.read previous))

/-- Read the exact certificate appended by `executeDirect`. -/
def directCertificateQuery
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uPrevious}
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Query Previous fun _ =>
      Core.MinimalCounterexampleContext P Target progress) :
    Core.Residual.Query (DirectStage profile context) fun stage =>
      Core.Minimality.NoSubobjectBaselineCertificate profile
        (context.read stage.previous) :=
  Core.Residual.Query.latest

/-- Certificate appended by the existing minimality operation on an active
literal predecessor. -/
abbrev Certificate
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) (active : focus.Active previous) :=
  Core.Minimality.FocusedNoSubobjectBaselineOutput
    focus profile context previous active

/-- The single canonical ledger extension produced by minimal-subobject
exclusion. -/
abbrev Stage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Minimality.FocusedNoSubobjectBaselineStage focus profile context

/-- Run the existing focused minimality operation.  This wrapper performs no
independent branch decision and appends no payload other than the certificate
returned by `executeFocusedNoSubobjectBaselineCounted`. -/
def executeCounted
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    Core.Counted (Stage focus profile context) :=
  Core.Minimality.executeFocusedNoSubobjectBaselineCounted
    focus profile context previous

/-- Project the accumulated successor stage from the counted execution. -/
def execute
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    Stage focus profile context :=
  (executeCounted focus profile context previous).value

/-- Execution retains the literal incoming stage as its predecessor. -/
@[simp] theorem executeCounted_previous
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    (executeCounted focus profile context previous).value.previous = previous := by
  simp [executeCounted,
    Core.Minimality.executeFocusedNoSubobjectBaselineCounted]

/-- The uncounted projection retains the same literal predecessor. -/
@[simp] theorem execute_previous
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    (execute focus profile context previous).previous = previous :=
  executeCounted_previous focus profile context previous

/-- The composition cannot replace or repackage the incoming residual. -/
@[simp] theorem residual_execute
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    {Residual : Type uResidual}
    [Core.Residual.HasResidual Previous Residual]
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    Core.Residual.residualOf (execute focus profile context previous) =
      Core.Residual.residualOf previous := by
  change
    Core.Residual.residualOf
        (execute focus profile context previous).previous =
      Core.Residual.residualOf previous
  rw [execute_previous]

/-- Exact work is the existing framework-owned focus-selection work. -/
@[simp] theorem executeCounted_checks
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    (executeCounted focus profile context previous).checks =
      focus.selectionBudget.checks previous :=
  Core.Minimality.executeFocusedNoSubobjectBaselineCounted_checks
    focus profile context previous

/-- Predicate-form polynomial work evidence inherited from Core minimality. -/
theorem executeCounted_work_within
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeCounted focus profile context previous).checks :=
  Core.Minimality.executeFocusedNoSubobjectBaselineCounted_work_within
    focus profile context previous

/-- Focus inherited by the successor stage after the certificate is
appended. -/
abbrev SuccessorFocus
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Minimality.FocusedNoSubobjectBaselineProfile focus profile context

/-- Canonical read of the exact certificate appended by `executeCounted`.
The query is proof-indexed and available only on the inherited active branch. -/
def certificateQuery
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :
    Core.Residual.Focus.ActiveQuery
      (SuccessorFocus focus profile context)
      (fun stage active =>
        Certificate focus profile context stage.previous active) :=
  Core.Minimality.focusedNoSubobjectBaselineQuery focus profile context

end Hypostructure.Core.Strategy.MinimalSubobjectExclusion
