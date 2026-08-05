import Hypostructure.Core.Minimality
import Hypostructure.Core.Residual.Focus

/-!
# Subobject minimality: the legacy focused execution

**Legacy.**  `Core/Minimality.lean` holds `lem:no-proper-core`'s generic form --
the subobject-minimality profile and the certificate that excludes a proper
subobject satisfying the baseline.  This file holds the focused-stage execution
that used to drive it, which reaches `Core.Residual.Focus` and through it the
legacy `Core.Residual.Ledger`.

Separated so that the spine's node `[8]` can consume the exclusion without
importing the legacy stage stack.  Nothing in the ported spine reaches this
file.
-/

namespace Hypostructure.Core.Minimality

universe uAmbient uBranch uMeasure uSubobject

/-- Focused output carrying the certificate on active predecessors. -/
abbrev FocusedNoSubobjectBaselineOutput
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (stage : Previous) (active : focus.Active stage) :=
  NoSubobjectBaselineCertificate profile (context stage active)

/-- Exact accumulated stage after focused minimality registration. -/
abbrev FocusedNoSubobjectBaselineStage
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Residual.Focus.Stage focus
    (FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context)

/-- Counted focused execution of the generic subobject minimality pattern. -/
def executeFocusedNoSubobjectBaselineCounted
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    Core.Counted (FocusedNoSubobjectBaselineStage (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context) :=
  Core.Residual.Focus.runCounted focus
    (Output :=
      FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context)
    previous
    (fun active _checks _exact =>
      deriveNoSubobjectBaseline profile (context previous active))

@[simp] theorem executeFocusedNoSubobjectBaselineCounted_checks
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    (executeFocusedNoSubobjectBaselineCounted (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context
  previous).checks =
      focus.selectionBudget.checks previous := by
  simp [executeFocusedNoSubobjectBaselineCounted]

theorem executeFocusedNoSubobjectBaselineCounted_work_within
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedNoSubobjectBaselineCounted (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context
        previous).checks :=
  by
    rw [executeFocusedNoSubobjectBaselineCounted_checks (P := P)
      (Target := Target) (progress := progress) (Subobject := Subobject)
      focus profile context previous]
    exact focus.selectionBudget.bounded previous

/-- Focused profile used by successor stages. -/
abbrev FocusedNoSubobjectBaselineProfile
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Residual.Focus.successor focus
    (FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context)

/-- Read the exact certificate from the newest focused stage. -/
def focusedNoSubobjectBaselineQuery
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :
    Core.Residual.Focus.ActiveQuery
      (FocusedNoSubobjectBaselineProfile (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context)
      (fun stage active =>
        FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
          (progress := progress) (Subobject := Subobject) focus profile
          context stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Core.Minimality
