import Hypostructure.Graph.Obstruction
import Hypostructure.Graph.CT1

/-!
# CT1 encodings for induced-copy obstructions

**Legacy.**  These are the focused CT1 encodings of the obstruction predicates
in `Graph/Obstruction.lean`.  They are kept separate from the predicates so
that a consumer of `HasInducedObstruction` -- the entry spine, in particular --
does not drag the legacy `Core.Residual.Ledger` stage stack in behind it.

Nothing in the ported spine reaches this file.  It goes when the rows that
would use it are ported onto the canonical ledger.
-/

namespace Hypostructure.Graph

universe uPrevious uVertex uPattern

namespace CT1

/-- Focused proof-carrying CT1 encoding for an arbitrary induced obstruction in
a graph read from the active residual. -/
def focusedInducedObstructionEncoding {Previous : Type uPrevious}
    {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Encoding profile
      (fun previous active =>
        HasInducedObstruction pattern (object previous active)) where
  Code := fun previous active =>
    pattern ↪g (object previous active).graph
  Accepts := fun _previous _active _certificate => True
  encode := by
    intro previous active target
    rcases target with ⟨certificate⟩
    exact ⟨certificate, trivial⟩
  decode := by
    intro previous active certificate _accepted
    exact ⟨certificate⟩
  acceptsDecidable := fun _previous _active _certificate => .isTrue trivial

/-- Counted focused CT1 execution for an induced-obstruction certificate
target. -/
noncomputable def executeFocusedInducedObstructionCounted
    {Previous : Type uPrevious} {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
        (focusedInducedObstructionEncoding profile object pattern)) :=
  (focusedInducedObstructionEncoding profile object pattern).runCounted previous

/-- Public focused CT1 stage for an induced-obstruction certificate target. -/
noncomputable def executeFocusedInducedObstruction
    {Previous : Type uPrevious} {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) (previous : Previous) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
      (focusedInducedObstructionEncoding profile object pattern) :=
  (executeFocusedInducedObstructionCounted profile object pattern previous).value

end CT1

end Hypostructure.Graph
