import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.ObstructionCT1

/-!
# CT1 encodings for induced-path obstructions

**Legacy.**  Split out of `Graph/InducedPath.lean` for the same reason as
`Graph/ObstructionCT1.lean`: the predicate `InducedPathFree` is what the entry
spine's external closure law is stated against, and it must not carry the
legacy stage stack with it.
-/

namespace Hypostructure.Graph

universe uPrevious uVertex

namespace CT1

/-- Focused proof-carrying CT1 encoding for induced paths in a graph read from
the active residual. -/
def focusedInducedPathEncoding {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Encoding profile
      (fun previous active =>
        HasInducedPath (object previous active) order) :=
  focusedInducedObstructionEncoding profile object (inducedPathObstruction order)

/-- Counted focused CT1 execution for an induced-path certificate target. -/
noncomputable def executeFocusedInducedPathCounted {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
        (focusedInducedPathEncoding profile object order)) :=
  (focusedInducedPathEncoding profile object order).runCounted previous

/-- Public focused CT1 stage for an induced-path certificate target. -/
noncomputable def executeFocusedInducedPath {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) (previous : Previous) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
      (focusedInducedPathEncoding profile object order) :=
  (executeFocusedInducedPathCounted profile object order previous).value

end CT1

end Hypostructure.Graph
