import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Residual.Query

/-!
# Pointwise atom--context obstruction semantics

This file contains only the inert mathematical presentation at one exact
incoming residual.  The predecessor-indexed `Query` that owns this value is
part of the Strategy profile, not part of the presentation.  This file
contains no predecessor, route, selected branch, successor, ledger, executor,
or target closure.
-/

namespace Hypostructure.Core.Strategy.AtomContextObstructionDichotomy

open Hypostructure.Core

universe uAmbient uBranch uData uPrevious uResidual

/--
One pointwise atom--context presentation.

The exact atom and context are derived from `assembly` at this presentation's
`object` and `site`.  The value supplies only the two local representations,
decidability of the atom obstruction, and the mathematical implication from
failure of that obstruction to the context obstruction.
-/
structure Presentation (P : Core.Problem.{uAmbient, uBranch}) where
  semantics : Core.SemanticEquivalence P
  assembly : Core.AtomContextAssembly.{
    uAmbient, uBranch, uData, uData, uData, uData} P semantics
  object : P.Ambient
  site : assembly.Site object
  AtomLocal : Type uData
  atomRepresented : AtomLocal
  ContextLocal : Type uData
  contextRepresented : ContextLocal
  AtomObstruction : AtomLocal -> Prop
  ContextObstruction : ContextLocal -> Prop
  atomDecidable : Decidable (AtomObstruction atomRepresented)
  contextOfAtomFailure :
    Not (AtomObstruction atomRepresented) ->
      ContextObstruction contextRepresented

/-!
The reusable registration is indexed by the domain residual interpreted by
Graph or PDE.  It contains only the pointwise mathematical projection.  The
compiler supplies the query for the literal predecessor and owns every ledger
write and branch route.
-/

structure Registration
    (P : Core.Problem.{uAmbient, uBranch})
    (Residual : Type uResidual) where
  presentation : Residual → Presentation.{uAmbient, uBranch, uData} P

namespace Registration

/-- Map the exact residual query to the presentation query consumed by the
sealed Strategy. -/
def query
    {P : Core.Problem.{uAmbient, uBranch}}
    {Residual : Type uResidual}
    {Previous : Type uPrevious}
    (registration : Registration P Residual)
    (residual : Core.Residual.Query Previous (fun _ => Residual)) :
    Core.Residual.Query Previous (fun _ =>
      Presentation.{uAmbient, uBranch, uData} P) :=
  residual.map fun _ value => registration.presentation value

@[simp] theorem query_read
    {P : Core.Problem.{uAmbient, uBranch}}
    {Residual : Type uResidual}
    {Previous : Type uPrevious}
    (registration : Registration P Residual)
    (residual : Core.Residual.Query Previous (fun _ => Residual))
    (previous : Previous) :
    (registration.query residual) previous =
      registration.presentation (residual previous) :=
  rfl

end Registration

end Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
