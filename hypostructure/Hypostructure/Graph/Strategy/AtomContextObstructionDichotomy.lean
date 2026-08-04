import Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
import Hypostructure.Graph.Gluing

/-!
# Boundary-piece/outside-context obstruction registration

This module only translates Graph terminology into the inert registration
consumed by Core's sealed atom--context obstruction dichotomy.  It defines no
stage, query, ledger operation, route, executor, or closure.
-/

namespace Hypostructure.Graph.Strategy.BoundaryContextObstructionDichotomy

open Hypostructure

universe u v uResidual

/--
Residual-indexed graph mathematics for the generic Core dichotomy.

The boundary piece and outside context themselves are derived by
`Graph.boundaryAssembly` from `object residual` and `site residual`; callers
provide only their local presentations and the complementary obstruction law.
-/
structure Registration
    (Baseline : Graph.FiniteObject.{u} → Prop)
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (baselineInvariant : Graph.FiniteObject.IsomorphismInvariant Baseline)
    (Residual : Type uResidual) where
  object : Residual → Graph.FiniteObject.{u}
  site : (residual : Residual) →
    Graph.OwnedDecomposition (object residual)
  PieceObstruction :
    (residual : Residual) →
      Graph.BoundaryPiece (site residual).interface → Prop
  OutsideObstruction :
    (residual : Residual) →
      Graph.OutsideContext (site residual).interface → Prop
  pieceDecidable : (residual : Residual) →
    Decidable (PieceObstruction residual (site residual).piece)
  outsideOfPieceFailure : (residual : Residual) →
    Not (PieceObstruction residual (site residual).piece) →
      OutsideObstruction residual (site residual).outside

namespace Registration

/-- Forget only Graph names; Core owns classification and branch execution. -/
noncomputable def toCore
    {Baseline : Graph.FiniteObject.{u} → Prop}
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {baselineInvariant : Graph.FiniteObject.IsomorphismInvariant Baseline}
    {Residual : Type uResidual}
    (registration :
      Registration Baseline BranchState baselineInvariant Residual) :
    Core.Strategy.AtomContextObstructionDichotomy.Registration.{
      u + 1, v, u + 1, uResidual}
      (Graph.problem Baseline BranchState) Residual where
  presentation := fun residual =>
    { semantics :=
        Graph.isomorphismEquivalence
          Baseline BranchState baselineInvariant
      assembly :=
        Graph.boundaryAssembly
          Baseline BranchState baselineInvariant
      object := registration.object residual
      site := registration.site residual
      AtomLocal :=
        Graph.BoundaryPiece (registration.site residual).interface
      atomRepresented := (registration.site residual).piece
      ContextLocal :=
        Graph.OutsideContext (registration.site residual).interface
      contextRepresented := (registration.site residual).outside
      AtomObstruction := registration.PieceObstruction residual
      ContextObstruction := registration.OutsideObstruction residual
      atomDecidable := registration.pieceDecidable residual
      contextOfAtomFailure :=
        registration.outsideOfPieceFailure residual }

/-- Package the Graph specialization in the ordinary registered Strategy
family.  Only the residual-indexed graph mathematics and documentation cross
the domain boundary; Core still owns classification and both branch ledgers. -/
noncomputable def toStrategyData
    {Baseline : Graph.FiniteObject.{u} → Prop}
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {baselineInvariant : Graph.FiniteObject.IsomorphismInvariant Baseline}
    (registration :
      Registration Baseline BranchState baselineInvariant
        (Core.Strategy.ProblemInput
          (Graph.problem Baseline BranchState)))
    (metadata : Core.Documentation := {})
    (components : List Core.Documentation := [])
    (pieceMetadata : Core.Documentation := {})
    (outsideMetadata : Core.Documentation := {}) :
    Core.AtomContextObstructionDichotomyData.{
      u + 1, v, u + 1}
      (Graph.problem Baseline BranchState) where
  registration := registration.toCore
  metadata := metadata
  components := components
  atomMetadata := pieceMetadata
  contextMetadata := outsideMetadata

end Registration

end Hypostructure.Graph.Strategy.BoundaryContextObstructionDichotomy
