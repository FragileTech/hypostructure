import Hypostructure.Fixtures.GraphBoundariedAtom
import Hypostructure.Graph.Coordinate
import Hypostructure.Core.Residual.Query

/-!
# Graph parity for local-child closure and context handoff

The graph analogue of a recentered PDE tail is an exact boundary
decomposition whose local piece is discharged before the outside context is
relabelled as the next local graph view.  This fixture uses the same Core
ledger queries and coordinate paths; it introduces no graph executor or
route.
-/

namespace Hypostructure.Fixtures.GraphLocalTailParity

open Hypostructure
open Hypostructure.Graph

namespace Source

open GraphBoundariedAtom

abbrev Site := OwnedDecomposition ambient

/-- The exact graph decomposition is one ordinary Core-ledger entry. -/
abbrev SplitStage :=
  Core.Residual.Ledger.Extension Unit fun _ => Site

noncomputable def splitStage : SplitStage :=
  Core.Residual.Ledger.extend () decomposition

def splitQuery :
    Core.Residual.Query SplitStage fun _ => Site :=
  Core.Residual.Query.latest

def localPieceQuery :
    Core.Residual.Query SplitStage fun previous =>
      BoundaryPiece (splitQuery previous).interface :=
  splitQuery.dependentMap fun _ site => site.piece

def outsideContextQuery :
    Core.Residual.Query SplitStage fun previous =>
      OutsideContext (splitQuery previous).interface :=
  splitQuery.dependentMap fun _ site => site.outside

/-- Exact gluing reconstruction stays attached to the original split. -/
noncomputable def reconstructionQuery :
    Core.Residual.Query SplitStage fun previous =>
      (glue (splitQuery previous).piece
        (splitQuery previous).outside).Isomorphic ambient :=
  splitQuery.dependentMap
    (Output := fun _ site =>
      (glue site.piece site.outside).Isomorphic ambient)
    fun _ site => ⟨site.reconstructionIso⟩

/--
The local-piece certificate is the immediately following Core entry.  The
outside context is not activated before this stage exists.
-/
abbrev LocalClosedStage :=
  Core.Residual.Ledger.Extension SplitStage fun previous =>
    (localPieceQuery previous).graph.Connected

noncomputable def localClosedStage : LocalClosedStage :=
  Core.Residual.Ledger.extend splitStage piece_connected

def localClosedQuery :
    Core.Residual.Query LocalClosedStage fun stage =>
      (localPieceQuery.preserve stage).graph.Connected :=
  Core.Residual.Query.latest

def outsideOnClosedQuery :
    Core.Residual.Query LocalClosedStage fun stage =>
      OutsideContext
        (splitQuery.preserve stage).interface :=
  outsideContextQuery.preserve

/--
The exact outside context and the exact local closure are read from the same
stage.  This is the graph counterpart of tail activation.
-/
def handoffInputs :
    Core.Residual.Query LocalClosedStage fun stage =>
      PProd
        (OutsideContext (splitQuery.preserve stage).interface)
        ((localPieceQuery.preserve stage).graph.Connected) :=
  outsideOnClosedQuery.and localClosedQuery

/--
Rerooting/relabeling is an existing graph primitive inside Core's path
language.  The target coordinate is the packed outside context itself.
-/
noncomputable def outsidePathQuery :
    Core.Residual.Query LocalClosedStage fun stage =>
      Core.CoordinatePath
        (Graph.coordinateSystem Baseline BranchState)
        (outsideOnClosedQuery stage).pack
        (outsideOnClosedQuery stage).pack :=
  handoffInputs.dependentMap fun _ _ =>
    Core.CoordinatePath.cons
      (CoordinatePrimitive.relabel SimpleGraph.Iso.refl)
      Core.CoordinatePath.nil

/-- Original gluing reconstruction is still queryable after local closure. -/
noncomputable def reconstructionOnClosedQuery :
    Core.Residual.Query LocalClosedStage fun stage =>
      (glue (splitQuery.preserve stage).piece
        (splitQuery.preserve stage).outside).Isomorphic ambient :=
  reconstructionQuery.preserve

example :
    outsideOnClosedQuery localClosedStage = outside :=
  rfl

example :
    (outsidePathQuery localClosedStage).run () = () :=
  rfl

example :
    (glue (splitQuery.preserve localClosedStage).piece
      (splitQuery.preserve localClosedStage).outside).Isomorphic
        ambient :=
  reconstructionOnClosedQuery localClosedStage

end Source

end Hypostructure.Fixtures.GraphLocalTailParity
