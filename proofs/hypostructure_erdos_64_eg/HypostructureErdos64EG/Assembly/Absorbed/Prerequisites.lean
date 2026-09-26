import Hypostructure.Graph.Strategy.ColdCorridorRows.DenseTerminal
import HypostructureErdos64EG.Assembly.NearCubic.ColdPass

/-!
# Assembly: Absorbed / Prerequisites

The node-`[153]` corridor and extraction facts which node `[175]` receives on
the absorbed-configuration residual `[174]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[174]`**: the absorbed configurations are the cold corridors whose
charge node `[153]`'s bounded arm discarded.  Their return corridors
(`lem:bridgeless`), states, terminality on the dense residual, first failures
and candidate family are published by the registered node-`[153]` owners on
this literal residual; `[175]` only queries them. -/
noncomputable def selectedAbsorbedGermPrerequisites
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .bridgeless) known]
    (fresh : List.Disjoint
      [K .coldReturnCorridors, K .coldCorridorState,
        K .denseColdCorridorsTerminal, K .coldFirstFailureOccurrence,
        K .coldFailureCycle, K .coldFailureDefect, K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldFailureRouting, K .coldExchangeBound, K .coldGermExtraction,
        K .coldGermCandidates] known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldGermCandidates :: K .coldExchangeBound :: K .coldGermExtraction ::
        K .coldFailureRouting :: K .coldHandoffTransfer :: K .coldFailureHandoff ::
        K .coldFailureCompression :: K .coldFailureDefect ::
        K .coldFailureDefectRoute :: K .coldFailureCycle ::
        K .coldFirstFailureOccurrence :: K .denseColdCorridorsTerminal ::
        K .coldCorridorState :: K .coldReturnCorridors :: known) :=
  let state := nearCubicColdCorridorState history
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state (by key_fresh)
  nearCubicColdCandidates terminal

end HypostructureErdos64EG
