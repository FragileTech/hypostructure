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
(`lem:bridgeless`), states, first failures and candidate family are published
by the registered node-`[153]` owners on this literal residual; `[175]` only
queries them.  Node `[153]`'s exact (★) decision is taken here as on the
spine: its ¬(★) arm returns the explicitly constructed residual
`K .coldRepeatedStateResidual`.  Node `[162]`'s terminality is not run here:
the paper states it only on the dense-packing residual
(`lem:dense-cold-pass`), and node `[176]` does not use it
(`lem:absorbed-germ-fan-data` (i)). -/
noncomputable def selectedAbsorbedGermPrerequisites
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (fresh : List.Disjoint
      [K .coldReturnCorridors, K .coldCorridorState,
        K .coldFirstFailureOccurrence, K .coldCutStatesDistinct,
        K .coldRepeatedStateResidual,
        K .coldFailureCycle, K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldHandoffTransfer,
        K .coldFailureRouting, K .coldExchangeBound,
        K .coldGermCandidates] known := by key_fresh) :
    PSum
      (ExactLedger EGInput.{u} selected
        (K .coldGermCandidates :: K .coldExchangeBound ::
          K .coldFailureRouting :: K .coldHandoffTransfer ::
          K .coldFailureCompression ::
          K .coldFailureDefectRoute :: K .coldFailureCycle ::
          K .coldCutStatesDistinct :: K .coldFirstFailureOccurrence ::
          K .coldCorridorState :: K .coldReturnCorridors :: known))
      (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .coldRepeatedStateResidual
          selected.object) :=
  let state := nearCubicColdCorridorState history
  match nearCubicColdOccurrence state with
  | .inl distinct => .inl (nearCubicColdCandidates distinct)
  | .inr repeated => .inr repeated

end HypostructureErdos64EG
