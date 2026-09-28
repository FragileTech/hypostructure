import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.Realized
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.Unrealized

/-! The near-cubic survivor dispatcher. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **Nodes `[21]` and `[158]`** on the sparse survivor of `[19]`: the finite
enumeration `[21]`, then `[158]`, the exact finite form of the realization
sentence of `lem:p13-window-package`/`prop:p13-density`.  The yes arm continues
at `[22]`; the no arm is the dense-packing residual `[159]`. -/
-- EG-NODE [158] joint window package realized in the labelled class?
noncomputable def selectedNearCubicSurvivorBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
          K .admissibleQuotientsLabelInjective, K .replacementExclusion,
          K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
          K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .tightEndpoint,
        K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .noProperBaseline, K .returnAvoidance,
          K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
          K .highDegreePairSum, K .minDegreeBaseline, K .bridgeless, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .packingOrderBound,
          K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let dominated := selectedNearCubicNode21 history
  match windowPackageRealizationDichotomy (data := spineData) dominated
      (by key_fresh) (by key_fresh) with
  | .right unrealizedHistory =>
      exact Assembly.Internal.nearCubicUnrealized unrealizedHistory
  | .left enumerated =>
      exact Assembly.Internal.nearCubicRealized enumerated

end HypostructureErdos64EG
