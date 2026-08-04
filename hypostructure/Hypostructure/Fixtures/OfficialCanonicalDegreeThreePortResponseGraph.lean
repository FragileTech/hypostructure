import Hypostructure.Graph.Strategy.Official.Features.CanonicalDegreeThreePortResponse

namespace Hypostructure.Fixtures.OfficialCanonicalDegreeThreePortResponseGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features
open CanonicalDegreeThreePortResponse

universe u v

variable
    {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}

example
    {criticality : DeletionCriticalityCertificate profile ctx}
    {threshold_eq_three : profile.threshold = 3}
    {baselineFromThreshold : BaselineFromThreshold profile}
    (family : CompletedFamily criticality threshold_eq_three
      baselineFromThreshold) :
    family.rows.length =
      (DegreeSurplusLedger.derive ctx.G
        (ExcessPortExtraction.surplusBaseline
          (profile := profile) ctx)).total :=
  family.rows_length

noncomputable example
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3)
    (baselineFromThreshold : BaselineFromThreshold profile) :
    CompletedFamily criticality threshold_eq_three baselineFromThreshold :=
  completedFamily criticality threshold_eq_three baselineFromThreshold

noncomputable example
    {port : Port (profile := profile) (ctx := ctx)}
    (response : LocalResponse port)
    (baselineFromThreshold : BaselineFromThreshold profile) :
    CompletedLocalResponse port :=
  completeResponse baselineFromThreshold response

#print axioms CanonicalPath.selectOfPath
#print axioms deriveShoulders
#print axioms suppressionConfiguration
#print axioms canonicalReturn
#print axioms triangleWalk_isCycle
#print axioms OpenSuppressionRequest.complete
#print axioms completeResponse
#print axioms CompletedFamily.rows_length
#print axioms CompletedFamily.port_mem_extracted

end Hypostructure.Fixtures.OfficialCanonicalDegreeThreePortResponseGraph
