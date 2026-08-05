import Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence
import Hypostructure.Fixtures.GraphDeletionCriticality

namespace Hypostructure.Fixtures.S09S10DeletionFan

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence

def residual :
    Residual (minimumDegreeDeletionCriticalityProfile 1)
      GraphDeletionCriticality.context :=
  deriveResidual
    (GraphDeletionCriticality.certificateQuery
      GraphDeletionCriticality.stage)

/-- The threshold is inherited from the deletion profile.  Nothing in the
feature layer repeats it as fan configuration. -/
example :
    (minimumDegreeDeletionCriticalityProfile 1).threshold = 1 :=
  rfl

/-- K₂ has no centre above its graph-derived deletion threshold. -/
example : residual.centers = [] := by
  rw [residual, deriveResidual]
  native_decide

example : residual.incidences = [] := by
  rw [residual, deriveResidual]
  native_decide

/-- For every generated high centre, the residual proves the exact canonical
port partition and derives endpoint tightness from deletion criticality. -/
theorem exact_generated_row
    {Baseline : FiniteObject → Prop}
    {BranchState : FiniteObject → Type}
    {Target : FiniteObject → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (result : Residual profile ctx)
    (row : HighCenterRow profile ctx.G)
    {endpoint : ctx.G.Vertex} (endpoint_mem : endpoint ∈ row.ports) :
    row.base ++ row.excess = row.ports ∧
    row.excess.length = ctx.G.degree row.center - profile.threshold ∧
    ctx.G.degree endpoint = profile.threshold ∧
    (outsideIncidences ctx.G row.center endpoint).length + 1 =
      profile.threshold := by
  exact ⟨row.partition, row.excess_length,
    result.endpoint_tight row endpoint_mem,
    result.outside_cardinality row endpoint_mem⟩

#print axioms Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence.deriveResidual
#print axioms Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence.Residual.endpoint_tight
#print axioms Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence.Residual.centers_independent
#print axioms Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence.Residual.incidence_outside_cardinality
#print axioms exact_generated_row

end Hypostructure.Fixtures.S09S10DeletionFan
