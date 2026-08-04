import Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortCapacity

namespace Hypostructure.Fixtures.OfficialCanonicalExcessPortCapacityGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features
open CanonicalExcessPortCapacity

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
    (family : SelectedSubfamily (profile := profile) (ctx := ctx))
    (center : ctx.G.Vertex) :
    family.centerMultiplicity center ≤
      ctx.G.degree center - profile.threshold :=
  center_multiplicity_le_degree_sub_threshold family center

#print axioms center_multiplicity_le_degree_sub_threshold

end Hypostructure.Fixtures.OfficialCanonicalExcessPortCapacityGraph
