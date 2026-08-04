import Hypostructure.Graph.MinimalCounterexampleConnected

/-!
# Fixture: connectivity from graph minimality

The fixture records the public, problem-independent theorem shape used by
minimum-degree graph applications.
-/

namespace Hypostructure.Fixtures.OfficialMinimalCounterexampleConnectedGraph

open Hypostructure

universe u v

theorem minimumDegreeBaseline_forces_connected
    {threshold : Nat}
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Target : Graph.FiniteObject.{u} → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (Graph.problem
        (fun object : Graph.FiniteObject.{u} =>
          threshold ≤ object.minDegree)
        BranchState)
      Target
      (Graph.lexicographicProgress
        (fun object : Graph.FiniteObject.{u} =>
          threshold ≤ object.minDegree)
        BranchState)}
    [Nonempty ctx.G.Vertex]
    (certificate : Graph.NoProperBaselineCertificate ctx)
    (currentMinimumDegree : threshold ≤ ctx.G.minDegree) :
    ctx.G.graph.Connected :=
  Graph.connected_of_noProperBaseline_of_minDegree
    certificate threshold (fun _ baseline => baseline) currentMinimumDegree

#print axioms minimumDegreeBaseline_forces_connected

end Hypostructure.Fixtures.OfficialMinimalCounterexampleConnectedGraph
