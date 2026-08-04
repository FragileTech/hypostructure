import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Core.Strategy.Official.Availability
import Hypostructure.Graph.Finite
import Hypostructure.Graph.Strategy.Official.Target

/-!
# Inert presentation data for official graph strategies

The structures in this file contain only a finite graph and finite rows.
They contain no executable function, classifier, continuation, closure, or
target proof.  Graph-owned kernels interpret the rows against the literal
`FiniteObject`.
-/

namespace Hypostructure.Graph.Strategy.Official

universe u

/-- Finite mathematical data visible to the closed Graph registry.

The unique target interface is carried beside the object.  Every Graph
strategy derives shifted return acceptance from this same interface, so an
application cannot provide a second, inconsistent return-length table. -/
structure Presentation where
  object : Graph.FiniteObject.{u}
  target : CycleTargetInterface

namespace Presentation

variable (data : Presentation)

/-- The only vertex schedule used by official Graph execution. -/
def vertexSchedule : List data.object.Vertex :=
  data.object.orderedVertices

theorem vertexSchedule_complete (vertex : data.object.Vertex) :
    vertex ∈ data.vertexSchedule :=
  data.object.mem_orderedVertices vertex

theorem vertexSchedule_nodup : data.vertexSchedule.Nodup :=
  data.object.orderedVertices_nodup

end Presentation

end Hypostructure.Graph.Strategy.Official
