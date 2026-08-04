import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Strategy.Official.Presentation

/-!
# Framework-owned semantics for official Graph operations

Every operation below is computed by Graph from a `FiniteObject` and inert
presentation rows.  There is no application-supplied program or branch
selector.
-/

namespace Hypostructure.Graph.Strategy.Official

open Hypostructure.Graph

universe u

namespace Presentation

variable (data : Presentation.{u})

/-- Semantic rooted-return query derived from the graph and accepted rows. -/
def RootedReturnResult : Prop :=
  ∃ dart : data.object.graph.Dart,
    ∃ length ∈ returnLengthSet data.object dart,
      data.target.ReturnLengthOK length

theorem rootedReturnResult_iff :
    data.RootedReturnResult ↔
      ∃ dart : data.object.graph.Dart,
        ∃ length ∈ returnLengthSet data.object dart,
          data.target.ReturnLengthOK length :=
  Iff.rfl

/-- Canonical one-edge decorated-fan rim schedule at a hub.  Longer
decorations are obtained by subsequent official rooted-return/path operations;
authors cannot nominate fan incidences. -/
def fanSchedule (hub : data.object.Vertex) : List data.object.Vertex :=
  let _ := data.object.decideAdj
  data.vertexSchedule.filter fun rim => decide (data.object.graph.Adj hub rim)

theorem fanSchedule_nodup (hub : data.object.Vertex) :
    (data.fanSchedule hub).Nodup :=
  List.Nodup.filter _ data.vertexSchedule_nodup

theorem mem_fanSchedule_iff (hub rim : data.object.Vertex) :
    rim ∈ data.fanSchedule hub ↔ data.object.graph.Adj hub rim := by
  letI := data.object.decideAdj
  simp [fanSchedule, vertexSchedule_complete]

theorem fanSchedule_length_le_vertexCount (hub : data.object.Vertex) :
    (data.fanSchedule hub).length ≤ data.object.vertexCount := by
  rw [data.object.vertexCount_eq_orderedVertices_length]
  exact List.length_filter_le _ _

/-- Framework-owned exact response table: adjacency of every ordered pair. -/
def adjacencyResponses :
    List ((data.object.Vertex × data.object.Vertex) × Bool) :=
  let _ := data.object.decideAdj
  data.vertexSchedule.flatMap fun left =>
    data.vertexSchedule.map fun right =>
      ((left, right), decide (data.object.graph.Adj left right))

/-- Framework-owned capacity table: graph degree at each scheduled vertex. -/
def degreeCapacities : List (data.object.Vertex × Nat) :=
  data.vertexSchedule.map fun vertex => (vertex, data.object.degree vertex)

/-- Framework-owned support relation: the literal oriented adjacency rows. -/
def adjacencySupport :
    List (data.object.Vertex × data.object.Vertex) :=
  let _ := data.object.decideAdj
  data.vertexSchedule.flatMap fun left =>
    (data.fanSchedule left).map fun right => (left, right)

/-- Framework-owned rank table.  The canonical finite-graph rank is degree;
rank-budget strategies may combine it with Core-owned numeric operations. -/
def degreeRanks : List (data.object.Vertex × Nat) :=
  data.degreeCapacities

end Presentation

end Hypostructure.Graph.Strategy.Official
