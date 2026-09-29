import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.ColdCorridorRuns

/-!
# Statements: the retained cold corridors of G as induced paths, and their runs in `R`

`[162]`'s residual is a retained cold corridor of G that reads more than `Q_cold`
states while its first failure is an (F4) heavy centre before its terminal segment.
The corridor is the shortest path of its component `K` of `G − X_cold`
(`Corridor.inside_length_le`), so it is an induced path of G, and any two of its
vertices in the remainder `R = G − W(P₀)` that are joined inside `R` are at most `11`
positions apart (`Graph/ColdCorridorRuns.lean`, with `WindowFreeGeometry` of the
canonical maximal packing).  The corridor can therefore be long only through the windows
of `P₀` it crosses.

Every statement is about G's retained corridors (the occurrence data of `[151]`) and G's
canonical packing; this module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The number of edges of G's retained cold corridor of `ε`. -/
noncomputable def coldCorridorLength (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) : Nat :=
  (coldOccurrenceCorridorAt data object occurrence epsilon).inside.1.length

/-- The vertex of G at position `i` of the retained cold corridor of `ε`. -/
noncomputable def coldCorridorVertex (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) (i : Nat) : object.Vertex :=
  ((coldOccurrenceCorridorAt data object occurrence epsilon).inside.1.getVert i).1

/-- **The cold corridors of G are induced paths whose runs in `R` are short.**  For
every retained corridor of G: two corridor vertices that are not consecutive are not
adjacent in G, and two corridor vertices joined by a walk inside the remainder
`R = G − W(P₀)` are at most `11` positions apart on the corridor. -/
def ColdCorridorInducedRunsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object),
    (∀ i j : Nat, i + 1 < j → j ≤ coldCorridorLength data object occurrence epsilon →
      ¬ object.graph.Adj (coldCorridorVertex data object occurrence epsilon i)
        (coldCorridorVertex data object occurrence epsilon j)) ∧
    (∀ i j : Nat, i ≤ j → j ≤ coldCorridorLength data object occurrence epsilon →
      (∃ k, Graph.WindowCombination.Reach object.graph
        {v | v ∉ (↑(Graph.FiniteObject.windowSupport
          (canonicalWindowPacking data object)) : Set object.Vertex)}
        (coldCorridorVertex data object occurrence epsilon i)
        (coldCorridorVertex data object occurrence epsilon j) k) →
      j - i ≤ 11)

end Hypostructure.Graph.Strategy.Spine
