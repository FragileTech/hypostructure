import Hypostructure.Graph.ColdCorridor

/-!
# Fixture: the corridor construction is inhabited

`def:cold-corridor-first-failure` builds the cold return corridor before it
states the cut-state, and the cut-state theorems are stated at a
`Graph.ColdCorridor.Presentation`.  This fixture checks that the two meet: a
`Corridor` built from the manuscript's own data produces a `Presentation`, so
`Q_cold`, the retention, and the pigeonhole are statements about the initial
segments of a real corridor and not about an empty interface.

Nothing here is a concrete graph.  The point being checked is structural: given
a component with at least two boundary stubs (`lem:bridgeless`), a selected
branch-excess half-edge, and the two outside feet joined inside the component,
every downstream object exists and every downstream theorem applies.
-/

namespace Hypostructure.Fixtures.ColdCorridorConstruction

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.ColdCorridor

universe u

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}

/-- **A corridor is built from exactly the manuscript's data.**  The three
inputs are `lem:bridgeless`'s two-stub conclusion, the selected branch-excess
half-edge `ε = hᵢ`, and the connection inside `K` that lets the
lexicographically first simple path be chosen. -/
example
    (twoStubs : 2 ≤ (boundaryStubs object windows component).length)
    (entry : Fin (boundaryStubs object windows component).length)
    (connected :
      (object.induce component).graph.Reachable
        (stubFoot object windows component entry)
        (stubFoot object windows component
          (successorIndex (Nat.lt_of_lt_of_le Nat.zero_lt_two twoStubs) entry))) :
    Corridor object windows component :=
  { twoStubs := twoStubs, entry := entry, connected := connected }

/-- **A corridor presents the declared data**, so the cut-state theorems have a
real subject.  The offsets and the clause readings are supplied by the packing
and by the owners of the clauses, as `def:declared-coordinate-signature`
requires. -/
noncomputable example (corridor : Corridor object windows component) (S : DeclaredSignature)
    (offsetOf : object.Vertex → Fin S.windowOrder)
    (support : (clause : S.Clause) → S.Generator clause →
      Finset object.Vertex)
    (value : corridor.Segment → (clause : S.Clause) → S.Generator clause →
      S.Value) :
    Presentation.{u} S object :=
  corridor.presentation S offsetOf support value

/-- **`Q_cold + 1` initial segments of a real corridor repeat a state.**  This
is the pigeonhole `lem:cold-corridor-first-failure` reaches the repeat subcase
of (F5) by, read at the corridor rather than at an abstract interface. -/
noncomputable example (corridor : Corridor object windows component) (S : DeclaredSignature)
    (offsetOf : object.Vertex → Fin S.windowOrder)
    (support : (clause : S.Clause) → S.Generator clause →
      Finset object.Vertex)
    (value : corridor.Segment → (clause : S.Clause) → S.Generator clause →
      S.Value)
    (segments : Fin (stateBound S + 1) → corridor.Segment) :
    ∃ left right, left ≠ right ∧
      (corridor.presentation S offsetOf support value).state
          (ULift.up (segments left)) =
        (corridor.presentation S offsetOf support value).state
          (ULift.up (segments right)) :=
  corridor.exists_repeated_state S offsetOf support value segments

/-- **"Each selected branch-excess half-edge has exactly one corridor."** -/
example (left right : Corridor object windows component)
    (same : left.entry = right.entry) : left = right :=
  Corridor.eq_of_entry_eq left right same

/-- **"Each boundary stub is the successor of at most one selected
half-edge."** -/
example (left right : Corridor object windows component)
    (same : left.successorStub = right.successorStub) : left = right :=
  Corridor.eq_of_successorStub_eq left right same

/-- **The boundary stubs are exactly the edges from `K` to the cold windows**,
with no repeats -- the manuscript's `h₁,…,h_m`. -/
example (stub : object.Vertex × object.Vertex) :
    stub ∈ boundaryStubs object windows component ↔
      (stub.1 ∈ component ∧ stub.2 ∈ windows ∧ object.graph.Adj stub.1 stub.2) :=
  mem_boundaryStubs_iff object windows component stub

example : (boundaryStubs object windows component).Nodup :=
  boundaryStubs_nodup object windows component

end Hypostructure.Fixtures.ColdCorridorConstruction
