import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Cut parity

A closed walk crosses every vertex cut an even number of times, so a cycle that
meets both sides of a cut uses at least two distinct cut edges.

This is the graph content of `lem:typeA-carrier-cut-parity`: *"A cycle crosses
every cut an even number of times.  Because `C` is simple, it cannot use the
same cut edge twice.  Hence `C` uses at least two distinct boundary edges of
`X`."*  Nothing about response coordinates appears here; this file is about
walks and cuts only.
-/

namespace Hypostructure.Graph.CutParity

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

variable (S : Set V) [DecidablePred (· ∈ S)]

/-- Which side of the cut a vertex is on. -/
def side (vertex : V) : Bool := decide (vertex ∈ S)

/-- A dart crosses the cut of `S` when its endpoints are on opposite sides. -/
def crosses (dart : G.Dart) : Bool := side S dart.fst != side S dart.snd

/-- The number of cut crossings a walk makes, counted with multiplicity on the
walk's own dart list. -/
def crossings {u v : V} (walk : G.Walk u v) : Nat :=
  walk.darts.countP (crosses S)

@[simp] theorem crossings_nil {u : V} :
    crossings S (Walk.nil : G.Walk u u) = 0 := rfl

theorem crossings_cons {u v w : V} (adjacency : G.Adj u v) (walk : G.Walk v w) :
    crossings S (Walk.cons adjacency walk) =
      crossings S walk + (if side S u = side S v then 0 else 1) := by
  simp only [crossings, Walk.darts_cons, List.countP_cons, crosses]
  by_cases same : side S u = side S v <;> simp [same]

/-- **Cut parity.**  A walk's crossing count is even exactly when its two
endpoints lie on the same side of the cut. -/
theorem crossings_mod_two {u v : V} (walk : G.Walk u v) :
    crossings S walk % 2 = if side S u = side S v then 0 else 1 := by
  induction walk with
  | nil => simp
  | @cons a b c adjacency rest inductionHypothesis =>
      rw [crossings_cons, Nat.add_mod, inductionHypothesis]
      by_cases first : side S a = side S b
      · by_cases second : side S b = side S c
        · have third : side S a = side S c := first.trans second
          simp [first, second, third]
        · have third : ¬ side S a = side S c := fun same =>
            second (first ▸ same)
          simp [first, second, third]
      · by_cases second : side S b = side S c
        · have third : ¬ side S a = side S c := fun same =>
            first (same.trans second.symm)
          simp [first, second, third]
        · have third : side S a = side S c := by
            revert first second
            cases side S a <;> cases side S b <;> cases side S c <;> simp
          have flipped : ¬ side S c = side S b := fun same => second same.symm
          simp [first, second, third, flipped]

/-- A closed walk always crosses the cut an even number of times. -/
theorem crossings_closed_mod_two {u : V} (walk : G.Walk u u) :
    crossings S walk % 2 = 0 := by
  simpa using crossings_mod_two S walk

/-- A walk that never crosses the cut keeps every visited vertex on the side
its start is on. -/
theorem side_of_crossings_eq_zero {u v : V} (walk : G.Walk u v)
    (none : crossings S walk = 0) :
    ∀ vertex ∈ walk.support, side S vertex = side S u := by
  induction walk with
  | @nil start =>
      intro vertex member
      have single : vertex = start := by simpa using member
      rw [single]
  | @cons a b c adjacency rest inductionHypothesis =>
      rw [crossings_cons] at none
      have restNone : crossings S rest = 0 := by
        by_cases same : side S a = side S b <;> simp [same] at none <;> omega
      have same : side S a = side S b := by
        by_contra different
        simp [different] at none
      intro vertex member
      rcases List.mem_cons.mp (by simpa using member) with head | tail
      · rw [head]
      · rw [inductionHypothesis restNone vertex tail, same]

/-- A walk meeting both sides of the cut crosses it. -/
theorem crossings_pos {u v : V} (walk : G.Walk u v) {vertex : V}
    (member : vertex ∈ walk.support) (opposite : side S vertex ≠ side S u) :
    0 < crossings S walk := by
  rcases Nat.eq_zero_or_pos (crossings S walk) with none | positive
  · exact absurd (side_of_crossings_eq_zero S walk none vertex member) opposite
  · exact positive

/-- **`lem:typeA-carrier-cut-parity`, the counting half.**  A closed walk
meeting both sides of a cut crosses it at least twice. -/
theorem two_le_crossings {u : V} (walk : G.Walk u u)
    (positive : 0 < crossings S walk) : 2 ≤ crossings S walk := by
  have parity := crossings_closed_mod_two S walk
  omega

/-- The cut edges a walk uses, in walk order. -/
def crossingEdges {u v : V} (walk : G.Walk u v) : List (Sym2 V) :=
  (walk.darts.filter (crosses S)).map Dart.edge

theorem crossingEdges_nodup {u v : V} {walk : G.Walk u v}
    (trail : walk.IsTrail) : (crossingEdges S walk).Nodup :=
  trail.edges_nodup.sublist (List.Sublist.map _ List.filter_sublist)

theorem length_crossingEdges {u v : V} (walk : G.Walk u v) :
    (crossingEdges S walk).length = crossings S walk := by
  simp [crossingEdges, crossings, List.countP_eq_length_filter]

/-- **`lem:typeA-carrier-cut-parity`.**  A cycle that meets both sides of a cut
uses at least two *distinct* cut edges: parity gives two crossings, and a simple
cycle cannot use the same edge twice. -/
theorem two_le_card_crossingEdges {u : V} {walk : G.Walk u u}
    [DecidableEq (Sym2 V)]
    (cycle : walk.IsCycle) (positive : 0 < crossings S walk) :
    2 ≤ (crossingEdges S walk).toFinset.card := by
  rw [List.toFinset_card_of_nodup (crossingEdges_nodup S cycle.isTrail),
    length_crossingEdges]
  exact two_le_crossings S walk positive

end Hypostructure.Graph.CutParity
