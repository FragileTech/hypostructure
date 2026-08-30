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

/-- Orient a simple cycle so that a selected edge is its first dart. -/
theorem exists_oriented_cycle_of_edge [DecidableEq V]
    {left right start : V} (different : left ≠ right)
    (cycle : G.Walk start start) (isCycle : cycle.IsCycle)
    (uses : s(left, right) ∈ cycle.edges) :
    ∃ oriented : G.Walk left left,
      oriented.IsCycle ∧ oriented.length = cycle.length ∧
        oriented.snd = right := by
  have leftMember : left ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges uses
  let forward := cycle.rotate left leftMember
  have forwardCycle : forward.IsCycle := isCycle.rotate leftMember
  have forwardUses : s(left, right) ∈ forward.edges :=
    (cycle.rotate_edges left leftMember).mem_iff.mpr uses
  have forwardLength : forward.length = cycle.length :=
    cycle.length_rotate left leftMember
  by_cases firstIsRight : forward.snd = right
  · exact ⟨forward, forwardCycle, forwardLength, firstIsRight⟩
  · have forwardNotNil : ¬ forward.Nil := forwardCycle.not_nil
    have rebuilt : (Walk.cons (forward.adj_snd forwardNotNil)
        forward.tail).IsCycle := by
      rw [forward.cons_tail_eq forwardNotNil]
      exact forwardCycle
    have tailData : forward.tail.IsPath ∧
        s(left, forward.snd) ∉ forward.tail.edges :=
      (Walk.cons_isCycle_iff forward.tail
        (forward.adj_snd forwardNotNil)).mp rebuilt
    have tailNotNil : ¬ forward.tail.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      have cycleLength := forwardCycle.three_le_length
      have exactDrop := forward.length_tail_add_one forwardNotNil
      omega
    have tailUses : s(left, right) ∈ forward.tail.edges := by
      have split := forwardUses
      rw [← forward.cons_tail_eq forwardNotNil,
        Walk.edges_cons, List.mem_cons] at split
      rcases split with first | later
      · have rightIsSnd : right = forward.snd := by
          rw [Sym2.eq_iff] at first
          rcases first with same | reversed
          · exact same.2
          · exact (different reversed.2.symm).elim
        exact (firstIsRight rightIsSnd.symm).elim
      · exact later
    have rightIsPenultimate : right = forward.tail.penultimate :=
      tailData.1.eq_penultimate_of_mem_edges tailUses
    have forwardPenultimate : forward.penultimate =
        forward.tail.penultimate := by
      calc
        forward.penultimate =
            (Walk.cons (forward.adj_snd forwardNotNil)
              forward.tail).penultimate := by
                rw [forward.cons_tail_eq forwardNotNil]
        _ = forward.tail.penultimate :=
          Walk.penultimate_cons_of_not_nil
            (forward.adj_snd forwardNotNil) forward.tail tailNotNil
    have reverseSnd : forward.reverse.snd = right := by
      rw [Walk.snd_reverse, forwardPenultimate]
      exact rightIsPenultimate.symm
    exact ⟨forward.reverse, forwardCycle.reverse,
      by simpa only [Walk.length_reverse] using forwardLength,
      reverseSnd⟩

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

@[simp] theorem crossings_copy {u v u' v' : V} (walk : G.Walk u v)
    (start : u = u') (finish : v = v') :
    crossings S (walk.copy start finish) = crossings S walk := by
  simp [crossings]

theorem crossings_append {u v w : V} (first : G.Walk u v)
    (second : G.Walk v w) :
    crossings S (first.append second) =
      crossings S first + crossings S second := by
  simp [crossings, Walk.darts_append, List.countP_append]

theorem crossings_reverse {u v : V} (walk : G.Walk u v) :
    crossings S walk.reverse = crossings S walk := by
  induction walk with
  | nil => rfl
  | @cons u v w adjacent rest ih =>
      have ih' : List.countP (crosses S) rest.reverse.darts =
          List.countP (crosses S) rest.darts := by
        simpa [crossings] using ih
      have crossesSymm : (crosses (G := G) S) ∘ Dart.symm = crosses S := by
        funext dart
        simp [crosses, Bool.xor_comm]
      rw [crossings_cons]
      simp [crossings, Walk.darts_append, ih', crossesSymm, crosses, side,
        Bool.xor_comm, Nat.add_comm]

@[simp] theorem crossings_rotate [DecidableEq V] {u v : V} (cycle : G.Walk u u)
    (member : v ∈ cycle.support) :
    crossings S (cycle.rotate v member) = crossings S cycle := by
  unfold crossings
  exact (cycle.rotate_darts v member).perm.countP_eq (crosses S)

/-- Orient a selected cycle edge while preserving its exact cut-crossing
count. -/
theorem exists_oriented_cycle_of_edge_with_crossings [DecidableEq V]
    {left right start : V} (different : left ≠ right)
    (cycle : G.Walk start start) (isCycle : cycle.IsCycle)
    (uses : s(left, right) ∈ cycle.edges) :
    ∃ oriented : G.Walk left left,
      oriented.IsCycle ∧ oriented.length = cycle.length ∧
        oriented.snd = right ∧ crossings S oriented = crossings S cycle := by
  have leftMember : left ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges uses
  let forward := cycle.rotate left leftMember
  have forwardCycle : forward.IsCycle := isCycle.rotate leftMember
  have forwardUses : s(left, right) ∈ forward.edges :=
    (cycle.rotate_edges left leftMember).mem_iff.mpr uses
  have forwardLength : forward.length = cycle.length :=
    cycle.length_rotate left leftMember
  have forwardCrossings : crossings S forward = crossings S cycle :=
    crossings_rotate S cycle leftMember
  by_cases firstIsRight : forward.snd = right
  · exact ⟨forward, forwardCycle, forwardLength, firstIsRight, forwardCrossings⟩
  · have forwardNotNil : ¬ forward.Nil := forwardCycle.not_nil
    have rebuilt : (Walk.cons (forward.adj_snd forwardNotNil)
        forward.tail).IsCycle := by
      rw [forward.cons_tail_eq forwardNotNil]
      exact forwardCycle
    have tailData : forward.tail.IsPath ∧
        s(left, forward.snd) ∉ forward.tail.edges :=
      (Walk.cons_isCycle_iff forward.tail
        (forward.adj_snd forwardNotNil)).mp rebuilt
    have tailNotNil : ¬ forward.tail.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      have cycleLength := forwardCycle.three_le_length
      have exactDrop := forward.length_tail_add_one forwardNotNil
      omega
    have tailUses : s(left, right) ∈ forward.tail.edges := by
      have split := forwardUses
      rw [← forward.cons_tail_eq forwardNotNil,
        Walk.edges_cons, List.mem_cons] at split
      rcases split with first | later
      · have rightIsSnd : right = forward.snd := by
          rw [Sym2.eq_iff] at first
          rcases first with same | reversed
          · exact same.2
          · exact (different reversed.2.symm).elim
        exact (firstIsRight rightIsSnd.symm).elim
      · exact later
    have rightIsPenultimate : right = forward.tail.penultimate :=
      tailData.1.eq_penultimate_of_mem_edges tailUses
    have forwardPenultimate : forward.penultimate =
        forward.tail.penultimate := by
      calc
        forward.penultimate =
            (Walk.cons (forward.adj_snd forwardNotNil)
              forward.tail).penultimate := by
                rw [forward.cons_tail_eq forwardNotNil]
        _ = forward.tail.penultimate :=
          Walk.penultimate_cons_of_not_nil
            (forward.adj_snd forwardNotNil) forward.tail tailNotNil
    have reverseSnd : forward.reverse.snd = right := by
      rw [Walk.snd_reverse, forwardPenultimate]
      exact rightIsPenultimate.symm
    exact ⟨forward.reverse, forwardCycle.reverse,
      by simpa only [Walk.length_reverse] using forwardLength,
      reverseSnd, (crossings_reverse S forward).trans forwardCrossings⟩

theorem crossings_tail_add_first {u v : V} (walk : G.Walk u v)
    (notNil : ¬ walk.Nil) :
    crossings S walk.tail +
      (if side S u = side S walk.snd then 0 else 1) = crossings S walk := by
  have identity := crossings_cons S (walk.adj_snd notNil) walk.tail
  rw [walk.cons_tail_eq notNil] at identity
  exact identity.symm

theorem crossings_dropLast_add_last {u v : V} (walk : G.Walk u v)
    (notNil : ¬ walk.Nil) :
    crossings S walk.dropLast +
      (if side S walk.penultimate = side S v then 0 else 1) =
        crossings S walk := by
  induction walk with
  | nil => exact (notNil .nil).elim
  | @cons u next v adjacent rest ih =>
      cases rest with
      | nil => simp [crossings, crosses, side]
      | @cons next finish v adjacent' remaining =>
          have restNotNil : ¬ (Walk.cons adjacent' remaining).Nil := by simp
          rw [Walk.dropLast_cons_of_not_nil adjacent
            (Walk.cons adjacent' remaining) restNotNil]
          simp only [crossings_cons, crossings_copy,
            Walk.penultimate_cons_of_not_nil adjacent
              (Walk.cons adjacent' remaining) restNotNil]
          have restIdentity := ih restNotNil
          have restCross := crossings_cons S adjacent' remaining
          omega

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
